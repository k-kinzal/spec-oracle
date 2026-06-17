#!/usr/bin/env python3
"""External validation on real OSS artifacts for UAD/f interval consistency.

Design goals:
- Fully automatic extraction (no manual post-editing)
- Reproducible source lock with URL + SHA256 + retrieval timestamp
- Layered consistency check using interval intersection
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import urllib.request
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Literal, Optional

FailurePolicy = Literal["fail-fast", "none"]
NoneSemantics = Literal["must", "may"]
Judgement = Literal["consistent", "contradictory", "inconclusive"]
LayerStatus = Literal["supported", "invalid", "unknown"]


@dataclass(frozen=True)
class LayerBounds:
    lower: Optional[int]
    upper: Optional[int]
    source: str
    note: str


@dataclass(frozen=True)
class ProjectArtifacts:
    name: str
    requirement: LayerBounds
    api: LayerBounds
    code: LayerBounds


@dataclass(frozen=True)
class SourceRecord:
    url: str
    sha256: str
    retrieved_at_utc: str
    snapshot_file: str


def slugify(url: str) -> str:
    cleaned = re.sub(r"^https?://", "", url)
    cleaned = re.sub(r"[^a-zA-Z0-9._-]+", "_", cleaned)
    return cleaned.strip("_")[:180]


def fetch_text(
    url: str,
    snapshots_dir: Path,
    source_records: dict[str, SourceRecord],
    offline_records: Optional[dict[str, SourceRecord]] = None,
) -> str:
    if offline_records is not None:
        record = offline_records.get(url)
        if record is None:
            raise ValueError(f"url not found in offline lock: {url}")
        snapshot_path = snapshots_dir.parent / record.snapshot_file
        if not snapshot_path.exists():
            raise FileNotFoundError(f"snapshot not found for offline replay: {snapshot_path}")
        raw = snapshot_path.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        if sha != record.sha256:
            raise ValueError(
                "snapshot SHA256 mismatch for offline replay: "
                f"url={url}, expected={record.sha256}, actual={sha}"
            )
        source_records[url] = record
        return raw.decode("utf-8", errors="replace")

    req = urllib.request.Request(url, headers={"User-Agent": "spec-oracle/1.0"})
    with urllib.request.urlopen(req, timeout=30) as res:
        raw = res.read()

    sha = hashlib.sha256(raw).hexdigest()
    ts = datetime.now(timezone.utc).isoformat()

    snapshots_dir.mkdir(parents=True, exist_ok=True)
    snapshot_name = f"{slugify(url)}.txt"
    snapshot_path = snapshots_dir / snapshot_name
    snapshot_path.write_bytes(raw)

    source_records[url] = SourceRecord(
        url=url,
        sha256=sha,
        retrieved_at_utc=ts,
        snapshot_file=str(snapshot_path.relative_to(snapshots_dir.parent)),
    )
    return raw.decode("utf-8", errors="replace")


def load_offline_records(lock_path: Path) -> dict[str, SourceRecord]:
    payload = json.loads(lock_path.read_text(encoding="utf-8"))
    items = payload.get("source_lock", [])
    records: dict[str, SourceRecord] = {}
    for item in items:
        record = SourceRecord(
            url=item["url"],
            sha256=item["sha256"],
            retrieved_at_utc=item["retrieved_at_utc"],
            snapshot_file=item["snapshot_file"],
        )
        records[record.url] = record
    return records


def html_to_text(raw: str) -> str:
    text = re.sub(r"<script.*?</script>", " ", raw, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r"<style.*?</style>", " ", text, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text)
    return text


def record_issue(
    issues: list[dict],
    *,
    project: str,
    layer: str,
    field: str,
    reason: str,
    pattern: str,
) -> None:
    issues.append(
        {
            "project": project,
            "layer": layer,
            "field": field,
            "reason": reason,
            "pattern": pattern,
        }
    )


def parse_first_int(
    pattern: str,
    text: str,
    label: str,
    *,
    project: str,
    layer: str,
    field: str,
    failure_policy: FailurePolicy,
    issues: list[dict],
) -> tuple[Optional[int], Optional[str]]:
    m = re.search(pattern, text, flags=re.IGNORECASE)
    if not m:
        record_issue(
            issues,
            project=project,
            layer=layer,
            field=field,
            reason="regex_no_match",
            pattern=pattern,
        )
        if failure_policy == "fail-fast":
            raise ValueError(f"failed to parse {label} with pattern: {pattern}")
        return None, None
    return int(m.group(1)), m.group(0)


def require_phrase(
    phrase: str,
    text: str,
    label: str,
    *,
    project: str,
    layer: str,
    field: str,
    failure_policy: FailurePolicy,
    issues: list[dict],
) -> bool:
    if phrase in text:
        return True
    record_issue(
        issues,
        project=project,
        layer=layer,
        field=field,
        reason="phrase_not_found",
        pattern=phrase,
    )
    if failure_policy == "fail-fast":
        raise ValueError(f"failed to locate {label}")
    return False


def classify_uand(
    *layers: LayerBounds,
    undefined_from_parse: bool = False,
) -> tuple[Judgement, Optional[int], Optional[int], str]:
    if undefined_from_parse:
        return "inconclusive", None, None, "parse_issue"

    lowers = [x.lower for x in layers if x.lower is not None]
    uppers = [x.upper for x in layers if x.upper is not None]
    if not lowers or not uppers:
        return "inconclusive", None, None, "insufficient_bounds"

    lower = max(lowers)
    upper = min(uppers)
    if lower <= upper:
        return "consistent", lower, upper, "interval_intersection"
    return "contradictory", lower, upper, "interval_intersection"


def apply_none_policy(judgement: Judgement, none_semantics: NoneSemantics) -> Judgement:
    if judgement != "inconclusive":
        return judgement
    # inconclusive + must -> contradictory, inconclusive + may -> consistent
    return "contradictory" if none_semantics == "must" else "consistent"


def classify_layer_status(
    layer: LayerBounds,
    *,
    layer_has_parse_issue: bool,
    ) -> LayerStatus:
    if layer_has_parse_issue:
        return "unknown"
    # PoC policy: treat one-sided/incomplete bounds as unknown evidence.
    # "supported" / "invalid" are assigned only when both bounds are present.
    if layer.lower is None or layer.upper is None:
        return "unknown"
    return "supported" if layer.lower <= layer.upper else "invalid"


def status_to_membership(status: LayerStatus, none_semantics: NoneSemantics) -> bool:
    if none_semantics == "must":
        return status == "supported"
    return status != "invalid"


def compute_layer_status(
    requirement: LayerBounds,
    api: LayerBounds,
    code: LayerBounds,
    *,
    layer_issue_flags: dict[str, bool],
) -> dict[str, LayerStatus]:
    return {
        "requirement": classify_layer_status(
            requirement,
            layer_has_parse_issue=layer_issue_flags["requirement"],
        ),
        "api": classify_layer_status(
            api,
            layer_has_parse_issue=layer_issue_flags["api"],
        ),
        "code": classify_layer_status(
            code,
            layer_has_parse_issue=layer_issue_flags["code"],
        ),
    }


def status_count(layer_status: dict[str, LayerStatus], status: LayerStatus) -> int:
    return sum(1 for value in layer_status.values() if value == status)


def status_ratio(layer_status: dict[str, LayerStatus], status: LayerStatus) -> float:
    total = len(layer_status)
    return float(status_count(layer_status, status)) / float(total) if total > 0 else 0.0


def layers_with_status(layer_status: dict[str, LayerStatus], status: LayerStatus) -> list[str]:
    return [name for name, value in layer_status.items() if value == status]


def postgres_artifacts(
    source_records: dict[str, SourceRecord],
    snapshots_dir: Path,
    offline_records: Optional[dict[str, SourceRecord]],
    failure_policy: FailurePolicy,
    issues: list[dict],
) -> tuple[ProjectArtifacts, list[dict]]:
    name = "PostgreSQL identifier length"
    req_url = "https://www.postgresql.org/docs/current/runtime-config-preset.html"
    api_url = "https://www.postgresql.org/docs/current/sql-syntax-lexical.html"
    code_url = "https://raw.githubusercontent.com/postgres/postgres/master/src/include/pg_config_manual.h"

    req_txt = html_to_text(fetch_text(req_url, snapshots_dir, source_records, offline_records))
    api_txt = html_to_text(fetch_text(api_url, snapshots_dir, source_records, offline_records))
    code_txt = fetch_text(code_url, snapshots_dir, source_records, offline_records)

    req_max, req_hit = parse_first_int(
        r"max_identifier_length\s+is\s+([0-9]+)\s+bytes",
        req_txt,
        "postgres requirement max",
        project=name,
        layer="requirement",
        field="upper",
        failure_policy=failure_policy,
        issues=issues,
    )
    api_max, api_hit = parse_first_int(
        r"maximum identifier length is\s+([0-9]+)\s+bytes",
        api_txt,
        "postgres api max",
        project=name,
        layer="api",
        field="upper",
        failure_policy=failure_policy,
        issues=issues,
    )
    namedatalen, code_hit = parse_first_int(
        r"#define\s+NAMEDATALEN\s+([0-9]+)",
        code_txt,
        "postgres NAMEDATALEN",
        project=name,
        layer="code",
        field="namedatalen",
        failure_policy=failure_policy,
        issues=issues,
    )

    patterns = [
        {"field": "requirement.upper", "pattern": r"max_identifier_length\\s+is\\s+([0-9]+)\\s+bytes", "match": req_hit},
        {"field": "api.upper", "pattern": r"maximum identifier length is\\s+([0-9]+)\\s+bytes", "match": api_hit},
        {"field": "code.namedatalen", "pattern": r"#define\\s+NAMEDATALEN\\s+([0-9]+)", "match": code_hit},
    ]

    return (
        ProjectArtifacts(
            name=name,
            requirement=LayerBounds(
                lower=1 if req_max is not None else None,
                upper=req_max,
                source=req_url,
                note="max_identifier_length documented default.",
            ),
            api=LayerBounds(
                lower=1 if api_max is not None else None,
                upper=api_max,
                source=api_url,
                note="SQL lexical maximum identifier length.",
            ),
            code=LayerBounds(
                lower=None,
                upper=(namedatalen - 1) if namedatalen is not None else None,
                source=code_url,
                note="NAMEDATALEN-1 from source constant.",
            ),
        ),
        patterns,
    )


def zlib_artifacts(
    source_records: dict[str, SourceRecord],
    snapshots_dir: Path,
    offline_records: Optional[dict[str, SourceRecord]],
    failure_policy: FailurePolicy,
    issues: list[dict],
) -> tuple[ProjectArtifacts, list[dict]]:
    name = "zlib compression level"
    req_url = "https://www.zlib.net/manual.html"
    api_url = "https://docs.python.org/3/library/zlib.html"
    code_url = "https://raw.githubusercontent.com/madler/zlib/master/zlib.h"

    req_txt = html_to_text(fetch_text(req_url, snapshots_dir, source_records, offline_records))
    api_txt = html_to_text(fetch_text(api_url, snapshots_dir, source_records, offline_records))
    code_txt = fetch_text(code_url, snapshots_dir, source_records, offline_records)

    req_phrase = "between 0 and 9"
    api_phrase = "integer from 0 to 9 or -1"
    req_found = require_phrase(
        req_phrase,
        req_txt,
        "zlib requirement interval",
        project=name,
        layer="requirement",
        field="interval",
        failure_policy=failure_policy,
        issues=issues,
    )
    api_found = require_phrase(
        api_phrase,
        api_txt,
        "python-zlib api interval",
        project=name,
        layer="api",
        field="interval",
        failure_policy=failure_policy,
        issues=issues,
    )

    z_no, no_hit = parse_first_int(
        r"#define\s+Z_NO_COMPRESSION\s+(-?[0-9]+)",
        code_txt,
        "zlib Z_NO_COMPRESSION",
        project=name,
        layer="code",
        field="z_no",
        failure_policy=failure_policy,
        issues=issues,
    )
    z_best, best_hit = parse_first_int(
        r"#define\s+Z_BEST_COMPRESSION\s+(-?[0-9]+)",
        code_txt,
        "zlib Z_BEST_COMPRESSION",
        project=name,
        layer="code",
        field="z_best",
        failure_policy=failure_policy,
        issues=issues,
    )
    z_default, def_hit = parse_first_int(
        r"#define\s+Z_DEFAULT_COMPRESSION\s+\((-?[0-9]+)\)",
        code_txt,
        "zlib Z_DEFAULT_COMPRESSION",
        project=name,
        layer="code",
        field="z_default",
        failure_policy=failure_policy,
        issues=issues,
    )

    patterns = [
        {"field": "requirement.interval", "pattern": req_phrase, "match": req_phrase if req_found else None},
        {"field": "api.interval", "pattern": api_phrase, "match": api_phrase if api_found else None},
        {"field": "code.z_no", "pattern": r"#define\\s+Z_NO_COMPRESSION\\s+(-?[0-9]+)", "match": no_hit},
        {"field": "code.z_best", "pattern": r"#define\\s+Z_BEST_COMPRESSION\\s+(-?[0-9]+)", "match": best_hit},
        {"field": "code.z_default", "pattern": r"#define\\s+Z_DEFAULT_COMPRESSION\\s+\\((-?[0-9]+)\\)", "match": def_hit},
    ]

    z_candidates = [x for x in [z_no, z_default] if x is not None]
    req_lower: Optional[int]
    if req_found and z_default is not None:
        req_lower = min(0, z_default)
    elif req_found:
        req_lower = 0
    else:
        req_lower = None

    return (
        ProjectArtifacts(
            name=name,
            requirement=LayerBounds(
                lower=req_lower,
                upper=9 if req_found else None,
                source=req_url,
                note="manual: Z_DEFAULT_COMPRESSION or [0,9].",
            ),
            api=LayerBounds(
                lower=-1 if api_found else None,
                upper=9 if api_found else None,
                source=api_url,
                note="python zlib API interval.",
            ),
            code=LayerBounds(
                lower=min(z_candidates) if z_candidates else None,
                upper=z_best,
                source=code_url,
                note="zlib.h constants.",
            ),
        ),
        patterns,
    )


def sqlite_artifacts(
    source_records: dict[str, SourceRecord],
    snapshots_dir: Path,
    offline_records: Optional[dict[str, SourceRecord]],
    failure_policy: FailurePolicy,
    issues: list[dict],
) -> tuple[ProjectArtifacts, list[dict]]:
    name = "SQLite page size"
    req_url = "https://www.sqlite.org/pragma.html#pragma_page_size"
    api_url = "https://www.sqlite.org/fileformat.html"
    code_url = "https://www.sqlite.org/src/doc/tip/src/sqliteLimit.h"

    req_txt = html_to_text(fetch_text(req_url, snapshots_dir, source_records, offline_records))
    api_txt = html_to_text(fetch_text(api_url, snapshots_dir, source_records, offline_records))
    code_txt = html_to_text(fetch_text(code_url, snapshots_dir, source_records, offline_records))

    req_min, req_min_hit = parse_first_int(
        r"between ([0-9]+) and 65536 inclusive",
        req_txt,
        "sqlite requirement min",
        project=name,
        layer="requirement",
        field="min",
        failure_policy=failure_policy,
        issues=issues,
    )
    req_max, req_max_hit = parse_first_int(
        r"between [0-9]+ and ([0-9]+) inclusive",
        req_txt,
        "sqlite requirement max",
        project=name,
        layer="requirement",
        field="max",
        failure_policy=failure_policy,
        issues=issues,
    )
    api_min, api_min_hit = parse_first_int(
        r"between ([0-9]+) and 65536 inclusive",
        api_txt,
        "sqlite api min",
        project=name,
        layer="api",
        field="min",
        failure_policy=failure_policy,
        issues=issues,
    )
    api_max, api_max_hit = parse_first_int(
        r"between [0-9]+ and ([0-9]+) inclusive",
        api_txt,
        "sqlite api max",
        project=name,
        layer="api",
        field="max",
        failure_policy=failure_policy,
        issues=issues,
    )
    code_max, code_max_hit = parse_first_int(
        r"SQLITE_MAX_PAGE_SIZE ([0-9]+)",
        code_txt,
        "sqlite code max",
        project=name,
        layer="code",
        field="max",
        failure_policy=failure_policy,
        issues=issues,
    )
    code_default, code_def_hit = parse_first_int(
        r"SQLITE_DEFAULT_PAGE_SIZE ([0-9]+)",
        code_txt,
        "sqlite default page size",
        project=name,
        layer="code",
        field="default",
        failure_policy=failure_policy,
        issues=issues,
    )

    patterns = [
        {"field": "requirement.min", "pattern": r"between ([0-9]+) and 65536 inclusive", "match": req_min_hit},
        {"field": "requirement.max", "pattern": r"between [0-9]+ and ([0-9]+) inclusive", "match": req_max_hit},
        {"field": "api.min", "pattern": r"between ([0-9]+) and 65536 inclusive", "match": api_min_hit},
        {"field": "api.max", "pattern": r"between [0-9]+ and ([0-9]+) inclusive", "match": api_max_hit},
        {"field": "code.max", "pattern": r"SQLITE_MAX_PAGE_SIZE ([0-9]+)", "match": code_max_hit},
        {"field": "code.default", "pattern": r"SQLITE_DEFAULT_PAGE_SIZE ([0-9]+)", "match": code_def_hit},
    ]

    return (
        ProjectArtifacts(
            name=name,
            requirement=LayerBounds(
                lower=req_min,
                upper=req_max,
                source=req_url,
                note="PRAGMA page_size range in docs.",
            ),
            api=LayerBounds(
                lower=api_min,
                upper=api_max,
                source=api_url,
                note="file-format documented range.",
            ),
            code=LayerBounds(
                lower=None,
                upper=code_max,
                source=code_url,
                note=f"sqliteLimit.h max/default = {code_max}/{code_default}.",
            ),
        ),
        patterns,
    )


def run(
    offline_lock_path: Optional[Path] = None,
    failure_policy: FailurePolicy = "fail-fast",
    none_semantics: NoneSemantics = "must",
) -> dict:
    if failure_policy == "fail-fast" and none_semantics != "must":
        raise ValueError("none-semantics=may requires --failure-policy none")

    base_dir = Path(__file__).resolve().parent
    snapshots_dir = base_dir / "snapshots"
    source_records: dict[str, SourceRecord] = {}
    run_date = datetime.now(timezone.utc).date().isoformat()
    offline_records: Optional[dict[str, SourceRecord]] = None
    if offline_lock_path is not None:
        offline_records = load_offline_records(offline_lock_path)

    parse_issues: list[dict] = []
    projects_and_patterns = [
        postgres_artifacts(source_records, snapshots_dir, offline_records, failure_policy, parse_issues),
        zlib_artifacts(source_records, snapshots_dir, offline_records, failure_policy, parse_issues),
        sqlite_artifacts(source_records, snapshots_dir, offline_records, failure_policy, parse_issues),
    ]

    real_results = []
    mutation_results = []
    extraction_patterns = {}

    for p, patterns in projects_and_patterns:
        extraction_patterns[p.name] = patterns
        layer_issue_flags = {
            "requirement": any(
                issue["project"] == p.name and issue["layer"] == "requirement" for issue in parse_issues
            ),
            "api": any(issue["project"] == p.name and issue["layer"] == "api" for issue in parse_issues),
            "code": any(issue["project"] == p.name and issue["layer"] == "code" for issue in parse_issues),
        }
        has_project_parse_issue = any(layer_issue_flags.values())

        layer_status = compute_layer_status(
            p.requirement,
            p.api,
            p.code,
            layer_issue_flags=layer_issue_flags,
        )
        lifted_must = {
            name: status_to_membership(status, "must") for name, status in layer_status.items()
        }
        lifted_may = {
            name: status_to_membership(status, "may") for name, status in layer_status.items()
        }
        support_count = status_count(layer_status, "supported")
        unknown_count = status_count(layer_status, "unknown")
        invalid_interval_count = status_count(layer_status, "invalid")
        u0_support_indicator = support_count > 0
        u0_unfalsified_indicator = (support_count + unknown_count) > 0
        support_ratio = status_ratio(layer_status, "supported")
        unknown_ratio = status_ratio(layer_status, "unknown")
        invalid_interval_ratio = status_ratio(layer_status, "invalid")

        judgement, lower, upper, reason = classify_uand(
            p.requirement,
            p.api,
            p.code,
            undefined_from_parse=has_project_parse_issue,
        )
        policy_judgement = apply_none_policy(judgement, none_semantics)

        real_results.append(
            {
                "project": p.name,
                "consistent": policy_judgement == "consistent",
                "policy_judgement": policy_judgement,
                "judgement": judgement,
                "intersection_lower": lower,
                "intersection_upper": upper,
                "consistency_reason": reason,
                "has_parse_issue": has_project_parse_issue,
                "u0_support_indicator": u0_support_indicator,
                "u0_unfalsified_indicator": u0_unfalsified_indicator,
                "u0_unknown_only": support_count == 0 and unknown_count > 0,
                "support_count": support_count,
                "unknown_count": unknown_count,
                "invalid_interval_count": invalid_interval_count,
                "support_ratio": support_ratio,
                "unknown_ratio": unknown_ratio,
                "invalid_interval_ratio": invalid_interval_ratio,
                "u0_support_layers": layers_with_status(layer_status, "supported"),
                "u0_unknown_layers": layers_with_status(layer_status, "unknown"),
                "u0_invalid_interval_layers": layers_with_status(layer_status, "invalid"),
                "layer_status": layer_status,
                "lifted_membership": {
                    "must": lifted_must,
                    "may": lifted_may,
                },
                "artifacts": asdict(p),
            }
        )

        if lower is None or upper is None:
            mutation_results.append(
                {
                    "project": p.name,
                    "mutation_id": "stale_requirement_lower",
                    "expected_outcome": "raw_judgement=contradictory",
                    "detected_expectation": None,
                    "expectation_satisfied": None,
                    "skipped": True,
                    "reason": "mutation_skipped_missing_intersection_bounds",
                }
            )
            mutation_results.append(
                {
                    "project": p.name,
                    "mutation_id": "unit_mismatch_upper_scale_down_1024",
                    "expected_outcome": "intersection_upper_at_most_floor_baseline_div_1024",
                    "detected_expectation": None,
                    "expectation_satisfied": None,
                    "skipped": True,
                    "reason": "mutation_skipped_missing_intersection_bounds",
                }
            )
            continue

        stale_lower_requirement = LayerBounds(
            lower=upper + 1,
            upper=p.requirement.upper,
            source=p.requirement.source,
            note="mutation: stale requirement lower bound exceeds implementation/API upper bound",
        )
        stale_judgement, stale_lower, stale_upper, stale_reason = classify_uand(
            stale_lower_requirement,
            p.api,
            p.code,
            undefined_from_parse=has_project_parse_issue,
        )
        stale_policy_judgement = apply_none_policy(stale_judgement, none_semantics)
        stale_layer_status = compute_layer_status(
            stale_lower_requirement,
            p.api,
            p.code,
            layer_issue_flags=layer_issue_flags,
        )
        stale_lifted_must = {
            name: status_to_membership(status, "must") for name, status in stale_layer_status.items()
        }
        stale_lifted_may = {
            name: status_to_membership(status, "may") for name, status in stale_layer_status.items()
        }
        stale_support_count = status_count(stale_layer_status, "supported")
        stale_unknown_count = status_count(stale_layer_status, "unknown")
        stale_invalid_interval_count = status_count(stale_layer_status, "invalid")
        mutation_results.append(
            {
                "project": p.name,
                "mutation_id": "stale_requirement_lower",
                "expected_outcome": "raw_judgement=contradictory",
                "detected_expectation": stale_judgement == "contradictory",
                "expectation_satisfied": stale_judgement == "contradictory",
                "policy_judgement": stale_policy_judgement,
                "judgement": stale_judgement,
                "mutated_intersection_lower": stale_lower,
                "mutated_intersection_upper": stale_upper,
                "consistency_reason": stale_reason,
                "mutated_u0_support_indicator": any(stale_lifted_must.values()),
                "mutated_u0_unfalsified_indicator": any(stale_lifted_may.values()),
                "mutated_support_count": stale_support_count,
                "mutated_unknown_count": stale_unknown_count,
                "mutated_invalid_interval_count": stale_invalid_interval_count,
                "mutated_u0_support_layers": layers_with_status(stale_layer_status, "supported"),
                "mutated_u0_unknown_layers": layers_with_status(stale_layer_status, "unknown"),
                "mutated_u0_invalid_interval_layers": layers_with_status(stale_layer_status, "invalid"),
                "skipped": False,
            }
        )

        scaled_upper = None
        if p.requirement.upper is not None:
            scaled_upper = max(0, p.requirement.upper // 1024)
        unit_mismatch_requirement = LayerBounds(
            lower=p.requirement.lower,
            upper=scaled_upper,
            source=p.requirement.source,
            note="mutation: unit mismatch (upper bound scaled down by 1024)",
        )
        unit_judgement, unit_lower, unit_upper, unit_reason = classify_uand(
            unit_mismatch_requirement,
            p.api,
            p.code,
            undefined_from_parse=has_project_parse_issue,
        )
        unit_policy_judgement = apply_none_policy(unit_judgement, none_semantics)
        unit_layer_status = compute_layer_status(
            unit_mismatch_requirement,
            p.api,
            p.code,
            layer_issue_flags=layer_issue_flags,
        )
        unit_lifted_must = {
            name: status_to_membership(status, "must") for name, status in unit_layer_status.items()
        }
        unit_lifted_may = {
            name: status_to_membership(status, "may") for name, status in unit_layer_status.items()
        }
        unit_support_count = status_count(unit_layer_status, "supported")
        unit_unknown_count = status_count(unit_layer_status, "unknown")
        unit_invalid_interval_count = status_count(unit_layer_status, "invalid")
        expected_upper_threshold = upper // 1024
        unit_expectation_detected = unit_upper is not None and unit_upper <= expected_upper_threshold
        mutation_results.append(
            {
                "project": p.name,
                "mutation_id": "unit_mismatch_upper_scale_down_1024",
                "expected_outcome": "intersection_upper_at_most_floor_baseline_div_1024",
                "expected_upper_threshold": expected_upper_threshold,
                "detected_expectation": unit_expectation_detected,
                "expectation_satisfied": unit_expectation_detected,
                "detection_basis": [
                    "intersection_upper_le_floor_baseline_div_1024"
                ] if unit_expectation_detected else [
                    "intersection_upper_not_le_floor_baseline_div_1024"
                ],
                "policy_judgement": unit_policy_judgement,
                "judgement": unit_judgement,
                "mutated_intersection_lower": unit_lower,
                "mutated_intersection_upper": unit_upper,
                "consistency_reason": unit_reason,
                "mutated_u0_support_indicator": any(unit_lifted_must.values()),
                "mutated_u0_unfalsified_indicator": any(unit_lifted_may.values()),
                "mutated_support_count": unit_support_count,
                "mutated_unknown_count": unit_unknown_count,
                "mutated_invalid_interval_count": unit_invalid_interval_count,
                "mutated_u0_support_layers": layers_with_status(unit_layer_status, "supported"),
                "mutated_u0_unknown_layers": layers_with_status(unit_layer_status, "unknown"),
                "mutated_u0_invalid_interval_layers": layers_with_status(unit_layer_status, "invalid"),
                "skipped": False,
            }
        )

    raw_distribution = {
        "consistent": sum(1 for x in real_results if x["judgement"] == "consistent"),
        "contradictory": sum(1 for x in real_results if x["judgement"] == "contradictory"),
        "inconclusive": sum(1 for x in real_results if x["judgement"] == "inconclusive"),
    }
    policy_distribution = {
        "consistent": sum(1 for x in real_results if x["policy_judgement"] == "consistent"),
        "contradictory": sum(1 for x in real_results if x["policy_judgement"] == "contradictory"),
        "inconclusive": sum(1 for x in real_results if x["policy_judgement"] == "inconclusive"),
    }
    layer_names = ["requirement", "api", "code"]
    support_frequency = {
        layer: sum(1 for x in real_results if x["layer_status"][layer] == "supported") for layer in layer_names
    }
    unknown_frequency = {
        layer: sum(1 for x in real_results if x["layer_status"][layer] == "unknown") for layer in layer_names
    }
    invalid_interval_frequency = {
        layer: sum(1 for x in real_results if x["layer_status"][layer] == "invalid") for layer in layer_names
    }

    summary = {
        "date": run_date,
        "failure_policy": failure_policy,
        "none_semantics": none_semantics,
        "extraction_mode": (
            "automatic_regex_no_manual_edit_offline_snapshot_replay"
            if offline_records is not None
            else "automatic_regex_no_manual_edit_online_fetch"
        ),
        "network_required": offline_records is None,
        "n_real_projects": len(real_results),
        "n_real_consistent": policy_distribution["consistent"],
        "n_real_contradictory": policy_distribution["contradictory"],
        "n_real_inconclusive": raw_distribution["inconclusive"],
        "raw_judgement_distribution": raw_distribution,
        "policy_judgement_distribution": policy_distribution,
        "n_u0_support_indicator": sum(1 for x in real_results if x["u0_support_indicator"]),
        "n_u0_unfalsified_indicator": sum(1 for x in real_results if x["u0_unfalsified_indicator"]),
        "n_u0_unknown_only": sum(1 for x in real_results if x["u0_unknown_only"]),
        "avg_support_ratio": (
            sum(x["support_ratio"] for x in real_results) / len(real_results) if real_results else 0.0
        ),
        "avg_unknown_ratio": (
            sum(x["unknown_ratio"] for x in real_results) / len(real_results) if real_results else 0.0
        ),
        "avg_invalid_interval_ratio": (
            sum(x["invalid_interval_ratio"] for x in real_results) / len(real_results) if real_results else 0.0
        ),
        "support_frequency": support_frequency,
        "unknown_frequency": unknown_frequency,
        "invalid_interval_frequency": invalid_interval_frequency,
        "mutation_total": len(mutation_results),
        "mutation_detected_by_expectation": sum(
            1 for x in mutation_results if x.get("detected_expectation") is True
        ),
        "mutation_expected_contradictory_total": sum(
            1 for x in mutation_results if x.get("expected_outcome") == "raw_judgement=contradictory"
        ),
        "mutation_detected_contradictory": sum(
            1
            for x in mutation_results
            if x.get("expected_outcome") == "raw_judgement=contradictory"
            and x.get("detected_expectation") is True
        ),
        "mutation_expected_change_total": sum(
            1
            for x in mutation_results
            if x.get("expected_outcome") == "intersection_upper_at_most_floor_baseline_div_1024"
        ),
        "mutation_detected_change": sum(
            1
            for x in mutation_results
            if x.get("expected_outcome") == "intersection_upper_at_most_floor_baseline_div_1024"
            and x.get("detected_expectation") is True
        ),
        "mutation_skipped": sum(1 for x in mutation_results if x.get("skipped")),
        "parse_issue_count": len(parse_issues),
        "parse_issues": parse_issues,
        "real_results": real_results,
        "mutation_results": mutation_results,
        "source_lock": [asdict(x) for x in source_records.values()],
        "extraction_patterns": extraction_patterns,
    }
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description="External validation runner for UAD/f interval consistency.")
    parser.add_argument(
        "--offline-lock",
        type=Path,
        default=None,
        help="Path to external_validation_sources.lock.json for offline snapshot replay.",
    )
    parser.add_argument(
        "--failure-policy",
        choices=["fail-fast", "none"],
        default="fail-fast",
        help="Extraction failure handling: fail-fast (raise) or none (propagate undefined).",
    )
    parser.add_argument(
        "--none-semantics",
        choices=["must", "may"],
        default="must",
        help="Consistency policy when undefined bounds exist (used with --failure-policy none).",
    )
    args = parser.parse_args()

    base_dir = Path(__file__).resolve().parent
    result = run(args.offline_lock, args.failure_policy, args.none_semantics)

    out_path = base_dir / "external_validation_results.json"
    out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    # Keep deterministic replay inputs immutable: only online acquisition rewrites
    # the canonical lock. Offline replay must not clobber the pinned lock file.
    if args.offline_lock is None:
        lock_path = base_dir / "external_validation_sources.lock.json"
        lock_payload = {
            "date": result["date"],
            "source_lock": result["source_lock"],
        }
        lock_path.write_text(json.dumps(lock_payload, indent=2), encoding="utf-8")

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
