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
from typing import Optional


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


def parse_first_int(pattern: str, text: str, label: str) -> tuple[int, str]:
    m = re.search(pattern, text, flags=re.IGNORECASE)
    if not m:
        raise ValueError(f"failed to parse {label} with pattern: {pattern}")
    return int(m.group(1)), m.group(0)


def check_consistent(*layers: LayerBounds) -> tuple[bool, Optional[int], Optional[int]]:
    lowers = [x.lower for x in layers if x.lower is not None]
    uppers = [x.upper for x in layers if x.upper is not None]
    if not lowers or not uppers:
        return False, None, None
    lower = max(lowers)
    upper = min(uppers)
    return lower <= upper, lower, upper


def postgres_artifacts(
    source_records: dict[str, SourceRecord],
    snapshots_dir: Path,
    offline_records: Optional[dict[str, SourceRecord]] = None,
) -> tuple[ProjectArtifacts, list[dict]]:
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
    )
    api_max, api_hit = parse_first_int(
        r"maximum identifier length is\s+([0-9]+)\s+bytes",
        api_txt,
        "postgres api max",
    )
    namedatalen, code_hit = parse_first_int(r"#define\s+NAMEDATALEN\s+([0-9]+)", code_txt, "postgres NAMEDATALEN")

    patterns = [
        {"field": "requirement.upper", "pattern": r"max_identifier_length\\s+is\\s+([0-9]+)\\s+bytes", "match": req_hit},
        {"field": "api.upper", "pattern": r"maximum identifier length is\\s+([0-9]+)\\s+bytes", "match": api_hit},
        {"field": "code.namedatalen", "pattern": r"#define\\s+NAMEDATALEN\\s+([0-9]+)", "match": code_hit},
    ]

    return (
        ProjectArtifacts(
            name="PostgreSQL identifier length",
            requirement=LayerBounds(
                lower=1,
                upper=req_max,
                source=req_url,
                note="max_identifier_length documented default.",
            ),
            api=LayerBounds(
                lower=1,
                upper=api_max,
                source=api_url,
                note="SQL lexical maximum identifier length.",
            ),
            code=LayerBounds(
                lower=None,
                upper=namedatalen - 1,
                source=code_url,
                note="NAMEDATALEN-1 from source constant.",
            ),
        ),
        patterns,
    )


def zlib_artifacts(
    source_records: dict[str, SourceRecord],
    snapshots_dir: Path,
    offline_records: Optional[dict[str, SourceRecord]] = None,
) -> tuple[ProjectArtifacts, list[dict]]:
    req_url = "https://www.zlib.net/manual.html"
    api_url = "https://docs.python.org/3/library/zlib.html"
    code_url = "https://raw.githubusercontent.com/madler/zlib/master/zlib.h"

    req_txt = html_to_text(fetch_text(req_url, snapshots_dir, source_records, offline_records))
    api_txt = html_to_text(fetch_text(api_url, snapshots_dir, source_records, offline_records))
    code_txt = fetch_text(code_url, snapshots_dir, source_records, offline_records)

    req_hit = "between 0 and 9"
    api_hit = "integer from 0 to 9 or -1"
    if req_hit not in req_txt:
        raise ValueError("failed to locate zlib requirement interval")
    if api_hit not in api_txt:
        raise ValueError("failed to locate python-zlib api interval")

    z_no, no_hit = parse_first_int(r"#define\s+Z_NO_COMPRESSION\s+(-?[0-9]+)", code_txt, "zlib Z_NO_COMPRESSION")
    z_best, best_hit = parse_first_int(r"#define\s+Z_BEST_COMPRESSION\s+(-?[0-9]+)", code_txt, "zlib Z_BEST_COMPRESSION")
    z_default, def_hit = parse_first_int(
        r"#define\s+Z_DEFAULT_COMPRESSION\s+\((-?[0-9]+)\)",
        code_txt,
        "zlib Z_DEFAULT_COMPRESSION",
    )

    patterns = [
        {"field": "requirement.interval", "pattern": "between 0 and 9", "match": req_hit},
        {"field": "api.interval", "pattern": "integer from 0 to 9 or -1", "match": api_hit},
        {"field": "code.z_no", "pattern": r"#define\\s+Z_NO_COMPRESSION\\s+(-?[0-9]+)", "match": no_hit},
        {"field": "code.z_best", "pattern": r"#define\\s+Z_BEST_COMPRESSION\\s+(-?[0-9]+)", "match": best_hit},
        {"field": "code.z_default", "pattern": r"#define\\s+Z_DEFAULT_COMPRESSION\\s+\\((-?[0-9]+)\\)", "match": def_hit},
    ]

    return (
        ProjectArtifacts(
            name="zlib compression level",
            requirement=LayerBounds(
                lower=min(0, z_default),
                upper=9,
                source=req_url,
                note="manual: Z_DEFAULT_COMPRESSION or [0,9]",
            ),
            api=LayerBounds(
                lower=-1,
                upper=9,
                source=api_url,
                note="python zlib API interval.",
            ),
            code=LayerBounds(
                lower=min(z_no, z_default),
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
    offline_records: Optional[dict[str, SourceRecord]] = None,
) -> tuple[ProjectArtifacts, list[dict]]:
    req_url = "https://www.sqlite.org/pragma.html#pragma_page_size"
    api_url = "https://www.sqlite.org/fileformat.html"
    code_url = "https://www.sqlite.org/src/doc/tip/src/sqliteLimit.h"

    req_txt = html_to_text(fetch_text(req_url, snapshots_dir, source_records, offline_records))
    api_txt = html_to_text(fetch_text(api_url, snapshots_dir, source_records, offline_records))
    code_txt = html_to_text(fetch_text(code_url, snapshots_dir, source_records, offline_records))

    req_min, req_min_hit = parse_first_int(r"between ([0-9]+) and 65536 inclusive", req_txt, "sqlite requirement min")
    req_max, req_max_hit = parse_first_int(r"between [0-9]+ and ([0-9]+) inclusive", req_txt, "sqlite requirement max")
    api_min, api_min_hit = parse_first_int(r"between ([0-9]+) and 65536 inclusive", api_txt, "sqlite api min")
    api_max, api_max_hit = parse_first_int(r"between [0-9]+ and ([0-9]+) inclusive", api_txt, "sqlite api max")
    code_max, code_max_hit = parse_first_int(r"SQLITE_MAX_PAGE_SIZE ([0-9]+)", code_txt, "sqlite code max")
    code_default, code_def_hit = parse_first_int(r"SQLITE_DEFAULT_PAGE_SIZE ([0-9]+)", code_txt, "sqlite default page size")

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
            name="SQLite page size",
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


def run(offline_lock_path: Optional[Path] = None) -> dict:
    base_dir = Path(__file__).resolve().parent
    snapshots_dir = base_dir / "snapshots"
    source_records: dict[str, SourceRecord] = {}
    run_date = datetime.now(timezone.utc).date().isoformat()
    offline_records: Optional[dict[str, SourceRecord]] = None
    if offline_lock_path is not None:
        offline_records = load_offline_records(offline_lock_path)

    projects_and_patterns = [
        postgres_artifacts(source_records, snapshots_dir, offline_records),
        zlib_artifacts(source_records, snapshots_dir, offline_records),
        sqlite_artifacts(source_records, snapshots_dir, offline_records),
    ]

    real_results = []
    mutation_results = []
    extraction_patterns = {}

    for p, patterns in projects_and_patterns:
        extraction_patterns[p.name] = patterns
        ok, lower, upper = check_consistent(p.requirement, p.api, p.code)
        real_results.append(
            {
                "project": p.name,
                "consistent": ok,
                "intersection_lower": lower,
                "intersection_upper": upper,
                "artifacts": asdict(p),
            }
        )

        if lower is None or upper is None:
            continue
        mutated_requirement = LayerBounds(
            lower=upper + 1,
            upper=p.requirement.upper,
            source=p.requirement.source,
            note="mutation: stale requirement lower bound exceeds implementation/API upper bound",
        )
        mut_ok, mut_lower, mut_upper = check_consistent(mutated_requirement, p.api, p.code)
        mutation_results.append(
            {
                "project": p.name,
                "expected_contradictory": True,
                "detected_contradictory": not mut_ok,
                "mutated_intersection_lower": mut_lower,
                "mutated_intersection_upper": mut_upper,
            }
        )

    summary = {
        "date": run_date,
        "extraction_mode": (
            "automatic_regex_no_manual_edit_offline_snapshot_replay"
            if offline_records is not None
            else "automatic_regex_no_manual_edit_online_fetch"
        ),
        "network_required": offline_records is None,
        "n_real_projects": len(real_results),
        "n_real_consistent": sum(1 for x in real_results if x["consistent"]),
        "n_real_contradictory": sum(1 for x in real_results if not x["consistent"]),
        "mutation_total": len(mutation_results),
        "mutation_detected": sum(1 for x in mutation_results if x["detected_contradictory"]),
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
    args = parser.parse_args()

    base_dir = Path(__file__).resolve().parent
    result = run(args.offline_lock)

    out_path = base_dir / "external_validation_results.json"
    out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    lock_path = base_dir / "external_validation_sources.lock.json"
    lock_payload = {
        "date": result["date"],
        "source_lock": result["source_lock"],
    }
    lock_path.write_text(json.dumps(lock_payload, indent=2), encoding="utf-8")

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
