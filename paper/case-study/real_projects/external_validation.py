#!/usr/bin/env python3
"""External validation on real OSS artifacts for UAD/f interval consistency.

This script fetches constraints from official documentation/source pages and
checks cross-layer consistency via interval intersection.
"""

from __future__ import annotations

import html
import json
import re
import urllib.request
from dataclasses import asdict, dataclass
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


def fetch_text(url: str) -> str:
    req = urllib.request.Request(url, headers={"User-Agent": "spec-oracle/1.0"})
    with urllib.request.urlopen(req, timeout=30) as res:
        return res.read().decode("utf-8", errors="replace")


def html_to_text(raw: str) -> str:
    text = re.sub(r"<script.*?</script>", " ", raw, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r"<style.*?</style>", " ", text, flags=re.IGNORECASE | re.DOTALL)
    text = re.sub(r"<[^>]+>", " ", text)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text)
    return text


def parse_first_int(pattern: str, text: str, label: str) -> int:
    m = re.search(pattern, text, flags=re.IGNORECASE)
    if not m:
        raise ValueError(f"failed to parse {label}")
    return int(m.group(1))


def check_consistent(*layers: LayerBounds) -> tuple[bool, Optional[int], Optional[int]]:
    lowers = [x.lower for x in layers if x.lower is not None]
    uppers = [x.upper for x in layers if x.upper is not None]
    if not lowers or not uppers:
        return False, None, None
    lower = max(lowers)
    upper = min(uppers)
    return lower <= upper, lower, upper


def postgres_artifacts() -> ProjectArtifacts:
    req_url = "https://www.postgresql.org/docs/current/runtime-config-preset.html"
    api_url = "https://www.postgresql.org/docs/current/sql-syntax-lexical.html"
    code_url = "https://raw.githubusercontent.com/postgres/postgres/master/src/include/pg_config_manual.h"

    req_txt = html_to_text(fetch_text(req_url))
    api_txt = html_to_text(fetch_text(api_url))
    code_txt = fetch_text(code_url)

    req_max = parse_first_int(
        r"max_identifier_length\s+is\s+([0-9]+)\s+bytes",
        req_txt,
        "postgres requirement max",
    )
    api_max = parse_first_int(
        r"maximum identifier length is\s+([0-9]+)\s+bytes",
        api_txt,
        "postgres api max",
    )
    namedatalen = parse_first_int(r"#define\s+NAMEDATALEN\s+([0-9]+)", code_txt, "postgres NAMEDATALEN")

    return ProjectArtifacts(
        name="PostgreSQL identifier length",
        requirement=LayerBounds(
            lower=1,
            upper=req_max,
            source=req_url,
            note="max_identifier_length is documented as 63 bytes by default.",
        ),
        api=LayerBounds(
            lower=1,
            upper=api_max,
            source=api_url,
            note="SQL lexical doc states maximum identifier length is 63 bytes by default.",
        ),
        code=LayerBounds(
            lower=None,
            upper=namedatalen - 1,
            source=code_url,
            note="NAMEDATALEN=64 implies default identifier cap 63 bytes.",
        ),
    )


def zlib_artifacts() -> ProjectArtifacts:
    req_url = "https://www.zlib.net/manual.html"
    api_url = "https://docs.python.org/3/library/zlib.html"
    code_url = "https://raw.githubusercontent.com/madler/zlib/master/zlib.h"

    req_txt = html_to_text(fetch_text(req_url))
    api_txt = html_to_text(fetch_text(api_url))
    code_txt = fetch_text(code_url)

    if "between 0 and 9" not in req_txt:
        raise ValueError("failed to locate zlib requirement interval")
    if "integer from 0 to 9 or -1" not in api_txt:
        raise ValueError("failed to locate python-zlib api interval")

    z_no = parse_first_int(r"#define\s+Z_NO_COMPRESSION\s+(-?[0-9]+)", code_txt, "zlib Z_NO_COMPRESSION")
    z_best = parse_first_int(r"#define\s+Z_BEST_COMPRESSION\s+(-?[0-9]+)", code_txt, "zlib Z_BEST_COMPRESSION")
    z_default = parse_first_int(r"#define\s+Z_DEFAULT_COMPRESSION\s+\((-?[0-9]+)\)", code_txt, "zlib Z_DEFAULT_COMPRESSION")

    return ProjectArtifacts(
        name="zlib compression level",
        requirement=LayerBounds(
            lower=min(0, z_default),
            upper=9,
            source=req_url,
            note="manual: level is Z_DEFAULT_COMPRESSION or between 0 and 9.",
        ),
        api=LayerBounds(
            lower=-1,
            upper=9,
            source=api_url,
            note="python zlib API: integer from 0 to 9 or -1.",
        ),
        code=LayerBounds(
            lower=min(z_no, z_default),
            upper=z_best,
            source=code_url,
            note="zlib.h constants define supported range endpoints.",
        ),
    )


def sqlite_artifacts() -> ProjectArtifacts:
    req_url = "https://www.sqlite.org/pragma.html#pragma_page_size"
    api_url = "https://www.sqlite.org/fileformat.html"
    code_url = "https://www.sqlite.org/src/doc/tip/src/sqliteLimit.h"

    req_txt = html_to_text(fetch_text(req_url))
    api_txt = html_to_text(fetch_text(api_url))
    code_txt = html_to_text(fetch_text(code_url))

    req_min = parse_first_int(r"between ([0-9]+) and 65536 inclusive", req_txt, "sqlite requirement min")
    req_max = parse_first_int(r"between [0-9]+ and ([0-9]+) inclusive", req_txt, "sqlite requirement max")
    api_min = parse_first_int(r"between ([0-9]+) and 65536 inclusive", api_txt, "sqlite api min")
    api_max = parse_first_int(r"between [0-9]+ and ([0-9]+) inclusive", api_txt, "sqlite api max")
    code_max = parse_first_int(r"SQLITE_MAX_PAGE_SIZE ([0-9]+)", code_txt, "sqlite code max")
    code_default = parse_first_int(r"SQLITE_DEFAULT_PAGE_SIZE ([0-9]+)", code_txt, "sqlite default page size")

    return ProjectArtifacts(
        name="SQLite page size",
        requirement=LayerBounds(
            lower=req_min,
            upper=req_max,
            source=req_url,
            note="PRAGMA page_size: power of two between 512 and 65536 inclusive.",
        ),
        api=LayerBounds(
            lower=api_min,
            upper=api_max,
            source=api_url,
            note="file format doc states same page-size range.",
        ),
        code=LayerBounds(
            lower=None,
            upper=code_max,
            source=code_url,
            note=f"sqliteLimit.h: SQLITE_MAX_PAGE_SIZE={code_max}, SQLITE_DEFAULT_PAGE_SIZE={code_default}.",
        ),
    )


def run() -> dict:
    projects = [postgres_artifacts(), zlib_artifacts(), sqlite_artifacts()]

    real_results = []
    mutation_results = []
    for p in projects:
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
            note="mutation test: force requirement lower bound above computed upper bound",
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
        "date": "2026-02-14",
        "n_real_projects": len(real_results),
        "n_real_consistent": sum(1 for x in real_results if x["consistent"]),
        "n_real_contradictory": sum(1 for x in real_results if not x["consistent"]),
        "mutation_total": len(mutation_results),
        "mutation_detected": sum(1 for x in mutation_results if x["detected_contradictory"]),
        "real_results": real_results,
        "mutation_results": mutation_results,
    }
    return summary


def main() -> None:
    result = run()
    out_path = Path(__file__).resolve().parent / "external_validation_results.json"
    out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
