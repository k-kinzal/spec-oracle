#!/usr/bin/env python3
"""Synthetic benchmark for password-policy layer integration.

Model alignment (same as Lean case study):
- Requirement layer: min_req <= n <= max_req
- API layer: min_api <= n
- Code layer: n <= max_code

Consistency iff max(min_req, min_api) <= min(max_req, max_code)
"""

from __future__ import annotations

import json
import platform
import random
import statistics
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class ReqArtifact:
    min_len: int
    max_len: int


@dataclass(frozen=True)
class ApiArtifact:
    min_len: int


@dataclass(frozen=True)
class CodeArtifact:
    max_len: int


def check_consistent(req: ReqArtifact, api: ApiArtifact, code: CodeArtifact) -> bool:
    lower = max(req.min_len, api.min_len)
    upper = min(req.max_len, code.max_len)
    return lower <= upper


def classify(req: ReqArtifact, api: ApiArtifact, code: CodeArtifact) -> str:
    return "consistent" if check_consistent(req, api, code) else "contradictory"


def brute_force_consistent(req: ReqArtifact, api: ApiArtifact, code: CodeArtifact) -> bool:
    upper_scan = max(req.max_len, code.max_len, api.min_len, req.min_len)
    for n in range(upper_scan + 1):
        if req.min_len <= n <= req.max_len and api.min_len <= n and n <= code.max_len:
            return True
    return False


def sample_artifact(rng: random.Random) -> tuple[ReqArtifact, ApiArtifact, CodeArtifact]:
    req_min = rng.randint(6, 24)
    req_max = rng.randint(req_min, 128)
    api_min = rng.randint(6, 40)
    code_max = rng.randint(8, 120)
    return ReqArtifact(req_min, req_max), ApiArtifact(api_min), CodeArtifact(code_max)


def run_once(seed: int, n_cases: int) -> dict:
    rng = random.Random(seed)
    t0 = time.perf_counter()

    contradictions = 0
    consistent = 0
    lowers = []
    uppers = []

    for _ in range(n_cases):
        req, api, code = sample_artifact(rng)
        lower = max(req.min_len, api.min_len)
        upper = min(req.max_len, code.max_len)
        lowers.append(lower)
        uppers.append(upper)
        if lower <= upper:
            consistent += 1
        else:
            contradictions += 1

    dt = time.perf_counter() - t0

    return {
        "seed": seed,
        "n_cases": n_cases,
        "consistent": consistent,
        "contradictory": contradictions,
        "contradictory_ratio": contradictions / n_cases,
        "avg_lower": statistics.mean(lowers),
        "avg_upper": statistics.mean(uppers),
        "elapsed_sec": dt,
        "throughput_cases_per_sec": n_cases / dt if dt > 0 else None,
    }


def main() -> None:
    n_cases = 200_000
    seeds = [17, 29, 43, 71, 89]
    runs = [run_once(seed, n_cases) for seed in seeds]

    # Baseline: compare O(1) closed-form checker vs brute-force scan.
    baseline_seed = 101
    baseline_cases = 20_000
    rng = random.Random(baseline_seed)
    artifacts = [sample_artifact(rng) for _ in range(baseline_cases)]

    t_formula0 = time.perf_counter()
    formula_results = [check_consistent(req, api, code) for req, api, code in artifacts]
    t_formula = time.perf_counter() - t_formula0

    t_bruteforce0 = time.perf_counter()
    brute_results = [brute_force_consistent(req, api, code) for req, api, code in artifacts]
    t_bruteforce = time.perf_counter() - t_bruteforce0

    mismatches = sum(1 for a, b in zip(formula_results, brute_results) if a != b)

    summary = {
        "n_cases_per_run": n_cases,
        "n_runs": len(runs),
        "avg_contradictory_ratio": statistics.mean(r["contradictory_ratio"] for r in runs),
        "avg_elapsed_sec": statistics.mean(r["elapsed_sec"] for r in runs),
        "avg_throughput_cases_per_sec": statistics.mean(r["throughput_cases_per_sec"] for r in runs),
        "environment": {
            "python_version": platform.python_version(),
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
        },
        "baseline_comparison": {
            "seed": baseline_seed,
            "n_cases": baseline_cases,
            "formula_elapsed_sec": t_formula,
            "bruteforce_elapsed_sec": t_bruteforce,
            "speedup_formula_vs_bruteforce": (t_bruteforce / t_formula) if t_formula > 0 else None,
            "result_mismatches": mismatches,
        },
        "runs": runs,
    }

    out_path = Path(__file__).resolve().parent / "benchmark_results.json"
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
