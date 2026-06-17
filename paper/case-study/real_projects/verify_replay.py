#!/usr/bin/env python3
"""Replay verification helper for engineering-paper acceptance checks.

This script is intentionally stdlib-only.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def assert_main_metrics(log: dict) -> None:
    assert log["n_real_projects"] == 3, f"n_real_projects mismatch: {log['n_real_projects']}"

    raw = log["raw_judgement_distribution"]
    assert raw.get("consistent") == 3, f"raw.consistent mismatch: {raw}"
    assert raw.get("contradictory") == 0, f"raw.contradictory mismatch: {raw}"
    assert raw.get("inconclusive") == 0, f"raw.inconclusive mismatch: {raw}"

    policy = log["policy_judgement_distribution"]
    assert policy.get("consistent") == 3, f"policy.consistent mismatch: {policy}"
    assert policy.get("contradictory") == 0, f"policy.contradictory mismatch: {policy}"
    assert policy.get("inconclusive") == 0, f"policy.inconclusive mismatch: {policy}"

    assert log["mutation_detected_by_expectation"] == 6, (
        "mutation_detected_by_expectation mismatch: "
        f"{log['mutation_detected_by_expectation']}"
    )


def assert_drift_metrics(must_log: dict, may_log: dict) -> None:
    raw_must = must_log["raw_judgement_distribution"]
    assert raw_must.get("consistent") == 2, f"drift must raw mismatch: {raw_must}"
    assert raw_must.get("contradictory") == 0, f"drift must raw mismatch: {raw_must}"
    assert raw_must.get("inconclusive") == 1, f"drift must raw mismatch: {raw_must}"

    policy_must = must_log["policy_judgement_distribution"]
    assert policy_must.get("consistent") == 2, f"drift must policy mismatch: {policy_must}"
    assert policy_must.get("contradictory") == 1, f"drift must policy mismatch: {policy_must}"
    assert policy_must.get("inconclusive") == 0, f"drift must policy mismatch: {policy_must}"

    raw_may = may_log["raw_judgement_distribution"]
    assert raw_may.get("consistent") == 2, f"drift may raw mismatch: {raw_may}"
    assert raw_may.get("contradictory") == 0, f"drift may raw mismatch: {raw_may}"
    assert raw_may.get("inconclusive") == 1, f"drift may raw mismatch: {raw_may}"

    policy_may = may_log["policy_judgement_distribution"]
    assert policy_may.get("consistent") == 3, f"drift may policy mismatch: {policy_may}"
    assert policy_may.get("contradictory") == 0, f"drift may policy mismatch: {policy_may}"
    assert policy_may.get("inconclusive") == 0, f"drift may policy mismatch: {policy_may}"


def assert_edge_log(path: Path) -> None:
    lines = [x.strip() for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]
    expected_prefixes = [
        "contradiction_min_gt_max",
        "boundary_equal",
        "zero_and_negative",
        "missing_bounds",
    ]
    assert len(lines) == len(expected_prefixes), f"edge-case line count mismatch: {len(lines)}"
    for line, prefix in zip(lines, expected_prefixes):
        assert line.startswith(prefix + " "), f"edge-case label mismatch: {line}"


def assert_ablation_report(report: dict) -> None:
    summary = report["summary"]
    assert summary["n_scenarios"] == 21, f"ablation n_scenarios mismatch: {summary['n_scenarios']}"
    assert summary["group_counts"] == {
        "contradiction": 6,
        "uncertainty": 9,
        "benign_change": 6,
    }, f"ablation group_counts mismatch: {summary['group_counts']}"

    contradiction = summary["contradiction_detection_rate"]
    assert contradiction["policy_must"] == 1.0, f"ablation contradiction.must mismatch: {contradiction}"
    assert contradiction["policy_may"] == 1.0, f"ablation contradiction.may mismatch: {contradiction}"
    assert contradiction["binary_strict"] == 1.0, f"ablation contradiction.binary mismatch: {contradiction}"

    false_contradiction = summary["false_contradiction_rate_on_non_contradiction"]
    assert false_contradiction["policy_must"] == 0.7333333333333333, (
        f"ablation false_contradiction.must mismatch: {false_contradiction}"
    )
    assert false_contradiction["policy_may"] == 0.13333333333333333, (
        f"ablation false_contradiction.may mismatch: {false_contradiction}"
    )
    assert false_contradiction["binary_strict"] == 0.8666666666666667, (
        f"ablation false_contradiction.binary mismatch: {false_contradiction}"
    )

    uncertainty = summary["uncertainty_collapse_rate"]
    assert uncertainty["policy_must"] == 1.0, f"ablation uncertainty.must mismatch: {uncertainty}"
    assert uncertainty["policy_may"] == 0.0, f"ablation uncertainty.may mismatch: {uncertainty}"
    assert uncertainty["binary_strict"] == 1.0, f"ablation uncertainty.binary mismatch: {uncertainty}"


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify replay outputs for paper PoC.")
    parser.add_argument(
        "--logs-dir",
        type=Path,
        default=Path("logs"),
        help="Directory containing replay logs (default: logs).",
    )
    args = parser.parse_args()

    logs_dir = args.logs_dir
    main_log = load_json(logs_dir / "external_validation_graceful_may.log")
    drift_must = load_json(logs_dir / "regex_drift_graceful_must.log")
    drift_may = load_json(logs_dir / "regex_drift_graceful_may.log")
    ablation = load_json(logs_dir / "policy_ablation_report.json")

    assert_main_metrics(main_log)
    assert_drift_metrics(drift_must, drift_may)
    assert_edge_log(logs_dir / "check_consistent_edge_cases.log")
    assert_ablation_report(ablation)

    print("OK: replay verification checks passed")


if __name__ == "__main__":
    main()
