#!/usr/bin/env python3
"""Policy and baseline ablation benchmark for the engineering manuscript.

Deterministic, stdlib-only, and replay-friendly.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from external_validation import (  # type: ignore
    LayerBounds,
    apply_none_policy,
    classify_uand,
    run,
)

RawJudgement = Literal["consistent", "contradictory", "inconclusive"]
PolicyDecision = Literal["consistent", "contradictory"]


@dataclass(frozen=True)
class Scenario:
    project: str
    scenario_id: str
    expectation_raw: RawJudgement
    expectation_group: Literal["contradiction", "uncertainty", "benign_change"]
    requirement: LayerBounds
    api: LayerBounds
    code: LayerBounds
    undefined_from_parse: bool = False


@dataclass(frozen=True)
class EvalRow:
    project: str
    scenario_id: str
    expectation_raw: RawJudgement
    expectation_group: str
    raw_judgement: RawJudgement
    policy_must: PolicyDecision
    policy_may: PolicyDecision
    binary_strict: PolicyDecision


def to_layer(d: dict) -> LayerBounds:
    return LayerBounds(
        lower=d.get("lower"),
        upper=d.get("upper"),
        source=d.get("source", ""),
        note=d.get("note", ""),
    )


def binary_strict(*layers: LayerBounds, undefined_from_parse: bool) -> PolicyDecision:
    if undefined_from_parse:
        return "contradictory"
    for l in layers:
        if l.lower is None or l.upper is None:
            return "contradictory"
    j, _, _, _ = classify_uand(*layers, undefined_from_parse=False)
    return "contradictory" if j == "contradictory" else "consistent"


def mk_scenarios(project: str, req: LayerBounds, api: LayerBounds, code: LayerBounds) -> list[Scenario]:
    # Baseline is expected consistent from replay-locked artifacts.
    req_upper = req.upper if req.upper is not None else 0
    req_lower = req.lower if req.lower is not None else 0
    api_lower = api.lower if api.lower is not None else 0

    scenarios: list[Scenario] = []

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="stale_requirement_lower",
            expectation_raw="contradictory",
            expectation_group="contradiction",
            requirement=LayerBounds(req_upper + 1, req.upper, req.source, req.note),
            api=api,
            code=code,
        )
    )

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="api_upper_below_requirement_lower",
            expectation_raw="contradictory",
            expectation_group="contradiction",
            requirement=req,
            api=LayerBounds(api.lower, req_lower - 1, api.source, api.note),
            code=code,
        )
    )

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="all_uppers_missing",
            expectation_raw="inconclusive",
            expectation_group="uncertainty",
            requirement=LayerBounds(req.lower, None, req.source, req.note),
            api=LayerBounds(api.lower, None, api.source, api.note),
            code=LayerBounds(code.lower, None, code.source, code.note),
        )
    )

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="all_lowers_missing",
            expectation_raw="inconclusive",
            expectation_group="uncertainty",
            requirement=LayerBounds(None, req.upper, req.source, req.note),
            api=LayerBounds(None, api.upper, api.source, api.note),
            code=LayerBounds(None, code.upper, code.source, code.note),
        )
    )

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="parse_issue",
            expectation_raw="inconclusive",
            expectation_group="uncertainty",
            requirement=req,
            api=api,
            code=code,
            undefined_from_parse=True,
        )
    )

    scaled_upper = max(0, req_upper // 1024)
    scenarios.append(
        Scenario(
            project=project,
            scenario_id="unit_scale_upper_1024",
            expectation_raw="consistent",
            expectation_group="benign_change",
            requirement=LayerBounds(req.lower, scaled_upper, req.source, req.note),
            api=api,
            code=code,
        )
    )

    scenarios.append(
        Scenario(
            project=project,
            scenario_id="off_by_one_upper",
            expectation_raw="consistent",
            expectation_group="benign_change",
            requirement=LayerBounds(req.lower, max(api_lower, req_upper - 1), req.source, req.note),
            api=api,
            code=code,
        )
    )

    return scenarios


def evaluate(scenarios: list[Scenario]) -> list[EvalRow]:
    rows: list[EvalRow] = []
    for s in scenarios:
        raw, _, _, _ = classify_uand(
            s.requirement,
            s.api,
            s.code,
            undefined_from_parse=s.undefined_from_parse,
        )
        must = apply_none_policy(raw, "must")
        may = apply_none_policy(raw, "may")
        bstrict = binary_strict(
            s.requirement,
            s.api,
            s.code,
            undefined_from_parse=s.undefined_from_parse,
        )
        rows.append(
            EvalRow(
                project=s.project,
                scenario_id=s.scenario_id,
                expectation_raw=s.expectation_raw,
                expectation_group=s.expectation_group,
                raw_judgement=raw,
                policy_must=must,
                policy_may=may,
                binary_strict=bstrict,
            )
        )
    return rows


def aggregate(rows: list[EvalRow]) -> dict:
    total = len(rows)
    by_group: dict[str, int] = {}
    for r in rows:
        by_group[r.expectation_group] = by_group.get(r.expectation_group, 0) + 1

    contradiction_rows = [r for r in rows if r.expectation_group == "contradiction"]
    non_contradiction_rows = [r for r in rows if r.expectation_group != "contradiction"]
    uncertainty_rows = [r for r in rows if r.expectation_group == "uncertainty"]

    def contradiction_rate(method: str, target: list[EvalRow]) -> float:
        if not target:
            return 0.0
        hit = sum(1 for r in target if getattr(r, method) == "contradictory")
        return hit / len(target)

    def raw_match_rate() -> float:
        if not rows:
            return 0.0
        return sum(1 for r in rows if r.raw_judgement == r.expectation_raw) / len(rows)

    summary = {
        "n_scenarios": total,
        "group_counts": by_group,
        "raw_exact_match_rate": raw_match_rate(),
        "contradiction_detection_rate": {
            "policy_must": contradiction_rate("policy_must", contradiction_rows),
            "policy_may": contradiction_rate("policy_may", contradiction_rows),
            "binary_strict": contradiction_rate("binary_strict", contradiction_rows),
        },
        "false_contradiction_rate_on_non_contradiction": {
            "policy_must": contradiction_rate("policy_must", non_contradiction_rows),
            "policy_may": contradiction_rate("policy_may", non_contradiction_rows),
            "binary_strict": contradiction_rate("binary_strict", non_contradiction_rows),
        },
        "uncertainty_collapse_rate": {
            "policy_must": contradiction_rate("policy_must", uncertainty_rows),
            "policy_may": contradiction_rate("policy_may", uncertainty_rows),
            "binary_strict": contradiction_rate("binary_strict", uncertainty_rows),
        },
    }
    return summary


def to_markdown(rows: list[EvalRow], summary: dict) -> str:
    lines: list[str] = []
    lines.append("# Policy Ablation Report")
    lines.append("")
    lines.append("## Summary")
    lines.append(f"- n_scenarios: {summary['n_scenarios']}")
    lines.append(f"- group_counts: {summary['group_counts']}")
    lines.append(f"- raw_exact_match_rate: {summary['raw_exact_match_rate']:.3f}")
    lines.append(
        "- contradiction_detection_rate: "
        f"must={summary['contradiction_detection_rate']['policy_must']:.3f}, "
        f"may={summary['contradiction_detection_rate']['policy_may']:.3f}, "
        f"binary_strict={summary['contradiction_detection_rate']['binary_strict']:.3f}"
    )
    lines.append(
        "- false_contradiction_rate_on_non_contradiction: "
        f"must={summary['false_contradiction_rate_on_non_contradiction']['policy_must']:.3f}, "
        f"may={summary['false_contradiction_rate_on_non_contradiction']['policy_may']:.3f}, "
        f"binary_strict={summary['false_contradiction_rate_on_non_contradiction']['binary_strict']:.3f}"
    )
    lines.append(
        "- uncertainty_collapse_rate: "
        f"must={summary['uncertainty_collapse_rate']['policy_must']:.3f}, "
        f"may={summary['uncertainty_collapse_rate']['policy_may']:.3f}, "
        f"binary_strict={summary['uncertainty_collapse_rate']['binary_strict']:.3f}"
    )
    lines.append("")
    lines.append("## Scenario Table")
    lines.append("| project | scenario | expected(raw) | raw | must | may | binary_strict |")
    lines.append("|---|---|---|---|---|---|---|")
    for r in rows:
        lines.append(
            f"| {r.project} | {r.scenario_id} | {r.expectation_raw} | {r.raw_judgement} | "
            f"{r.policy_must} | {r.policy_may} | {r.binary_strict} |"
        )
    lines.append("")
    lines.append("## Interpretation")
    lines.append("- `policy_must` prioritizes contradiction signaling on uncertain inputs.")
    lines.append("- `policy_may` avoids contradiction escalation on uncertain inputs.")
    lines.append("- `binary_strict` is a fail-closed baseline that conflates uncertainty with contradiction.")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Evaluate policy/baseline ablations on fixed replay artifacts.")
    parser.add_argument(
        "--offline-lock",
        type=Path,
        default=Path("external_validation_sources.lock.json"),
        help="Offline lock file for deterministic artifact loading.",
    )
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path("logs/policy_ablation_report.json"),
        help="Output JSON report path.",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=Path("logs/policy_ablation_report.md"),
        help="Output Markdown report path.",
    )
    args = parser.parse_args()

    base = run(args.offline_lock, "none", "may")

    scenarios: list[Scenario] = []
    for rr in base["real_results"]:
        artifacts = rr["artifacts"]
        scenarios.extend(
            mk_scenarios(
                rr["project"],
                to_layer(artifacts["requirement"]),
                to_layer(artifacts["api"]),
                to_layer(artifacts["code"]),
            )
        )

    rows = evaluate(scenarios)
    summary = aggregate(rows)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "summary": summary,
        "rows": [r.__dict__ for r in rows],
        "source": {
            "offline_lock": str(args.offline_lock),
            "n_projects": len(base["real_results"]),
            "n_scenarios": len(rows),
        },
    }
    args.out_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    args.out_md.write_text(to_markdown(rows, summary), encoding="utf-8")

    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
