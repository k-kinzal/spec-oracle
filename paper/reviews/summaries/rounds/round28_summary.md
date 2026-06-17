# Round 28 Reviewer Summary

- Date: 2026-02-15
- Scope:
  - `paper/manuscript/uadf_u0_spec_proof.md`
  - `paper/case-study/real_projects/external_validation.py`
  - `paper/case-study/real_projects/external_validation_results.json`
- Subagent method: `claude -p` via `claude_p_subagent.py`

## Verdicts

- Reviewer 1 (`paper/reviews/reviewer1_round28.md`): `VERDICT: OK`
- Reviewer 2 (`paper/reviews/reviewer2_round28.md`): `VERDICT: OK`
- Reviewer 3 (`paper/reviews/reviewer3_round28.md`): `VERDICT: OK`

## What Was Confirmed as Resolved

1. `U0` evaluation is now informative (coverage count/ratio/support layers and mutation-time coverage deltas), not only boolean membership.
2. Three-valued raw judgement (`consistent/contradictory/inconclusive`) is separated from policy projection (`policy_judgement`) in both manuscript and implementation.
3. Mutation evaluation now uses expectation-defined criteria per mutation type, including explicit detection basis for change-oriented mutations.

## Remaining Notes (Minor, Non-blocking)

- Minor wording polish for `U0` terminology (baseline/envelope emphasis).
- Optional presentation table to show `judgement -> policy_judgement` flow.
- Optional stronger pointering in §6.x for quick reviewer navigation.
