# Reviewer 2 (Empirical Evaluation) — Round 36

## Recommendation
Minor Revision

## Pass Gate
true

## Verified Improvements
- Offline snapshot replay with source lock is reproducible.
- Mutation framework and expectations are explicit (`6/6` detected).
- Layer-wise support/unknown/invalid observability is in place.
- Unknown handling is explicit via policy judgement and semantics.

## Required Fixes
- Strengthen wording that `n=3` is proof-of-concept and not statistical generalization.
- Clarify interpretation of `avg_support_ratio` / `avg_unknown_ratio` as extraction completeness metrics.
- Make mutation rationale wording more explicit (stale-bound drift, unit confusion).
- Re-state regex extraction brittleness as a practical limitation.

## Summary
Empirical design is sound for feasibility scope; remaining items are framing clarifications.
