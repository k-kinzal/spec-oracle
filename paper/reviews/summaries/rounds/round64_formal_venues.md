# Round 64 Review Summary (Formal Venues)

## Review setup
- Target venues were explicitly specified:
  - FM / ITP / CPP / TACAS / FASE / Formal Aspects
- Review objective was explicitly specified:
  - "Review for acceptance at those venues"
- Constraint in prompt:
  - no extra assumptions beyond provided materials

Reviewer outputs:
- `paper/reviews/by-reviewer/reviewer1/rounds/reviewer1_round64.md`
- `paper/reviews/by-reviewer/reviewer2/rounds/reviewer2_round64.md`
- `paper/reviews/by-reviewer/reviewer3/rounds/reviewer3_round64.md`

## Recommendations
- Reviewer 1: Major Revision
- Reviewer 2: Major Revision
- Reviewer 3: Major Revision

## Common MUST-level findings
1. `UStar` formal definition is missing in the manuscript text.
2. `M.Ui` appears in theorem signatures but is not explicitly defined in the manuscript narrative.
3. Mechanization reproducibility is judged insufficient at submission text level (reviewers requested directly verifiable Lean artifact package declaration).

## Repeated SHOULD findings
1. Adequacy section should sharpen semantic role of `E` and concretization boundaries.
2. Related-work delta against mechanized Galois/Mathlib lines should be more explicit.
3. RQ role separation (`RQ1/RQ2` vs primary RQs) should be made structurally clearer.

## MINOR patterns
1. Notation consistency (`A` vs `Ui`) in text.
2. Bibliography detail level for FM readers.
3. Cross-reference tightening between theorem catalog and main text.
