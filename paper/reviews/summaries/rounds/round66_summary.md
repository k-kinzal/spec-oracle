# Round 66 Summary (Formal Venues)

Date: 2026-02-18
Target venues: FM / ITP / CPP / TACAS / FASE / Formal Aspects

## Reviewer decisions
- Reviewer 1: Major Revision
- Reviewer 2: Major Revision (artifact-conditional)
- Reviewer 3: Weak Accept / Conditional Accept

## Consensus signal
- Overall: Borderline, still below strong-accept confidence for strict FM tracks.
- Positive trend: definition clarity, assumption boundary, and mechanization structure are recognized.
- Blocking risk: novelty positioning and RQ-to-theorem traceability are still judged insufficiently explicit by at least two reviewers.

## Recurring major concerns
1. Novelty positioning is under-argued versus existing formalization lines (Mathlib/Coq-style set-theoretic kernels, BX/institution comparisons).
2. RQ mapping is not explicit enough at theorem granularity (which theorem answers which RQ).
3. Artifact trust language can still be read as unverifiable when only manuscript appendices are reviewed.
4. Role-separation result (`U0` vs `UAnd`) is present but not foregrounded as a main theorem-level contribution.

## Required edits before next round
1. Add an explicit RQ-to-theorem matrix in the main manuscript (section-level and theorem-level mapping).
2. Strengthen novelty section with concrete “what existing libraries do not provide together” argument.
3. Promote role-separation edge-case implications (`UAndOn_empty_eq_univ`, active-set laws) as a central formal result.
4. Keep artifact claims strictly scoped to what is verifiable from provided package and scripts.

## Files generated in this round
- `paper/reviews/by-reviewer/reviewer1/rounds/reviewer1_round66.md`
- `paper/reviews/by-reviewer/reviewer2/rounds/reviewer2_round66.md`
- `paper/reviews/by-reviewer/reviewer3/rounds/reviewer3_round66.md`
