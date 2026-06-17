# Round 74 Summary (Formal Paper)

Target venues used in review prompts:
- FM / ITP / CPP / TACAS / FASE / Formal Aspects

Reviewer outcomes:
1. Reviewer1: **Major Revision**
2. Reviewer2: **Minor Revision**
3. Reviewer3: **Minor Revision**

Status:
- Mechanization integrity and reproducibility packaging are consistently rated strong.
- Remaining blocker is novelty/framing strictness from Reviewer1.

Converged strengths across 3 reviewers:
1. assumption-audited theorem interfaces (`hproj`, `hA`, `hcomm`) are clear and useful.
2. counterexample-backed boundaries are recognized as substantive.
3. axiom disclosure and theorem traceability are above typical submissions.

Open blockers after round74:
1. sharpen novelty statement from "combination-level packaging" to a venue-legible contribution claim (or explicitly position as methodology/infrastructure paper).
2. strengthen definition-level comparison with baseline theorem libraries (Mathlib-style APIs) beyond prose.
3. keep role-accounting and traceability category assignments explicit (`UAndOn_subset_UAndMayOn`, `consistent_transport_left` placement).

Notes:
1. Reviewer3 flagged manifest SHA length as 63 chars; local verification shows the value is 64 hex chars and script check passes.
2. `reproduce_formal.sh` now passes end-to-end and validates hash/build/theorem/sorry/LOC checks.
