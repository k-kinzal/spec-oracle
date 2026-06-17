# Reviewer 1 Round 41

- Role: Formal Methods Acceptance Gate Reviewer (Round 41)
- Recommendation: Accept
- Pass Gate: true

## Summary
Round 41 submission demonstrates strong empirical validation of the U0 reverse-mapping framework with 3/3 real-world projects showing consistent specifications across requirement/API/code layers. The validation results clearly distinguish between 'invalid' (empty interval) and 'contradictory' (policy-level rejection) states with proper precedence rules. The PoC correctly implements U0_support as instantiation-limited observation where unknown≠falsified. Mutation testing (6/6 detected) confirms the framework's sensitivity to specification drift. The only limitation is the restricted scope to interval specifications, but this is explicitly acknowledged as a PoC boundary rather than a theoretical gap.

## Strengths
- Clear empirical evidence: 3/3 real projects (PostgreSQL, zlib, SQLite) achieve consistent U0 with avg 77.8% support ratio and 0% invalid intervals
- Correct invalid vs contradictory separation: 'invalid' = lower>upper at observation level; 'contradictory' = policy judgement that may include invalid intervals as evidence
- Proper precedence rule: contradiction detection uses raw interval invalidity as one signal, but final judgement remains policy-level
- Sound U0_support↔U0 instantiation model: unknown layers (code without lower bound) correctly yield may-membership=true without claiming must-membership
- Robust mutation testing: 6/6 injected defects detected (3 stale-requirement contradictions + 3 unit-mismatch changes), demonstrating practical falsifiability
- Complete offline-replay methodology: SHA256-locked snapshots eliminate network dependency and ensure reproducibility
- Proper admission of scope: PoC limited to interval specifications is explicitly stated, not hidden as universal claim

## Required Fixes
- None

## Optional Fixes
- Consider adding one architectural-level example (e.g., microservice contract) to demonstrate how interval-based U0 could compose with non-interval specifications in future work
- The dual observation naming (proj^U0 vs obs^U∧) could benefit from a brief glossary entry distinguishing projection (type-level functor) from observation (runtime witness extraction)
- Clarify whether 'unknown' semantics under none-policy means 'optimistic may-membership' or 'conservative exclusion from must-set' - current implementation uses optimistic interpretation which is sound but could be made more explicit
