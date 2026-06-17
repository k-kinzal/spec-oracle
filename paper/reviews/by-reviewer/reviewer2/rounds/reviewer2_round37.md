# Reviewer 2 Round 37

- Role: Software Engineering & Requirements Engineering Researcher
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The UAD/f framework addresses a genuine pain point in multi-layered specification governance through reverse mapping from artifacts to U0. The external validation (3/3 real projects consistent, 6/6 mutations detected) demonstrates proof-of-concept feasibility. However, the paper needs clearer articulation of (1) the specific problem scope vs. general specification challenges, (2) threat to validity regarding interval-only semantics, and (3) scalability claims. The core contribution—U0 as oracle for governing Test/Contract/Proof layers—is novel and practically valuable, but requires more explicit boundary statements about what UAD/f does NOT solve.

## Strengths
- Clear reverse-mapping philosophy: U0 constructed from artifacts rather than written by humans addresses real specification drift in practice
- Concrete external validation: PostgreSQL/zlib/SQLite cases show interval consistency checking works on real-world numeric constraints with mutation testing
- Honest limitations: acknowledges interval semantics limitation and positions as 'oracle for ambiguity' rather than complete formal verification

## Required Fixes
- Clarify problem scope: distinguish between 'multi-layer consistency governance' (claimed) vs. 'complete specification management' (not claimed). Current motivation may oversell generality—explicitly state UAD/f targets parameter constraints, not full behavioral specs
- Address validity threat: all 3 external cases are numeric intervals. Need explicit statement that structural/behavioral consistency (e.g., API contracts, state machines) remains future work to avoid reader misinterpretation of 'reverse mapping from Code/Tests/Docs'
- Quantify '荒め(coarse)' acceptable trade-off: provide concrete metric or example showing when interval-level U0 provides sufficient governance value vs. when finer-grained specs are needed

## Optional Fixes
- Add related work comparison: how does UAD/f relate to trace link maintenance (e.g., Hayes et al.) or consistency checking in product lines (e.g., feature models)? Position novelty more clearly
- Expand mutation testing rationale: explain why stale_requirement and unit_mismatch mutations specifically test the U0 oracle hypothesis vs. just testing interval arithmetic
- Discuss scalability: external validation uses 3 constraints—provide reasoning or pilot data on whether approach scales to 100s of constraints in a real system
