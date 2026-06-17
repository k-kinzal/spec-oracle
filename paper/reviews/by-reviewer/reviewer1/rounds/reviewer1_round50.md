# Reviewer 1 Round 50

- Role: Reviewer 1 (Formal Methods / Mechanization)
- Recommendation: Accept
- Pass Gate: true

## Summary
This manuscript presents a rigorous mechanization of the UAD/f model's U0/U∧ dual-operator kernel with exceptional attention to assumption boundaries and reproducibility. The Lean4 formalization is complete, well-structured, and successfully separates theoretical claims from engineering demonstration. The deterministic replay protocol for extraction pipelines (RQ6) is properly scoped as feasibility demonstration rather than statistical validation. All major theorems are mechanically verified with explicit assumption tracking, and the non-goals are clearly delineated to prevent overclaiming.

## Strengths
- Complete Lean4 mechanization (59 theorems, 1502 LOC) with reproducible build infrastructure including manifest SHA256 hashing
- Rigorous assumption tracking: all仮定 (hproj, hA, hSound, hComplete, UStar, hNecessaryOnDom) are explicitly typed and passed as proof parameters
- Clear separation of U0 (join/coverage baseline) and U∧ (meet/simultaneous satisfaction) resolves operational ambiguity in multi-layer governance
- One-sided adequacy decomposition (sound/complete) provides actionable engineering guidance for extractor requirements without false equivalence claims
- Non-random-adjoint theorem (§4.4) exposes subtle partiality implications that would be missed in informal treatment
- Deterministic replay protocol (source-lock + snapshot + SHA256) achieves technical reproducibility for n=3 PoC without statistical overclaiming
- Explicit Non-goals section (§0.3) prevents common mechanization pitfalls: no claim of general-domain validity, no extractor soundness proof, no operational readiness assertion
- Must/may semantics formalized with monotonicity proofs (UAndOn_subset_UAndMayOn) and operational policy separation

## Required Fixes
- None

## Optional Fixes
- Consider adding a Coq comparison appendix since Galois connection literature often uses Coq (low priority given self-contained presentation)
- The D(i) separation motivation (§2.1) could benefit from a counterexample showing what breaks without it (minor clarification)
- Extraction pattern table (§6.2, external_validation_results.json) could inline 1-2 examples directly in manuscript for readers without JSON access

## Evidence Quote
- "§4.3: "重要（適用境界）: 本節の adequacy 定理は抽象関係 E に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について hSound / hComplete が成り立つことを**別途証明**する必要がある。" — This level of boundary precision is exemplary for mechanized work."
