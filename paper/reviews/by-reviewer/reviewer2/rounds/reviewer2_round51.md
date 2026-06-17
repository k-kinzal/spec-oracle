# Reviewer 2 Round 51

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This manuscript presents a mechanized UAD/f core for multi-layer specification governance with Lean4 formalization and a preliminary PoC on interval-based constraint extraction. The SE/RE contribution lies in making explicit the assumptions needed for layer-crossing comparison (projection partiality, adequacy decomposition, must/may semantics) and demonstrating technical feasibility with source-locked reproducibility. The scope is appropriately bounded to numeric boundary constraints, the claims are conservative, and the PoC is correctly positioned as a feasibility demonstration rather than external validation. Minor revisions are needed to strengthen operational semantics documentation and clarify the gap between abstract adequacy theorems and concrete extractor instantiation.

## Strengths
- Explicit assumption tracking: The formalization surfaces hidden assumptions (same-point connection in §4.1, adequacy one-sidedness in §4.3, partiality breaking adjoints in §4.4) that are often implicit in multi-layer governance proposals. This is valuable for SE research reproducibility.
- Scope discipline: §0.3 Non-goals, §6.2 PoC boundaries, and §9 limitations are clearly stated. The manuscript does not overclaim from n=3 convenience sample to statistical generalization, correctly positions the work as 'preliminary feasibility demonstration', and explicitly separates RQ5 (theory) from RQ6 (practice).
- Reproducibility infrastructure: Source-lock with SHA256, offline replay mode, deterministic comparison defined as structural JSON equality on 4 fixed fields (§7.5), and mutation expectations pre-fixed before execution. This is stronger than typical SE PoC reporting.
- Operational semantics separation: The tri-state layer status (supported/invalid/unknown) + tri-valued judgement (consistent/contradictory/inconclusive) + policy projection (must/may) design makes failure modes observable rather than hidden. The distinction between 'invalid' (ill-formed interval) and 'contradictory' (intersection failure) prevents semantic conflation.
- Theory-practice linkage transparency: §4.8 explicitly documents which theorems have verified PoC instantiation vs which remain at abstract level. The manuscript does not claim to have 'applied' adequacy theorems to regex extractors without proving extractor soundness/completeness.

## Required Fixes
- §6.2 should add a forward reference to the operational semantics definitions (classify_uand, apply_none_policy) either as pseudocode in an appendix or as a pointer to the implementation. Currently the reader must infer the tri-valued logic from log outputs and scattered prose.
- §4.3 adequacy theorems state 'abstract relation E' but the connection to 'regex extractor E_regex' is only mentioned negatively (Non-goals). Add a subsection or paragraph outlining what additional proof obligations would be needed to instantiate E for a concrete extractor (e.g., 'For regex r, proving hSound requires showing r.match(doc) implies semantic_constraint holds'). This clarifies the theory-practice gap without claiming to have closed it.
- §6.3 'Results and interpretation' lists many points but lacks a summary sentence of the form: 'The PoC succeeds in demonstrating X (RQ6) but does not demonstrate Y (out of scope)'. Recommend adding a 2-sentence summary at the start of §6.3 for reader orientation.

## Optional Fixes
- §2.7 NL→IR entry point: The IR schema example is helpful, but consider adding a sentence on how 'condition' and 'exception' fields (currently shown as String?) would integrate with the interval-domain formalization. Are they metadata only, or do they affect lifted(i) membership?
- §6.2 mutation rationale: The two mutation families are briefly justified, but adding a sentence on why these two (boundary reversal + unit confusion) were chosen over other fault classes (e.g., off-by-one, sign errors) would strengthen the experimental design transparency.
- §7.6 table could add a column indicating which theorems have concrete PoC instantiation (e.g., §6.1.1 for preimage_compose) vs which remain abstract. This would make the theory-practice linkage map more scannable.
- Terminology consistency: 'extraction mode' (§6.2) vs 'extractor' (§2.6) vs 'extract_i' (§2.6 item 2) are used inconsistently. A glossary or consistent naming convention would reduce cognitive load.
- Future work: The conclusion mentions 'integration with CI/CD' but does not discuss how the tri-state outputs would map to pass/fail gates. A sentence or two on operational decision rules (e.g., 'unknown > threshold → manual review') would help practitioners assess adoption barriers.

## Evidence Quote
- 本稿の実証主張は「interval-domain における reverse-mapping（部分射影が誘導する逆像）カーネルの実行可能性」に限定し、一般ドメインでの有効性・網羅性は主張しない。(§0.3) ... 本節の評価は preliminary feasibility demonstration であり、外的妥当性の統計主張を行わない。(§6.2)
