# Reviewer 2 Round 54

- Role: SE/RE Reviewer #2 — Readability, Scope Control, and Theory-Practice Boundaries
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The manuscript has addressed most of the structural concerns raised in prior rounds. The separation of U0 (join/OR) from U∧ (meet/AND), the explicit Non-goals section, the layered must/may interpretation with a three-value judgement pipeline, the adequacy one-sided decomposition (RQ5), and the machine-verified Lean proofs are all now clearly articulated. The PoC scope is well-bounded as a "preliminary feasibility demonstration" with n=3 convenience sample caveats stated repeatedly. The theory-practice boundary is more explicit than in prior rounds. The paper is conditionally ready for acceptance after a small set of targeted fixes, primarily to reduce internal redundancy and close two remaining clarity gaps.

## Strengths
- Clear binary separation of U0 (join) and U∧ (meet) in §3 with corresponding Lean identifiers; the prior confusion between 'integrated specification' and 'simultaneous satisfaction' appears resolved.
- Non-goals section (§0.3) is now crisp and machine-readable, explicitly excluding statistical generalization, non-interval domains, extractor soundness proofs, and operational deployment readiness.
- The must/may split is formalized both in theory (§4.7, preimage vs preimageMay) and operationally (policy_judgement pipeline table), closing the prior gap on how 'none' propagates.
- RQ5 adequacy theorems are cleanly separated into one-sided inclusions (hSound / hComplete) with an explicit proof-obligation template for connecting concrete extractors; the boundary 'applies to abstract E, not to the regex extractor' is called out in a bold warning block.
- The mutation detection table (§6.2) lists exact criteria per mutation per project, making the feasibility claim falsifiable and reproducible. The SHA256-locked reproduce.sh closes the deterministic-replay requirement.
- §4.8 theory-application table explicitly maps each theorem to its required assumptions and states PoC verification status, directly addressing the prior concern about overclaiming theoretical results.
- The negative example (§6.4 regex drift) is concrete and implementation-grounded, not a hypothetical; it correctly shows that the graceful+must/may policy choice matters and gives actual log references.
- Section 5 design decisions are presented as engineering observations, not novel mathematical claims, which is an appropriate epistemic posture for mechanization-derived insights.

## Required Fixes
- REDUNDANCY: The must/may operational implications are stated at least four times across §3.3, §4.3, §4.7, and §6.2. The §4.7 block in particular contains the full 'error-direction' table, then the §4.3 'operational consequences' block repeats essentially the same content. Consolidate: state the canonical error-direction implications once in §4.7 and cross-reference from §4.3 rather than duplicating.
- SCOPE BLEED IN §6.2: The PoC section contains two long normative subsections ('PoC における must/may membership 近似' and 'U0 理論定義と PoC 指標の区別') that mix formal notation with implementation detail at a level of granularity that belongs in an appendix. The body of §6.2 should give the high-level mapping table and forward the reader to an appendix for the operational analogue definitions. This is the single largest readability obstacle remaining.
- UNDEFINED TERM INTRODUCED LATE: The term 'measure_i^{U∧}' (§6.2, PoC layer state definition) is introduced without a forward declaration in §2. The notation table in §2.1 should include a row for this PoC-specific symbol, or the symbol should be renamed to avoid confusion with the abstract model symbols.
- LEAN FILE PATH CONSISTENCY: §7.4 lists 'paper/lean/UadfU0/InterLayer/Adequacy.lean' but §4.3 refers to 'InterLayer/Adequacy.lean' without the full path prefix. While inferrable, all Lean paths should use one canonical form throughout (preferably relative to the repo root, as done in §7.4).

## Optional Fixes
- The opening sentence of §0.1 ('本稿が対象とする問題は、多層防御における層横断比較基準の欠如である') is strong and clear, but the motivation paragraph that follows (items 1-3) re-states what §0.3 Non-goals already addresses from the negative side. Consider trimming the overlap to ~2 sentences.
- §3.5 ('理想根 U* との関係') contains a long chain of subset relations that are stated in prose, then in math notation, then referenced in Lean. The prose and math duplicate each other; retaining the math + Lean reference and cutting the prose paraphrase would shorten the section without loss of content.
- The 'operational choice guide' table at the end of §4.7 (偽陽性/偽陰性の基準) lists four quadrants. Consider promoting this table to §3 and referring back to it in §4.7 so that readers encounter the operational framing before the formal details.
- §6.5 threats-to-validity lists six items. Item 6 ('表現力の制約') regarding non-contiguous sets like powers-of-two is the most substantive limitation not covered elsewhere and deserves one additional sentence explaining what class of constraints is excluded.

## Evidence Quote
- "本稿の既定意味論は must（`none` は除外）であり、may 変種は感度分析として §4.7 に分離して扱う。" (§3.3) — This sentence correctly defers the full must/may treatment, but §4.3 then re-expands it with a duplicate error-direction table, creating the primary redundancy issue flagged as required fix #1.
