# Reviewer 1 Round 57

- Role: Formal Methods Reviewer (strict re-review after blocker fixes)
- Recommendation: Accept
- Pass Gate: true

## Summary
All four prior blockers have been adequately resolved. The manuscript now precisely delineates may-side adequacy none-branch semantics, correctly restricts U* claims to domain-intersected formulations, unambiguously states the antitone direction for UAndOn, and provides MUS with explicit finite-active side conditions. No formal acceptance blocker remains.

## Strengths
- May-side adequacy none-branch is now cleanly separated: §4.7 explicitly defines preimageMay with the none-branch as an E-independent operational convention ('none 分岐は E 非依存の運用規約'), and §4.3 warns that may-side comparison requires semanticPullbackMay to carry the same none rule—eliminating the prior asymmetric-branch ambiguity.
- U* restriction wording is precise: §3.5 introduces Dom_i and Dom_active and states 'U* ∩ Dom_i ⊆ lifted(i)' as the operative hypothesis, explicitly noting it is a weakening of the stronger 'U* ⊆ lifted(i)' and labeling it a proof-tracked assumption ('hNecessaryOnDom'), not a derived result. The stronger variants are separately flagged as 'ideal-case assumptions'.
- Antitone direction is unambiguous: §3.3 and §2.4 both state the direction with a concrete quantifier: '(∀ i, J i → K i) ⇒ UAndOn(K) ⊆ UAndOn(J)', and the prose gloss 'active を増やすと U∧ は反単調に小さくなる' is consistent with this formal statement. The Lean theorem UAndOn_antitone carries the matching hypothesis hJK.
- MUS side conditions are now fully specified: §3.4 defines strict-subset (active' ⊊ active) with explicit quantifiers, adds 'Fintype {i // active i}' as an operational finiteness assumption, excludes the degenerate single-layer case, and restricts MUS to a 'diagnostic specification' rather than claiming an algorithmic completeness result for the current mechanization.
- Claim boundaries are consistently enforced throughout: Non-goals (§0.3), the theorem-applicability table (§4.8), and PoC interpretation (§6.3) all cross-reference each other, preventing the theory-to-PoC over-reach that was a concern in earlier rounds.
- The adequacy warning box in §4.3 ('警告（PoC非適用）') explicitly blocks misreading of the one-sided inclusion results as applying to the regex extractor, which addresses the prior concern about implicit soundness/completeness claims for concrete extractors.

## Required Fixes
- (none)

## Optional Fixes
- §4.7 may-side prose: The sentence 'UAndOn ⊆ UAndMayOn より、must空判定は may より矛盾を出しやすい' is directionally correct but could be made sharper by noting that this is the contrapositive (if UAndMayOn is empty then UAndOn is empty) supplied by the theorem UAndMayOn_empty_implies_UAndOn_empty. A one-line cross-reference would help readers follow the logical direction without recomputing.
- §3.5 may-side U* inclusion: The may variant 'U* ⊆ U^{∧,may}_{active}' is stated with the hypothesis '∀ i, active(i) → U* ⊆ lifted^{may}(i)' but the Lean name for this theorem is not listed alongside the must-side names. Adding 'UStar_subset_UAndMayOn' to the Lean reference list in §3.5 would complete the correspondence table.
- §3.4 MUS: The finiteness caveat ('Fintype {i // active i}') is stated in prose but not reflected in the formal MUS definition block. A parenthetical '(under Fintype {i // active i})' after the MUS predicate would make the side condition machine-checkable at the definition site rather than only in surrounding prose.
- §6.2 PoC model correspondence table: The row for 'UAndOn (同一 Ω 上の meet)' maps to 'classify_uand (operational analogue)' but does not mention that the non-equivalence is formally stated ('∀x, classify_uand(...) ↔ x ∈ UAndOn の同値主張を行わない'). Adding a column 'equivalence claimed?' with explicit 'No (operational analogue)' vs. 'Yes (must instantiation)' would reduce reviewer confusion in future rounds.

## Evidence Quote
- "方向の明示: (∀ i, J(i)→K(i)) ⇒ UAndOn(K) ⊆ UAndOn(J)。\n\n注記: U* ∩ Dom_i ⊆ lifted(i) は論理的には U* ⊆ lifted(i) を Dom_i へ制限した弱い仮定である。一方、部分射影下で観測不能点を除外するという意味で工学的には適切な精密化である。すなわち本稿はこの仮定を導出したのでなく、UStar と hNecessaryOnDom を仮定引数として Lean 上で追跡可能にした。\n\nMUS の運用的意味づけは Fintype {i // active i}（または同等の有限性仮定）の下で解釈する。\n\nnone 分岐は E 非依存の運用規約であり、E は some 証人がある枝（∃y）にのみ関与する。"
