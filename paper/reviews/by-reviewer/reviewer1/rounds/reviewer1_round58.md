# Reviewer 1 Round 58

- Role: Formal Methods Reviewer (Round 58)
- Recommendation: Accept
- Pass Gate: true

## Summary
After a strict formal re-review post round-57 fixes, no blocking formal issue remains. The manuscript maintains rigorous separation between (a) abstract model definitions, (b) one-sided adequacy theorems, and (c) PoC empirical claims. All previously identified regression-risk areas—adequacy warning scope, must/may ordering, and PoC non-applicability disclosures—remain correctly guarded. The key formal vocabulary (join=∪, meet=∩ under inclusion order), the preimage definition, the UAndOn antitone theorem, the non-adjoint theorem, and the ideal-root conditioned inclusions are all stated with explicit hypotheses and are consistent with the Lean mechanization citations. No new formal regressions are introduced by the current version.

## Strengths
- Adequacy definitions (§4.3) correctly decompose proj_i(x)=some(y)↔E(x,y) into one-sided inclusions (sound/complete) with explicit Lean theorem names, and the double-sided equality theorem is stated as a consequence—not as a primitive—avoiding the conflation error from earlier rounds.
- The ordering convention is fixed once in §2.3 (inclusion order ⊆ only; join=∪, meet=∩) and then used consistently throughout §3, §4, and the antitone statement for UAndOn, eliminating the lattice-vocabulary ambiguity flagged in prior rounds.
- The must/may duality in §4.7 is formally clean: UAndOn ⊆ UAndMayOn and UAndMayOn_empty_implies_UAndOn_empty are stated in the correct direction, the none-branch in semanticPullbackMay is correctly flagged as E-independent, and the cross-comparison warning (must vs must, may vs may) is explicit.
- The PoC non-applicability disclosure in §4.3 ('CAUTION: PoC non-application') and §4.8 table are consistent: all adequacy theorems are marked 'unverified in PoC', and §6.2 explicitly states that classify_uand↔UAndOn equivalence is not claimed.
- The ideal-root inclusions in §3.5 are correctly conditioned on hNecessaryOnDom (U*∩Dom_i ⊆ lifted(i)) rather than the unconditional U*⊆lifted(i), and Lean file IdealRoot.lean is cited for both the conditioned and the idealised-strong-assumption variants—making the hypothesis dependency transparent.
- The MUS definition in §3.4 correctly uses a strict subset relation (active'⊊active) and scopes finiteness to {i // active i}, avoiding the undecidability trap for infinite index sets.
- non-adjoint theorem (§4.4) is stated with the correct antecedent (∃x0, proj_i(x0)=none) and is cited to RelatedWork/Galois.lean, correctly scoping the result to the partial-projection setting without over-generalising.

## Required Fixes
- (none)

## Optional Fixes
- §6.2 mutation table row for 'zlib unit_mismatch_upper_scale_down_1024' shows mutated_intersection as [-1, 0] (lower=-1, upper=0) but the criterion states 'upper' ≤ floor(upper/1024)'. Since the baseline zlib upper is 9, floor(9/1024)=0, upper'=0 satisfies the criterion. However the lower=-1 originates from the baseline lower (-1), not from the mutation, which may confuse readers. A footnote clarifying that the lower boundary is unchanged by this mutation type would help.
- §3.3 states 'consistent_iff_exists_UAndOn_pair' as a theorem name but the body defines Consistent(i,j) via a direct ∃x formula. For round-59 readability, it would be helpful to add a one-line note confirming that the Lean statement is definitional unfolding plus the non-emptiness witness, not an additional axiom.
- §7.4 theorem count (59) and LOC (1502 for UadfU0, 1538 total) should be re-verified against the committed Lean tree if any files were added after the round-57 recount; the numbers are internally consistent but a re-run of the stated measurement commands before camera-ready would eliminate any stale-count risk.

## Evidence Quote
- "重要（適用境界）: 本節の adequacy 定理は抽象関係 E に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について hSound / hComplete が成り立つことを別途証明する必要がある。警告（PoC非適用）: 下記の運用帰結は hSound / hComplete が成立する場合に限る。§6 の regex 抽出器について本稿はこれを証明しておらず、PoC結果へ直接適用しない（§0.3, §4.8）。"
