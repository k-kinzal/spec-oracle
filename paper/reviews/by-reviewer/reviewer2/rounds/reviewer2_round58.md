# Reviewer 2 Round 58

- Role: Senior Reviewer — Formal Methods / Requirements Engineering track, SE/RE venue
- Recommendation: Accept
- Pass Gate: true

## Summary
The three previously-identified publication blockers have been adequately resolved. (1) Heterogeneous mutation criteria are now explicitly disaggregated: the "6 out of 6" headline is accompanied by the breakdown "uand_contradiction 3件 + bound_shrinkage 3件", with a table-level note clarifying that the two criteria are not equivalent (uand_contradiction maps to U∧ judgment directly; bound_shrinkage is an operational metric). (2) The adequacy-theorem applicability warnings (§4.3 "重要（適用境界）" and "警告（PoC非適用）") are now placed before the theorem statements and before §6.2 results, so a reader encounters the scope fence before the formal results. §4.8 consolidates the mapping of every theorem group against PoC verification status. (3) The U0_support ↔ U0 relationship is now explicitly characterised as a definitional equivalence under the stated PoC instantiation (Ω:=Ω_art, β_i:=ℤ×ℤ, proj_i:=interval_hat_i, A_i:={(l,u)|l≤u}), not as an independent theorem, with a qualifying sentence "本稿の PoC における U0 観測主張は上記 instantiation に限定する". Non-goals are comprehensively listed in §0.3 and repeated at appropriate entry points in §6.2. The paper remains over-long but is self-consistent, and the claim scopes are appropriately delimited for a formal-methods / RE venue.

## Strengths
- Prior blocker 1 resolved: mutation detection headline (6/6) is now decomposed into two distinct criterion types (uand_contradiction vs bound_shrinkage) in both the summary table and the narrative, with an explicit note that expectation_satisfied=true does not always imply raw_judgement=contradictory.
- Prior blocker 2 resolved: adequacy applicability warnings appear at the top of §4.3 before theorem statements, and §4.8 provides a structured table mapping each theorem group to its required hypotheses and PoC verification status, giving reviewers a clear audit trail.
- Prior blocker 3 resolved: U0_support ↔ U0 is explicitly characterised as a definitional consequence of the PoC instantiation parameters, not an independently proved theorem, with the limiting qualifier clearly stated in §6.2.
- Non-goals enumerated in §0.3 are substantive and specific (no statistical generalisation, no soundness/completeness proof for regex extractor, no operational readiness claim), and are cross-referenced at the right entry points in §6.2 and §4.3.
- The three-valued judgement pipeline (judgement → policy_judgement under must/may) is cleanly separated from the U0 coverage indicators (support/unknown/invalid), resolving the earlier semantic conflation.
- The must/may duality is now handled at both the theory level (preimageMay, UAndMayOn) and the PoC level (none_semantics flag), with the relationship UAndOn ⊆ UAndMayOn machine-verified in Lean.
- Lean mechanisation scope (59 theorems, 1502 LOC, zero mathlib dependency) is quantified with reproducible measurement commands.

## Required Fixes
- (none)

## Optional Fixes
- §6.2 table note for bound_shrinkage: the zlib row shows mutated_intersection [-1, 0] satisfying upper' <= 0 as true, but -1 is the lower bound and 0 is the upper bound — a brief parenthetical clarifying which endpoint is being compared to floor(upper/1024) would prevent reader confusion (the text implies upper'=0 ≤ floor(9/1024)=0, which holds, but the notation is ambiguous at first read).
- §3.4 MUS definition: the finiteness assumption (Fintype {i // active i}) is stated in prose but not reflected in the Lean file references listed; a brief note confirming whether this is axiom-free or uses a Fintype instance in Lean would help readers assessing the mechanisation.
- §4.7 operational policy table: the column headers 'sound 側' and 'complete 側' refer to the extractor adequacy assumptions (hSound/hComplete), but a reader who has not fully absorbed §4.3 might conflate these with must/may semantics — a one-line disambiguating footnote would help.
- The manuscript is unusually long for a research paper; the camera-ready version should consider moving §12 appendices and the detailed PoC ratio definitions to supplementary material or an extended version, leaving the main body at a more typical page count.

## Evidence Quote
- "内訳は `uand_contradiction` 3件 + `bound_shrinkage` 3件であり、前者は `U∧` 判定に直接結びつく一方、後者は運用メトリクス（交差上限縮退）による検出である。" (§6.2 デモ実行結果) — directly resolves blocker 1. "**重要（適用境界）**: 本節の adequacy 定理は抽象関係 `E` に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について `hSound` / `hComplete` が成り立つことを**別途証明**する必要がある。" and "**警告（PoC非適用）**: 下記の運用帰結は `hSound` / `hComplete` が成立する場合に限る。§6 の regex 抽出器について本稿はこれを証明しておらず、PoC結果へ直接適用しない" (§4.3, appearing before theorem statements) — directly resolves blocker 2. "本稿の PoC における `U0` 観測主張は上記 instantiation に限定する。抽出器一般（regex/LLM全般）で `U0_support ↔ U0` が常に成り立つことは主張しない。" (§6.2) and "本稿の `U0_support ↔ U0` はこの定義展開に基づく同値であり、独立の追加定理ではない。" (§6.2) — directly resolves blocker 3."
