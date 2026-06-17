# Reviewer 1 Round 47

- Role: Reviewer 1 (Formal Methods / Mechanization Correctness)
- Recommendation: Accept
- Pass Gate: true

## Summary
This manuscript presents a mechanized UAD/f kernel for multi-layer specification governance through reverse-mapping. The formal development is solid: 59 theorems in Lean4 (1502 LOC) establish typed definitions, join/meet separation, one-sided adequacy decomposition, and partial-projection non-adjointness. The work explicitly bounds its claims—RQ1-5 target theory (model definitions, transfer conditions, adequacy), RQ6 targets deterministic replay feasibility (n=3 PoC). The §0.3 Non-goals and §6.2 interpretation boundaries are unusually careful. Theorem-to-claim alignment is maintained throughout: §4 theorems carry explicit assumption parameters (hproj, hSound, hComplete), §6 PoC separates "technical replay" from "extractor soundness proof," and mutation expectations are pre-fixed rather than post-hoc. The mechanization reveals non-trivial design choices (§5): two-operator separation, same-point connection assumptions, one-sided adequacy, and adjoint failure under partiality. Notation is self-contained (§2.1 table), and the Lean-to-text correspondence table (§7.6) enables verification. The deterministic replay protocol (§7.5) with SHA256 lock and jq-based checklist is reproducible. Within its stated scope (interval-domain reverse-mapping kernel, not general behavioral-spec management), this is acceptance-ready formal work.

## Strengths
- Mechanization discipline: 59 theorems in Lean4 with explicit assumption parameters (hproj, hSound, hComplete) prevent hidden dependencies
- Boundary discipline: §0.3 Non-goals, §4.8 application-boundary table, and §6.2 PoC interpretation clearly separate 'theory proven' from 'practice demonstrated'
- Non-trivial formalization insights: §5 design judgments (join/meet separation, same-point connection, one-sided adequacy, partial-projection non-adjointness) expose tacit assumptions
- Reproducibility engineering: §7.5 deterministic replay with SHA256 lock, jq checklist, and offline snapshot bundle enables third-party verification
- Theorem-claim alignment: RQ1-5 map to specific Lean theorems (§7.6 table), RQ6 targets replay not extractor-soundness, mutation expectations pre-fixed (§6.2 table)
- Self-contained definitions: §2 provides typed UAD/f model with notation table (§2.1), proj/extract separation (§2.6), and NL/IR boundary (§2.7)
- Assumption transparency: §3.5 ideal-root relation explicitly labeled as 'assumption-dependent theorem' not 'derived claim', §4.1 transfer requires same-point connection
- Operational semantics: must/may (§4.7) and tri-valued judgement (§6.2) formalized with inclusion theorems and policy-projection rules

## Required Fixes
- None

## Optional Fixes
- Consider adding a 'theorem dependency graph' figure to visualize assumption flow (e.g., hproj+hA→lifted_transfer→U0_coverage)
- §2.6 proj-decomposition could benefit from a commutative diagram (obs∘extract vs proj)
- §6.2 mutation table: consider adding a 'detection_mechanism' column to clarify why each expectation holds (e.g., 'interval_intersection' vs 'upper_threshold')
- §7.6 correspondence table: consider adding 'assumption parameters' column to highlight which theorems carry explicit dependencies

## Evidence Quote
- "本稿の主たる貢献は、UAD/f 最小コアの参照 mechanization を通じて、必要仮定を明示化した点にある。以下は本稿が初出の数学的主張であることを意図せず、UAD/f 文脈での実装可能な設計判断として提示する。... 判断2: 伝播定理には同一点連結仮定が必要。`R` だけでは不十分で、`proj_j x` と `proj_i x` を同じ root 点 `x` で結ぶ仮定（`hproj`）が必要であることが分かった。この仮定が破れる場合、`lifted(j) ⊆ lifted(i)` の全域主張は一般に得られない。"
