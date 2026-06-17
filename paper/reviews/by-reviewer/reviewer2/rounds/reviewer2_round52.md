# Reviewer 2 Round 52

- Role: Software Engineering / Requirements Reviewer (#2)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This manuscript presents a mechanized reverse-mapping framework (UAD/f with U0/U∧) for multi-layer specification governance. The work demonstrates strong technical rigor through Lean4 formalization and deterministic PoC replay. The revised text successfully addresses key boundary issues: RQ5/RQ6 separation is now explicit (theory vs. practice), operational semantics references are clearly marked, and the interpretation section distinguishes observability metrics from theoretical claims. However, minor clarifications are needed around: (1) the D(i) separation's practical demonstration gap, (2) mutation test coverage boundaries, and (3) the artifact bundle instantiation's generalization limits. The core contribution—making implicit assumptions explicit via mechanization—is valuable and well-executed.

## Strengths
- Explicit RQ5/RQ6 boundary: §4.3 clearly states adequacy theorems apply to abstract relation E, not concrete extractors; §6.2 limits claims to deterministic replay (RQ6 only)
- Operational semantics marking: §6.2 consistently uses 'operational analogue' terminology for classify_uand and measure functions, preventing confusion with theoretical U∧
- Three-valued logic separation: judgement (3-value) vs. policy_judgement (must/may projection) is formally defined with implementation correspondence table (§4.7)
- Non-goals discipline: §0.3 explicitly lists 8 non-goals including statistical generalization, non-interval domains, and extractor soundness proofs
- Artifact reproducibility: source-lock with SHA256, offline snapshots, and reproduce.sh provide deterministic replay infrastructure (§7.5)
- D(i) conceptual justification: §2.1 explains why separating D(i) from A(i) matters theoretically (domain vs. admissibility), even though PoC uses trivial D(i)
- Mutation test expectations: Pre-fixed expectation conditions (contradictory for stale, upper'≤floor(upper/1024) for unit mismatch) prevent post-hoc interpretation
- Assumption surfacing: §5 design judgments explicitly call out hproj, hSound/hComplete, and adjunction failure—core mechanization contribution

## Required Fixes
- Clarify D(i) demonstration gap: Add explicit statement in §6.2 that while D(i) separation is theoretically motivated (§2.1), current PoC uses D(i)=ℤ×ℤ (trivial) and defers unit normalization/inclusion/type-range constraints to future work. Currently buried in footnote.
- Bound mutation coverage: In §6.5 validity threats, explicitly state that 2-mutation design (stale + unit mismatch) tests boundary *algebra* behavior but does NOT cover: (a) inclusive/exclusive boundary interpretation, (b) implicit default values, (c) non-numeric constraint interactions. Currently says 'limited to 2 systems' but unclear on *what* is untested.
- ArtifactBundle generalization limit: In §6.1.1, add sentence clarifying that Ω=ArtifactBundle instantiation demonstrates obs/extract/proj decomposition for *snapshot-based* artifact collection, but does NOT validate the approach for: (a) streaming/trace-based Ω, (b) artifact versioning across time, (c) cross-artifact referential consistency. Currently reads as if it validates §2.6 generally.

## Optional Fixes
- Add forward reference in §2.1: When introducing D(i) separation, add '(PoC demonstration status: §6.2)' to help readers track theory-practice gap
- Consolidate must/may semantics: §4.7 table (operational policy), §6.2 implementation correspondence, and §7.5 reproduce.sh modes all define must/may slightly differently—consider unified reference table in appendix
- RQ5 proof obligation example: §4.3 lists minimal proof obligations for concrete extractors but doesn't show *attempted* application to regex extractor. Consider adding §6.2.1 'Why regex adequacy is deferred' subsection showing where proof would break (e.g., span ambiguity, unit inference)
- Mutation expectation rationale: §6.2 defines expectations but doesn't explain *why* these two were chosen. Brief note (e.g., 'stale tests temporal consistency; unit tests semantic interpretation') would strengthen internal validity narrative
- Unknown ratio interpretation guide: §6.3 says 'unknown is not failure' but doesn't give actionable threshold—add engineering guideline (e.g., 'unknown >50% suggests extractor redesign; <20% acceptable for monitoring')
- Lean LOC breakdown: §7.4 gives total LOC but readers may want ratio of 'proof vs. boilerplate'—consider adding effective proof density metric

## Evidence Quote
- **RQ5/RQ6 boundary (strength)**:
'重要（適用境界）: 本節の adequacy 定理は抽象関係 `E` に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について `hSound` / `hComplete` が成り立つことを**別途証明**する必要がある。' (§4.3)

'**重要（RQ5/RQ6境界）**: 本節は `RQ6 (practice)`（source-lock付き決定的再実行可能性）を対象とする。`RQ5 (theory)` の adequacy（§4.3）で使う抽象関係 `E` について、regex抽出器が意味保存性を満たすことは本節で証明していない。' (§6.2)

**Operational semantics marking (strength)**:
'`U∧` 判定（`judgement`）は `\widehat{interval}_i` ではなく `\widehat{bounds}_i`（部分境界）を入力に行う。[...] PoC の `U∧` は、同一 `Ω` 上で `lifted(i)` の meet を直接計算したものではなく、抽出制約（bounds）上の同時満足可能性を返す **operational analogue** として実装している。' (§6.2)

**D(i) gap (required fix)**:
'PoCでは `D(i)` を trivial（全体集合）に置き、`A(i)=\{(l,u)\mid l\le u\}` の整形式監査を行う。単位正規化・包含性・型域制約を `D(i)` に載せる実運用設計は将来課題とする。' (§6.2)
→ This is buried; needs upfront statement in §6.2 intro that PoC doesn't demonstrate D(i) practical utility yet.
