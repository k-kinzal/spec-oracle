# Reviewer 2 Round 47

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Accept
- Pass Gate: true

## Summary
This revision successfully addresses the core SE/RE concerns through systematic claim scoping, explicit assumption tracking, and transparent feasibility demonstration. The manuscript consistently separates theoretical contributions (mechanized UAD/f kernel with typed assumptions) from empirical claims (n=3 PoC for deterministic replay), avoiding statistical generalization. The three-valued judgement + policy projection design provides clear operational semantics for incomplete extractions. Non-goals are front-loaded and consistently enforced. Reproducibility infrastructure (source-lock, snapshots, SHA256 verification) meets publication standards. Minor residual risks exist around extractor soundness assumptions and mutation coverage, but these are appropriately disclosed as limitations rather than hidden.

## Strengths
- Explicit Non-goals section (§0.3) front-loads claim boundaries: no statistical generalization from n=3, no interval-domain generalization, no extractor soundness proof, no production-readiness claim
- Systematic separation of theory (RQ1-5: typed model + Lean proofs) from practice (RQ6: deterministic replay demo) with clear applicability boundaries in §4.8
- Three-valued judgement design (consistent/contradictory/inconclusive) + must/may policy projection provides interpretable operational semantics for extraction failures
- Deterministic replay infrastructure with SHA256 verification, source-lock, and snapshots enables third-party verification without claiming network-robustness
- Assumption tracking infrastructure: adequacy theorems (§4.3) explicitly separate abstract E-relation proofs from concrete extractor application, preventing soundness overclaim
- Mutation testing uses pre-fixed expectations (stale_requirement_lower, unit_mismatch_upper_scale_down_1024) with explicit detection criteria, avoiding post-hoc rationalization
- U0/U∧ separation (§3) with formal join/meet definitions prevents OR/AND conflation common in specification integration papers
- Transparent limitation disclosure: code.lower unknown in 2/3 cases attributed to regex implementation limits rather than claimed as semantic property
- Extraction pattern transparency: logs include regex patterns + matched fragments, enabling audit of what was actually extracted
- Theory-to-PoC connection explicitly documented as 'not applied' for extractor soundness (§6.2 repeated warnings), avoiding implication that Lean proofs cover regex layer

## Required Fixes
- None (manuscript meets acceptance threshold)

## Optional Fixes
- Consider adding brief forward reference in §0.1 to §6.4 negative example (regex drift) when first introducing extraction as PoC component - would strengthen failure-mode transparency
- §6.3 'what was learned' could explicitly state that 2/3 code.lower=null demonstrates feasibility of partial-observability handling rather than API semantic property (currently implied but not stated)
- Mutation coverage limitation (§6.5 point 4) could quantify how many additional mutation operators would be needed for 'adequate' boundary robustness claim - current framing is honest but leaves reader uncertain about gap size

## Evidence Quote
- "本稿の実証主張は「interval-domain における reverse-mapping（部分射影が誘導する逆像）カーネルの実行可能性」に限定し、一般ドメインでの有効性・網羅性は主張しない。... PoCにおける理論要素と PoC 要素の対応（§6.2）: ... したがって本節は `RQ6 (practice)` の実行可能性確認を対象とし、`RQ5 (theory)` の実抽出器適用（意味保存証明）は対象外である。"
