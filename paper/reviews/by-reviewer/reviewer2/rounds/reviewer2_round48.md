# Reviewer 2 Round 48

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This revision demonstrates **rigorous claim discipline** with explicit Non-goals (§0.3), theoretical boundaries (§4.8), and PoC interpretation guardrails (§6.2-6.3). The manuscript achieves mechanized theory for UAD/f reverse-mapping kernels (RQ1-5) and deterministic replay feasibility (RQ6) without overgeneralizing from n=3 convenience samples. The multi-layered scope boundaries—interval-domain only, no statistical inference, no extractor soundness proof, no production-readiness claim—are consistently enforced across all evaluation sections. Minor revisions needed to strengthen RQ5 boundary clarity and consolidate must/may operational semantics.

## Strengths
- **Claim scoping discipline**: Non-goals (§0.3) explicitly bound what is NOT claimed (no statistical generalization, no non-interval validity, no extractor proof, no production readiness). This prevents reader misinterpretation.
- **Theoretical boundaries enforced**: §4.8 table separates 'Lean-verified theory' from 'PoC-demonstrated feasibility', preventing conflation of formal results with empirical observations.
- **PoC interpretation guardrails**: §6.2 labels n=3 as 'convenience sample', 'preliminary feasibility demonstration', not external validation study. Success criteria explicitly defined as deterministic replay + tri-valued judgement stability, not unknown-ratio=0.
- **Reproducibility infrastructure**: SHA256-locked sources (§7.5), offline replay via snapshots, minimal verification checklist in README. Deterministic replay scope explicitly defined (4 fields only, not all metadata).
- **Must/may operationalization**: §4.7 and §6.2 distinguish raw judgement (tri-valued), policy projection (must/may), and observability metrics (support/unknown/invalid ratios). Table in §4.7 maps operational choices to risk profiles.
- **Negative case transparency**: §6.4 demonstrates regex drift failure using actual implementation vulnerabilities, not constructed examples. Logs show fail-fast vs graceful+must/may behavior differences.
- **RQ-theorem correspondence**: §7.6 table maps each RQ to specific Lean files/theorems, enabling independent verification of formal claims vs empirical claims.

## Required Fixes
- **RQ5 application boundary needs frontloading**: §4.3 adequacy theorems state 'Note: abstract E only' in prose, but RQ5 definition (§1) should explicitly say 'RQ5 scope: abstract adequacy relations; concrete extractor application requires separate soundness/completeness proofs (Non-goal in this paper)'. Current phrasing allows misreading that regex extractors are covered.
- **Must/may vocabulary consolidation**: §2.3 uses 'must semantics' for membership, §4.7 uses 'must interpretation' for none-handling, §6.2 uses 'must policy' for inconclusive projection. Recommend single term 'must policy' throughout with explicit definition: 'must policy = none excludes membership (§2.3) + inconclusive projects to contradictory (§4.7)'.
- **PoC success criteria need single-location definition**: Currently scattered across §6.2 prose, §6.3 bullets, and README. Consolidate into boxed definition in §6.2: 'PoC success := (i) SHA256-locked replay stability, (ii) tri-valued judgement determinism on 4 fields (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation), (iii) 6/6 mutation expectation satisfaction. Unknown>0 is observable outcome, not failure.'

## Optional Fixes
- **Mutation coverage discussion**: §6.3 states '2 mutation families' limits robustness claims. Consider brief discussion of what mutation families would be needed for inclusive/exclusive boundary testing (e.g., '≤ vs <' sensitivity) or implicit-default testing, to guide future work.
- **U0/U∧ observability gap**: §6.2 footnote distinguishes 'U0 theory (join on Ω)' vs 'U0_support_indicator (operational must)' vs 'U0_unfalsified (operational may)'. This is correct but dense. Consider small worked example: 'If requirement=supported, api=unknown, code=invalid: U0_support=true (∃supported), U0_unfalsified=true (∃unfalsified), U∧=inconclusive (bounds insufficient).'
- **Regex extractor transparency**: §6.2 records extraction_patterns in JSON output (good). Consider stating explicitly: 'Matched fragments enable manual spot-checking but do not constitute soundness proof; §4.3 adequacy theorems apply only if hSound/hComplete hold for the regex extractor (not verified in this paper).'
- **Long-term source stability**: §7.5 recommends DOI archival + Wayback fallback. Consider explicitly stating: 'SHA256 locks enable replay from snapshots but do not prevent upstream URL deletion; archival snapshot repositories (e.g., Software Heritage, Zenodo) recommended for 10+ year reproducibility.'

## Evidence Quote
- "本稿の実証主張は「interval-domain における reverse-mapping（部分射影が誘導する逆像）カーネルの実行可能性」に限定し、一般ドメインでの有効性・網羅性は主張しない。 (§0.3 主張境界)"
