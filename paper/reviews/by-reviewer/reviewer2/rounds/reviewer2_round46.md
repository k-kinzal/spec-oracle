# Reviewer 2 Round 46

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This manuscript presents a mechanized formalization of UAD/f root coverage construction through reverse mapping (§0-§4) with deterministic replay demonstration on n=3 OSS projects (§6). The theory-practice boundary is now clearly delineated: RQ1-5 target formal adequacy with explicit assumptions, while RQ6 demonstrates source-locked extraction replay feasibility. The scope is appropriately narrow—interval-domain numeric constraints only, with Non-goals explicitly excluding statistical generalization, non-interval domains, and extractor soundness proofs. Minor revisions are needed to strengthen claim precision in extraction-theory connection and mutation interpretation, but no blocking issues remain.

## Strengths
- Explicit Non-goals section (§0.3) cleanly separates feasibility demo from statistical validation claims
- Theory-practice boundary is mechanically enforced: §4.3 adequacy theorems are abstract over relation E, with explicit note that regex extractor application requires separate proof (§4.8, §6.2)
- Deterministic replay definition (§7.5) is operationally precise with jq-based verification contract
- Tri-state observability (supported/invalid/unknown) avoids premature unknown→boolean collapse, enabling must/may policy separation
- 59 Lean theorems with dependency structure expose design assumptions (§5) rather than claiming novel mathematical results
- Mutation expectations are pre-fixed conditions (stale_requirement_lower: judgement=contradictory; unit_mismatch: upper'≤floor(baseline/1024)) not post-hoc pattern fitting
- Source-lock (SHA256+UTC+snapshot) provides artifact-level reproducibility independent of upstream document stability

## Required Fixes
- §6.2: Clarify that 'mutation_detected_by_expectation=6/6' measures adherence to pre-specified detection conditions, not discovery of real bugs or validation of fault-detection effectiveness
- §4.3 + §6.2: Add explicit statement that adequacy inclusion directions (sound→under-approx, complete→over-approx) apply to *abstract E only*, and that operational false-positive/false-negative rates depend on unstated regex extractor properties
- §6.3: Replace 'what was detected' phrasing with 'what expectation was satisfied' to avoid implying the mutations represent discovered defects rather than synthetic test conditions
- Abstract: Change '実アーティファクト抽出パイプラインの再実行可能性を示す' to explicitly mention 'n=3 convenience sample' to prevent readers from assuming production-scale validation

## Optional Fixes
- §6.2: Add a sentence explaining why code.lower is null in 2/3 cases—is this regex limitation or genuine API under-specification? Current text leans toward regex limitation but could be clearer
- §6.4: Consider renaming 'negative example' to 'extractor brittleness example' since the regex drift is not a counterexample to the theory
- §7.6: Add column showing which theorems have concrete instantiation in §6 vs. remain abstract—helps readers distinguish proven-applicable from proven-but-not-instantiated results
- §3.4: Since MUS extraction is defined but not implemented, consider adding estimated complexity class (NP-hard subset enumeration) to set expectations for future work

## Evidence Quote
- "本稿の実証主張は「interval-domain における reverse-mapping（部分射影が誘導する逆像）カーネルの実行可能性」に限定し、一般ドメインでの有効性・網羅性は主張しない。(§0.3) ... 本節は RQ6 (practice) の deterministic replay を対象とするため、§4 の理論定理は「適用可能条件」を次のように区別する。... §4.3 adequacy（must/may）: 未検証（実抽出器への意味保存証明は範囲外）(§4.8)"
