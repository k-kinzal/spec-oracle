# Reviewer 1 Round 45

- Role: Reviewer 1 (Formal Methods / Mechanization correctness)
- Recommendation: Accept
- Pass Gate: true

## Summary
The authors have successfully addressed all blocking formal issues from Round 44. The manuscript now achieves acceptable rigor through: (1) explicit Non-goals block clarifying what is NOT claimed (§0.3), (2) strengthened adequacy boundary distinguishing abstract theorems from concrete extractors (§4.3), (3) operational-analogue framing for PoC U∧ (§6.2), and (4) consistent separation of RQ5(theory) vs RQ6(practice). The mechanization remains sound (59 theorems, mathlib-free), and the PoC claims are now properly scoped as preliminary feasibility demonstration rather than external validation. No blocking issues remain.

## Strengths
- Non-goals block (§0.3) explicitly states what is NOT claimed: no statistical generalization from n=3, no interval-domain generalization, no extractor soundness/completeness proof, no production-readiness claim
- §4.3 adequacy theorems now clearly marked as abstract (relation E), with explicit warning that applying to regex/LLM requires separate proof of hSound/hComplete assumptions
- §6.2 PoC U∧ correctly framed as 'operational analogue' rather than direct UAndOn implementation, with clear statement that judgement uses bounds not intervals
- RQ5/RQ6 boundary cleanly separated: §4.8 table explicitly shows which theorems are unverified in PoC, §6.2 focuses solely on deterministic replay (RQ6)
- Mechanization quality unchanged: 59 theorems, no Classical dependency, funext+propext only, reproducible build

## Required Fixes
- None

## Optional Fixes
- Consider adding forward reference from §4.3 to §4.8 table immediately after adequacy theorems, to remind readers that extractor application requires separate verification
- In §6.2 PoC model connection paragraph, consider emphasizing once more that extract_i soundness is assumed not proven (currently stated but could be more prominent given §4.3 warnings)

## Evidence Quote
- "§0.3: "本稿が主張しないこと: n=3 PoC からの統計的一般化（母集団推定）は行わない. interval-domain 以外（状態遷移・時相・非連続構造制約）への一般妥当性は主張しない. 抽出器（regex/LLM）の soundness/completeness 証明は本稿の対象外である.""
