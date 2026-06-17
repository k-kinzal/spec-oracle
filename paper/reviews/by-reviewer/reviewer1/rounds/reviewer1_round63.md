# Reviewer 1 Round 63

- Role: Formal Methods Reviewer (Round 63)
- Recommendation: Accept. No required fixes remain. The manuscript correctly scopes all claims, the PoC implementation is internally consistent with the stated design, and previously flagged issues have been resolved.
- Pass Gate: true

## Summary
Round 63 review finds no concrete inconsistencies between the manuscript (uadf_u0_spec_proof.md), the PoC driver (external_validation.py), and the replay script (reproduce.sh). All theoretical claims are appropriately bounded by Non-goals, adequacy theorems are guarded by explicit hSound/hComplete preconditions, PoC metrics match the stated formulas, the SHA256 precheck in reproduce.sh matches the hashes declared in §7.2, and the mutation detection table in §6.2 is consistent with the classify_uand/apply_none_policy implementation. pass_gate = true because required_fixes is empty.

## Strengths
- Tight claim scoping: every major claim (RQ1–RQ6) is accompanied by an explicit Non-goals section that prevents over-interpretation of the n=3 PoC.
- Dual-operator separation (U0 join vs. U∧ meet) is consistently maintained throughout the manuscript and reflected in the distinct code paths (u0_support_indicator vs. classify_uand).
- The must/may duality is formally defined (§4.7, preimageMay), mechanically verified in Lean, and operationally exercised in reproduce.sh steps 2–3.
- SHA256 integrity chain: reproduce.sh embeds expected hashes for external_validation.py, the lock file, and drift artefacts, matching the values declared in §7.2.
- The adequacy theorems (§4.3) are correctly guarded: the manuscript explicitly warns that hSound/hComplete are NOT verified for the regex extractor and instructs readers not to apply those theorems to PoC results.
- The mutation detection table (§6.2) is internally consistent: uand_contradiction detections tie to classify_uand returning 'contradictory', while bound_shrinkage detections tie to the upper <= floor(upper/1024) criterion, both implemented correctly in external_validation.py.
- The three-valued judgement pipeline (judgement → apply_none_policy → policy_judgement) is consistently defined in §4.7, the terminology table, and the implementation.
- support_ratio, unknown_ratio, and invalid_interval_ratio are defined by explicit formulas in §6.2 and implemented by status_ratio in external_validation.py with matching denominator (|I_active|=3).
- The offline replay guarantee (deterministic replay = same lock/snapshot input → same output) is correctly scoped; the script prevents clobbering the canonical lock during offline runs.
- The D(i)=ℤ×ℤ trivial placement is honestly disclosed as a limitation (§6.2, Non-goals), and no claim of domain-constraint validation is made.

## Required Fixes
- (none)

## Optional Fixes
- Minor clarity: §6.2 states 'zlib unit_mismatch_upper_scale_down_1024 produces mutated_intersection = [-1, 0]'. The code computes scaled_upper = max(0, 9//1024) = 0, so the mutated requirement upper = 0, and the intersection lower = max(-1, -1, min_z_candidates) which depends on z_no=-1 and z_default=-1 from zlib.h. The resulting lower=-1, upper=0 is plausible, but adding a one-line derivation comment in the table footnote would help readers independently verify this without running the script.
- Consider adding a sentence in §7.4 clarifying that the 59-theorem count excludes lemma/def declarations so readers do not attempt to reconcile it with a raw rg count that might include those keywords.
- The reproduce.sh SHA256 listed in §7.2 (3a60d05c...) ends at 62 hex characters in the manuscript excerpt, which is one character short of the expected 64. Verify this is a transcript/display artefact rather than an actual truncation in the paper source.
- The drift lock SHA256 in reproduce.sh (1f31c8e6...) and the drift snapshot SHA256 (0d2d319f...) are not listed in §7.2 of the manuscript. Adding them to §7.2 or a supplementary table would make the integrity chain fully auditable from the paper alone.

## Evidence Quote
- "RQ整合: RQ5 は抽象関係 E に対する一般定理の提示を対象とし、具体抽出器への適用証明は Non-goals として本稿では扱わない。" (§0.3) — confirms that the adequacy theorems in §4.3 are correctly not applied to the regex extractor, resolving the main structural concern from prior rounds. The implementation in external_validation.py is consistent: classify_uand operates on LayerBounds directly and is not gated on any hSound/hComplete proof obligation.
