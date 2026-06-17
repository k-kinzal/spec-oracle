# Reviewer 3 Round 50

- Role: Reviewer 3 (Reproducibility / Artifact)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This submission provides a solid reproducibility foundation with Lean4 mechanization (59 theorems, 1502 LOC), deterministic replay infrastructure (source-lock + snapshots), and transparent scope boundaries. The artifact demonstrates technical feasibility of reverse-mapping extraction (n=3 OSS, numeric constraints only) with pre-registered mutation expectations (6/6 detected). However, minor revisions are needed to: (1) strengthen the replay verification protocol with explicit SHA256 commands, (2) clarify the non-equivalence between PoC operational analogues (U0_support, classify_uand) and theoretical definitions (U0, UAndOn), and (3) add fail-safe instructions for snapshot SHA256 mismatches.

## Strengths
- Complete Lean4 mechanization with 59 theorems covering core model (§2), join/meet separation (§3), and adequacy decomposition (§4.3). No mathlib dependency reduces long-term bitrot risk.
- Deterministic replay infrastructure: source-lock JSON with URL/SHA256/UTC timestamps, offline snapshot bundle, and reproduce.sh wrapper for 3 policy modes (fail-fast/must/may).
- Transparent scope boundaries: Non-goals explicitly state no statistical generalization (n=3 convenience sample), no general NL understanding (regex-only), no extractor soundness proof, and no production readiness claim.
- Pre-registered mutation expectations: 2 mutation families (stale_requirement_lower, unit_mismatch_upper_scale_down_1024) with criterion-based validation (6/6 detected), avoiding post-hoc tuning.
- Theory-practice separation: §4.8 table clearly marks which theorems are Lean-verified vs. PoC-instantiated, preventing conflation of formal results with empirical demonstrations.
- Tri-state observability: layer_status (supported/invalid/unknown) + judgement (consistent/contradictory/inconclusive) + policy_judgement separation allows must/may policy comparison without information loss.

## Required Fixes
- §7.5 replay protocol: Add explicit SHA256 verification command (e.g., 'shasum -a 256 -c checksums.txt') before jq checklist. Current protocol only describes expected behavior but doesn't provide executable verification steps.
- §6.2 PoC-theory gap: Strengthen the warning that U0_support (PoC) and U0 (theory) are NOT generally equivalent. Current text (§6.2, footnote 'PoC instantiation') buries this in dense prose. Add a visible callout: 'IMPORTANT: classify_uand is an operational analogue, not a faithful implementation of UAndOn (§2.2).'
- §7.5 snapshot mismatch recovery: Add explicit recovery instructions if SHA256 check fails (current text only describes the exception). Example: 'If SHA256 mismatch occurs: (1) verify snapshots/* files are unmodified, (2) re-clone repository, (3) contact authors for archive DOI if issue persists.'
- §6.3 unknown semantics: Clarify that 'code.lower=null in 2/3 cases' reflects regex implementation limits, NOT a claim about API semantics being inherently underspecified. Current phrasing is ambiguous.

## Optional Fixes
- §7.4 Lean metrics: Add total proof-to-definition ratio and average proof length (lines/theorem) to give reviewers a sense of verification depth beyond raw counts.
- §6.4 negative example: Provide diff snippet showing the exact regex_drift input mutation (e.g., 'inclusive' deletion) to make the failure concrete and independently reproducible.
- §2.6 artifact-IR separation: Add a minimal worked example showing obs_i (artifact projection) vs extract_i (IR construction) with concrete types, similar to §6.1.1 but for the general case.
- paper/case-study/real_projects/README.md: Add 'Expected runtime' line (e.g., '<30 seconds on 2020 laptop') to set expectations for third-party replay.
- §3.3 contradiction definition: Provide a 1-sentence intuition before the formal definition (e.g., 'Two layers contradict if no root state satisfies both').

## Evidence Quote
- "§7.5: "Minimal Verification Checklist: jq '{n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation}' logs/external_validation_graceful_may.log" — provides executable replay target but lacks SHA256 pre-check step. §6.2: "PoC の U∧ は、同一 Ω 上で lifted(i) の meet を直接計算したものではなく、抽出制約（bounds）上の同時満足可能性を返す operational analogue として実装している" — correctly identifies gap but needs higher visibility for artifact users."
