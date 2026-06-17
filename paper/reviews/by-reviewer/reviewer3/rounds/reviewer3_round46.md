# Reviewer 3 Round 46

- Role: Reviewer 3 (Reproducibility & Artifact Acceptance-Gate)
- Recommendation: Accept
- Pass Gate: true

## Summary
This submission meets reproducibility standards for artifact acceptance. The manuscript provides comprehensive source-lock infrastructure (SHA256 hashes, snapshots, lock files), clear build instructions for Lean proofs, and deterministic replay machinery for the extraction PoC. The tri-valued judgement system (consistent/contradictory/inconclusive) with policy projection (must/may) is properly tracked. The 3-project PoC demonstrates technical feasibility with n=3 convenience sample and correctly scopes claims to "preliminary feasibility demonstration" rather than statistical validation. Key metrics (n_real_projects=3, raw_judgement_distribution.consistent=3, mutation_detected=6/6) are verifiable via provided jq commands. Minor documentation gaps exist but do not block reproduction.

## Strengths
- Complete source-lock chain: SHA256 hashes for Python script (7fb6541b...), reproduce.sh (388ef94c...), lock file (1b090656...), manifest (8c098d78...) enable bitwise verification
- Deterministic replay specification: §7.5 explicitly defines deterministic comparison via structural JSON equality on required fields (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation), with non-deterministic fields (date) properly excluded
- Offline reproducibility: Snapshots bundled in repo enable network-free replay via --offline-lock mode with SHA256 verification at load time
- Minimal verification checklist: README provides executable jq command for 3 core assertions matching manuscript claims
- Lean proof reproducibility: Clear toolchain (leanprover/lean4:v4.27.0), lake build command, no external dependencies beyond stdlib, 1502 LOC with 59 theorems
- Failure-mode transparency: Three replay modes (fail-fast, graceful-must, graceful-may) with separate logs demonstrate policy-projection behavior under extraction failures
- Mutation expectation pre-registration: Two mutation families (stale_requirement_lower, unit_mismatch_upper_scale_down_1024) with explicit expectation criteria avoid post-hoc outcome mining
- Pattern transparency: extraction_patterns field preserves regex+matched-fragment pairs for audit trail of automatic_regex_no_manual_edit extraction mode

## Required Fixes
- None

## Optional Fixes
- Add explicit SHA256 verification command in README (e.g., shasum -a 256 external_validation.py expecting 7fb6541b...)
- Consider adding .PHONY target in reproduce.sh or Makefile for clarity on deterministic vs. runtime-dependent outputs
- Clarify whether snapshots/* are intended for version control or external archive (current approach bundles them, which aids reproducibility but increases repo size)
- The manuscript states Python 3.9.6 but README does not specify minimum Python version; recommend adding explicit version constraint

## Evidence Quote
- "§7.5: "Deterministic comparison is based on JSON structural equality of required fields (key order is not part of the equality condition)." + "sha256(external_validation.py)=7fb6541b43605e229aa68b73c921908969400e5adc3152b84381e37a9837d2d4" + README: "jq '{n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation}' logs/external_validation_graceful_may.log""
