# Reviewer 3 Round 51

- Role: Reviewer 3 (Reproducibility / Artifact)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This manuscript provides a well-specified deterministic replay protocol for a UAD/f PoC with explicit checksums, source-locks, and offline snapshots. The reproducibility specification (§7.5) clearly defines 4 deterministic fields and separates them from runtime-dependent metadata. The PoC scope is appropriately limited (n=3 convenience sample, numeric bounds only, regex extraction). However, the submission requires artifact verification: (1) Lean proofs must build via lake build, (2) extraction script checksum must match claimed SHA256, (3) offline replay must produce the 4 specified fields matching expected values. The manuscript's reproducibility design is publication-ready; acceptance depends on artifact bundle verification.

## Strengths
- Explicit deterministic replay specification with 4 fixed JSON fields (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation)
- Source-lock mechanism with SHA256 verification for offline replay without network dependency
- Three execution modes (fail-fast, graceful-must, graceful-may) with documented policy projection
- Mutation testing with pre-fixed expectations (6/6 detection) providing concrete verification targets
- Clear separation of deterministic comparison targets vs. auxiliary observables
- Appropriate scope limitations (preliminary feasibility, n=3 convenience sample, numeric bounds only)
- Extraction pattern transparency (regex + matched fragments recorded in output)
- SHA256 checksums provided for scripts and lock files

## Required Fixes
- Provide verifiable artifact bundle: Lean source for lake build, extraction scripts with matching checksums, snapshots directory, and reproduce.sh
- Execute and document one complete offline replay run showing the 4 deterministic fields match expected values from §6.2
- Verify Lean proof mechanization builds successfully and document the build environment (Lean version, dependencies)

## Optional Fixes
- Add explicit non-generalization clause to abstract stating results are preliminary feasibility demonstration not claiming statistical external validity
- Clarify earlier in §6.2 that U0_support is an observability indicator, not theoretical U0 membership
- Explain rationale for 1/1024 scaling factor in unit_mismatch mutation
- Consider adding a quickstart verification section showing minimal commands to verify deterministic replay

## Evidence Quote
- deterministic comparison is based on JSON structural equality of required fields (key order is not part of the equality condition). Expected checks: n_real_projects == 3, raw_judgement_distribution.consistent == 3, policy_judgement_distribution.inconclusive == 0, mutation_detected_by_expectation == 6
