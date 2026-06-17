# Reviewer 3 Round 48

- Role: Reviewer 3 (Reproducibility / Artifact)
- Recommendation: Accept
- Pass Gate: true

## Summary
This manuscript demonstrates strong reproducibility infrastructure with deterministic replay via source locks, SHA256 verification, and snapshot-based offline execution. The artifact package (Lean proofs + extraction PoC) meets acceptance standards for mechanized verification with clear scope boundaries. Key strengths: (1) deterministic replay specification with 4-field JSON schema validation, (2) tri-mode execution (fail-fast/must/may) with documented policy semantics, (3) complete lock chain (manifest/script/snapshot SHA256s), (4) Lean build verification without external dependencies. The PoC correctly positions itself as feasibility demonstration (n=3 convenience sample, interval-only, regex extraction) rather than statistical validation. Mutation detection (6/6) demonstrates pipeline functionality under controlled conditions. Minor clarifications needed on long-term URL stability and domain expert validation, but these do not block acceptance given the clear non-goals statements and preliminary scope.

## Strengths
- Deterministic replay specification is explicit and testable: 4-field JSON schema (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation) with structural equality defined in §7.5
- Complete lock chain with SHA256 verification: external_validation.py (7fb6541...), reproduce.sh (388ef94...), sources.lock (1b09065...), manifest (8c098d7...), plus 9 snapshot files with individual SHA256s
- Tri-mode execution framework (fail-fast/graceful-must/graceful-may) correctly implements must/may semantics from §4.7 theory, with logs demonstrating policy projection behavior
- Lean mechanization is self-contained: 59 theorems across 1502 LOC, stdlib-only (no mathlib), lake build verifiable, with explicit funext/propext basis and no Classical imports
- PoC scope is appropriately bounded: Non-goals (§0.3) explicitly exclude statistical generalization, non-interval constraints, extractor soundness proof, and production readiness claims
- Mutation testing provides controlled verification: 2 families (stale_requirement_lower, unit_mismatch_upper_scale_down_1024) with pre-fixed expectations, all 6/6 detected as expected
- U0/U∧ separation is observable: layer_status tri-state (supported/invalid/unknown), support_ratio (0.778), unknown_ratio (0.222) demonstrate operational coverage monitoring distinct from consistency judgement
- Artifact transparency: extraction_patterns preserve regex+matched fragments, enabling pattern audit without re-execution
- Offline replay verification: reproduce.sh executes all 3 modes via snapshot inputs with SHA256 checks, no network dependency post-snapshot creation

## Required Fixes
- None for acceptance gate. The manuscript meets reproducibility standards for preliminary feasibility demonstration.

## Optional Fixes
- Add explicit guidance on long-term URL stability mitigation (e.g., DOI-based archive deposit, Wayback fallback protocol) beyond current lock+snapshot approach
- Consider documenting expected behavior when snapshot SHA256 verification fails during offline replay (current implementation raises ValueError; operational guidance for version drift would strengthen long-term usability)
- Minor: The deterministic replay definition (§7.5) could benefit from explicit non-determinism tolerance statement for metadata fields beyond 'date' (though current jq-based 4-field check is sufficient for paper claims)
- Future work: Document extractor adequacy validation protocol (§4.3 theory → §6.2 practice gap is acknowledged but operational validation procedure would aid adoption)

## Evidence Quote
- "Deterministic replay verification: reproduce.sh executes all 3 modes via snapshot inputs with SHA256 checks, no network dependency post-snapshot creation (§7.5). Expected checks: n_real_projects == 3, raw_judgement_distribution.consistent == 3, mutation_detected_by_expectation == 6 (README.md, logs/external_validation_graceful_may.log confirms all conditions)."
