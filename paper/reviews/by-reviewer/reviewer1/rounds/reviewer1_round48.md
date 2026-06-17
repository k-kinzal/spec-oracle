# Reviewer 1 Round 48

- Role: Reviewer 1 (Formal Methods / Mechanization Correctness)
- Recommendation: Accept
- Pass Gate: true

## Summary
This manuscript presents a mechanized UAD/f model with explicit separation of U0 (join/coverage baseline) and U∧ (meet/consistency), backed by 59 Lean4 theorems across 1502 LOC. The formal contribution lies in making previously implicit assumptions explicit through typed mechanization: (i) same-point connection requirement for inter-layer transfer (§4.1), (ii) one-sided adequacy decomposition for extraction (§4.3), (iii) partiality breaking adjunction (§4.4), and (iv) must/may semantics for none-handling (§4.7). The PoC demonstrates deterministic replay (RQ6) with source-locked artifact extraction (n=3, interval constraints only), maintaining clear boundaries between proven theory and operational approximation. All theorem-to-Lean mappings are traceable (§7.6), reproduction package is complete with SHA256 locks, and non-goals are explicitly bounded (no statistical generalization, no general NL understanding, no completeness proof for regex extractors). The work achieves its stated goal: a reference mechanization of UAD/f core with explicit assumption tracking, not a complete specification management system.

## Strengths
- Explicit assumption tracking: Model parameters (hproj, hA, hSound, hComplete) are surfaced as Lean function arguments rather than hidden preconditions, enabling formal dependency tracking (§4.1-4.3)
- Clean separation of U0 (join-based coverage) vs U∧ (meet-based consistency) with proven GLB/LUB properties (§3, Minimality.lean), resolving earlier semantic conflation
- Partiality as first-class concern: Theorem no_left_adjoint_of_partial (§4.4) demonstrates that Option-typed projections break standard abstract interpretation intuitions, justifying the partial-function foundation
- One-sided adequacy theorems (§4.3) decompose extraction soundness/completeness independently, providing theoretical grounding for operational policy choices (must/may) without claiming concrete extractor verification
- Reproducibility package exceeds standard: deterministic replay with SHA256 locks (§7.5), offline snapshot bundle, 3-mode policy comparison logs, and jq-checkable success conditions
- Honest scope boundaries: Non-goals (§0.3) clearly exclude statistical generalization, behavioral specification completeness, and extractor soundness proofs—preventing over-claiming
- Theory-practice separation: §6.2 PoC operational analogues (e.g., classify_uand as U∧ approximation) are labeled as such, not claimed as direct theory implementations
- Mutation expectation pre-registration: §6.2 fixes expected outcomes (contradictory for stale_requirement_lower, upper'<=floor(baseline/1024) for unit_mismatch) before execution, avoiding post-hoc interpretation

## Required Fixes
- None for acceptance gate (formal consistency achieved)

## Optional Fixes
- §2.6: Consider renaming 'obs_i' to 'artifact_proj_i' to avoid confusion with 'observation' in trace semantics (current usage is clear but could be more distinctive)
- §4.3: Add forward reference to §6.2's RQ5/RQ6 boundary note earlier in the adequacy section to preempt reader expectation of concrete extractor proofs
- §6.2: The tri-state layer_status (supported/invalid/unknown) could benefit from a small Lean example formalizing the partition to parallel §6.1.1's ArtifactBundleExample
- §7.6: Consider adding a column for 'Assumption dependencies' to the theorem correspondence table to make proof structure more transparent at a glance
- Table in §4.8 (theorem applicability): Could add a 'Required for RQ' column to clarify which theorems directly support which research questions
- §6.4 (negative case): The regex drift example is valuable but presented as narrative—a structured failure-mode taxonomy table would strengthen replication guides

## Evidence Quote
- "Therefore, this manuscript is not claiming 'we proved regex extractors correct for RQ5' but rather 'we proved one-sided adequacy theorems (§4.3) for abstract E, and demonstrated deterministic replay (RQ6) with operational must/may policies that connect to those theorems conceptually.' The PoC (§6.2) validates RQ6 (technical reproducibility) while RQ5 (theory) provides the adequacy framework that future concrete extractor proofs could instantiate."
