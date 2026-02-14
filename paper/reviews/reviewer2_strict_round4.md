# Reviewer #2 Formal Methods Specialist Assessment

Verdict: OK

## Key reasons

1. **Mechanization scope is adequate**: The Lean4 formalization (1103 LOC, 43 theorems) covers the core theoretical contributions without overreach. The type-indexed model (`carrier : I → Type`), partial projection (`proj i : Ω → Option β_i`), and dual operations (`U0` join vs `U∧` meet) are mechanically verified with explicit assumption tracking.

2. **Novel theoretical contributions are validated**: The four "discoveries" (§5) represent genuine formalization insights rather than trivial set theory:
   - Discovery 2: Same-root connection assumption in transfer theorem (`hproj` in `lifted_transfer`)
   - Discovery 3: Sound/complete decomposition (`preimage_subset_semanticPullback_of_sound`, `semanticPullback_subset_preimage_of_complete`)
   - Discovery 4: Adjoint failure under partiality (`no_left_adjoint_of_partial`)

3. **Reproducibility is exceptional**: Full build chain documented (Lean 4.27.0, no mathlib), source locks for external data (`external_validation_sources.lock.json` with SHA256/UTC timestamps), and explicit scope limits prevent overgeneralization.

4. **Statistical claims are appropriately constrained**: The manuscript correctly labels the 3-OSS evaluation as "convenience sample" demonstration of extraction pipeline, not population inference. Mutation testing is framed as procedure validation, not bug prevalence estimation.

5. **Assumption hygiene is explicit**: All major theorems mark their premises clearly (e.g., `hproj` in layer transfer, `hcomm` in composition). The non-Classical foundation choice is documented (§7.3).

6. **Related work positioning is honest**: Acknowledges that UAD/f is not replacing abstract interpretation or institution theory, just providing a minimal mechanized core for a specific root-integration problem.

## Minor edits before camera-ready

1. **§2.2 notation conflict**: Manuscript uses `f^{-1}_{0i}` in math but Lean code shows `preimage`. Add explicit bridge: "We write `f^{-1}_{0i}(S)` in mathematical notation for what Lean implements as `M.preimage i S`."

2. **§6.2 mutation test interpretation**: Add one sentence after Table: "The 3/3 detection rate demonstrates that the intersection logic responds correctly to constraint violations, not that real-world specs have 100% contradiction rates."

3. **§7.4 LOC breakdown percentages**: The sum 9.1% + 62.8% + 28.1% = 100%, but readers may wonder about test files. Add footnote: "Percentages exclude infrastructure files (lakefile, manifest) which add <50 LOC."

4. **§4.4 adjoint theorem**: The statement "left adjoint" should clarify direction. Change to: "If `∃x0, proj_i(x0)=none`, then `preimage_i` has no left adjoint `F` satisfying the Galois connection `F S ⊆ T ↔ S ⊆ preimage_i T`."

5. **§6.3 scope limitation**: Add to end of paragraph: "This evaluation validates *extraction mechanics* (regex → constraint → intersection), not *completeness* of requirements coverage in the three selected projects."

6. **Reference formatting**: "P. Cousot and R. Cousot" should include full citation (POPL '77, pp. 238–252). Similarly for Goguen/Burstall and Lamport TLA+ book.
