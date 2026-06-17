# Reviewer 1 Round 49

- Role: Reviewer 1 (Formal Methods / Mechanization correctness)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The manuscript presents a mechanized formalization of UAD/f's reverse-mapping core with appropriate rigor. The Lean4 mechanization (59 theorems, 1502 LOC) validates non-trivial formal properties including join/meet separation, non-adjointness under partial projections, and one-sided adequacy decomposition. The PoC correctly positions itself as a deterministic-replay feasibility demo (n=3, interval constraints only) rather than statistical validation. Assumption boundaries are explicitly tracked, and non-goals are clearly stated. The gap between abstract adequacy theorems (RQ5) and concrete extractors (RQ6) is acknowledged. Minor revisions needed to tighten the D(i) operational story and clarify the extractor trust boundary.

## Strengths
- Mechanization is substantive: 59 theorems with explicit Lean file/line references, non-trivial dependency structure
- Assumption tracking is rigorous: hproj/hA (§4.1), hSound/hComplete (§4.3), UStar hypothetical relationships (§3.5) all explicitly typed
- Honest scope boundaries: Non-goals (§0.3) clearly exclude statistical generalization, general-domain validity, and extractor soundness proofs
- Join/meet separation (§3) resolves semantic confusion between coverage (U0) and consistency (U∧) with proper GLB/LUB theorems
- Non-adjointness result (§4.4) under partial projections is formally valid and exposes a hidden assumption in standard abstract interpretation
- PoC deterministic replay (RQ6) demonstrates operational feasibility with source-lock and mutation tracking, without overclaiming generality

## Required Fixes
- Clarify extractor trust boundary: §4.3 adequacy theorems apply to abstract E, but PoC uses regex without proving hSound/hComplete. Add explicit 'trust assumption' section for the regex layer.
- Tighten D(i) operational story: §2.1 defines D(i) separation but §6.2 PoC admits 'D(i) trivial (ℤ×ℤ)...unit normalization future work'. Either demonstrate D(i) in PoC or move it to 'formal design not yet operationalized'.
- Make theorem→PoC gap more visible: Add a single table showing which of the 4 core theorems (§4.1-4.4) are instantiated in PoC vs. remain abstract demonstrations.

## Optional Fixes
- Consider adding a 'mechanization lessons' subsection: what design choices emerged from Lean formalization that weren't obvious in informal reasoning?
- The 'no manual edit' constraint (extraction_mode) is important for reproducibility but buried in JSON—consider elevating to a numbered 'reproducibility principle'.
- Minor notation: the switch between f_{0i} and proj_i could be smoother—consider always using proj_i with a single definitional equation f_{0i} := proj_i.
- The mutation coverage (2 families) is acknowledged as limited but could benefit from a 'mutation threat model' framing: what classes of spec drift are/aren't covered?

## Evidence Quote
- "Lean: `lifted_transfer` in `paper/lean/UadfU0/InterLayer/Transfer.lean`. [...] Lean: `preimage_compose` in `paper/lean/UadfU0/InterLayer/Composition.lean`. [...] **重要（適用境界）**: 本節の adequacy 定理は抽象関係 `E` に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について `hSound` / `hComplete` が成り立つことを**別途証明**する必要がある。"
