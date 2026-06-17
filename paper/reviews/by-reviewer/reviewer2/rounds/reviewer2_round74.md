## Formal Methods Paper Review — Reviewer #2

**Paper:** *UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization*
**Target venues:** FM / ITP / CPP / TACAS / FASE / Formal Aspects
**Role:** Reviewer #2 (balanced but rigorous)

---

## 1. Overall Recommendation

**Minor Revision**

The paper presents a self-contained, axiom-disclosed Lean4 mechanization of a partial-projection kernel for multi-layer specification comparison. The theorem-to-file traceability is unusually thorough, the non-claims are explicitly stated, and the assumption matrix (Appendix) is a genuine methodological asset. The core contribution — an assumption-audited typed kernel where same-root linkage, admissibility transport, and one-sided adequacy are individually mechanized with counterexample witnesses — is technically sound and appropriately scoped.

Revision is required mainly to address: (a) insufficient justification of the novelty delta against related work, (b) an underdiscussed tension in the axiom footprint, and (c) reproducibility claims that rely on local-run evidence alone.

---

## 2. Strengths

**S1. Explicit non-claims (§0.2).** The paper lists five non-claims explicitly, which is rare and valuable. Reviewers can evaluate the paper against what it actually claims.

**S2. Assumption-matrix appendix.** The `assumption_matrix.md` appendix is the most directly useful artifact: for each theorem, it states the required assumptions, the failure mode if dropped, and the fallback claim. This enables precise evaluation of whether counterexample theorems (`TransferCounterexample.lean`, `AdequacyCounterexample.lean`) are non-redundant, and they are.

**S3. RQ-to-theorem traceability (§1.5).** The matrix linking each research question to named Lean theorems and file paths is concrete. RQ1/RQ2 are correctly demoted to supporting questions, with explicit resolution policies (§1.3).

**S4. Axiom footprint disclosure (§4.3).** The per-theorem `#print axioms` table is the correct level of disclosure for this type of mechanization paper. The asymmetry between `lifted_transfer` (no axioms) and `preimage_compose` (`propext`, `Classical.choice`, `Quot.sound`) is acknowledged and explained (§4.3, points 9–10).

**S5. Mathlib-free design rationale stated.** The tradeoff of avoiding Mathlib (exposing all assumptions through a minimal dependency surface, at the cost of reduced immediate interface reuse) is explicitly stated in §2.1. This is an honest methodological choice.

**S6. Must/may split is operationally justified.** §3.6.2 explains why `semanticPullbackMay` includes the `proj_i(x)=none` branch — it is an operational comparability choice, not arbitrary. The rejected alternative is stated. This is the correct level of design narrative for a formal paper.

**S7. Vacuous-truth edge case is mechanized.** `UAndOn_empty_eq_univ` is not merely stated as a warning — it is a theorem, it appears in the counterexample file (`ContradictoryLayers.lean`, `contradictoryModel_empty_active_has_spurious_witness`), and it propagates to the operational enforcement note in §3.3. This is handled correctly.

---

## 3. Major Issues

**M1. Novelty delta (§6.1) is asserted, not argued.**

§6.1 claims the delta is "one auditable kernel that simultaneously fixes heterogeneous carriers, partial projections, assumption interfaces, and counterexample-backed boundary theorems." This is a combination-level claim. However, the paper does not argue why this combination is not directly obtainable by composing Mathlib's `Set.preimage_comp`, `GaloisConnection`, and lattice APIs — it merely asserts "baseline APIs provide component lemmas, but not this full assumption-audited contract bundle."

This assertion may be true, but for a CPP/ITP audience it is insufficient. The paper should either:
- Demonstrate concretely that the `Option`-based partial preimage signature with heterogeneous `carrier : ι -> Type` does *not* reduce to a straightforward Mathlib instance (e.g., the particular interaction between `Option.bind` commutation in `preimage_compose` and the impossible-branch elimination in §3.5 is the genuine difficulty), or
- Acknowledge that the novelty is primarily *methodological packaging* (explicit assumption interfaces + counterexample witnesses), not mathematical identity novelty.

The paper's own §6 preamble states "novelty claim is interface-level and methodological," which is the right framing — but §6.1 then reverts to listing mathematical deltas. These two framings should be unified.

**M2. Reproducibility claims rest entirely on local-run evidence.**

§9 and `build_evidence.md` record one local run (`Build completed successfully (42 jobs)`) and hash-check three files. There is no CI record, no artifact evaluation badge claim, and no Docker/Nix environment specification. For venues like CPP or TACAS with artifact evaluation tracks, the `reproduce_formal.sh` script is necessary but not sufficient:

- The script assumes `rg` (ripgrep) is installed but does not check for it.
- The LOC check (`wc -l`) is OS-sensitive (macOS vs. Linux differ on trailing-newline handling).
- The `42 jobs` build-graph count is noted as "not expected to equal source-file count" but no explanation is given of what drives it.

The paper should either: (a) provide a container specification for bit-reproducible builds, or (b) explicitly scope the reproducibility claim to "same Lean toolchain + same manifest" and document what environmental assumptions are made.

**M3. `CaseStudy/PasswordPolicy.lean` is claimed as a "mechanized sanity theorem" (§5.2) but its role in the RQ structure is unclear.**

`req_projection_adequacy` is described as "a concrete instantiation of abstract adequacy interface, not as a general proof of extractor correctness." This is correctly scoped. However, the password-policy case study is not linked to any RQ in §1.5 (the traceability matrix), and §5.2 does not explain what the case study *adds beyond* `ArtifactBundleExample.lean`. If the adequacy interface is already instantiated in `ArtifactBundleExample.lean` (§5.1), the PasswordPolicy case study needs a distinct justification — e.g., it demonstrates constrained-interval domain behavior not covered by the bundle example, or it validates `checkConsistent_iff_allThree` as a decision procedure for a specific domain. This should be made explicit, or the case study should be repositioned as an appendix-level validation.

**M4. `UStar` parametricity is underexplained in the context of the paper's motivation.**

§3.8 states "`UStar` is an explicit theorem parameter denoting ideal-root predicate (it is not constructed by this kernel; theorem statements are parametric in `UStar`)." This is honest and correct. However, the paper's introduction-level motivation (§1.1) frames the problem as "ideal complete root specification `U*` is usually unavailable in practice." A reader will naturally ask: if `UStar` is just a parameter, what do the `UStar_*` theorems actually achieve beyond expressing conditional linkage? The answer — "their value is to make assumption strength explicit and machine-checkable" — is given at the end of §3.8, but it arrives after three paragraphs of notation. The paper should front-load this interpretation (ideally in the abstract or §1.2) so the parametricity of `UStar` reads as a feature rather than a limitation.

---

## 4. Minor Issues

**m1. Section §2.3 "Pedagogical composite excerpt" disclaimer.**

The code block in §2.3 is described as a "Pedagogical composite excerpt across" two files. For a mechanization paper, presenting composite code that does not appear verbatim in any file is a reviewer risk: if the composite contains discrepancies from the actual source, the paper's traceability claims are weakened. Recommend either: (a) use `-- from File.lean` inline comments and quote exactly, or (b) replace the composite with a direct reference to the file and the theorem signature only.

**m2. §4.3 item 4 is potentially misleading.**

"does not use `open Classical`, but this namespace choice does not disable kernel-level classical constants" — this is true but may mislead readers unfamiliar with Lean4. The operative fact is that `Classical.choice` appears in `preimage_compose` proof terms regardless of namespace. The explanation should be inverted: "classical constants appear in proof terms regardless of `open Classical` because they are resolved at elaboration time; the namespace choice affects readability, not axiom usage."

**m3. `UAndOn_subset_UAndMayOn` appears in the theorem catalog (Construction.lean, line in §3.3 table header) but is not named in §3.3 body text.**

§3.3 lists five theorems for the role-separation bundle but the traceability table in §4.5 lists `UAndOn_subset_UAndMayOn` as a Construction.lean theorem in the must/may operator laws row. It is not discussed in §3.3 or §2.6 with adequate depth. A one-sentence clarification of its role (must ⊆ may direction for the meet operator) would complete the narrative.

**m4. Reference [11] (Darais & Van Horn, "Constructive Galois Connections") is cited in §7.5 but the definition-level difference is stated at prose level only.**

For a CPP audience, the difference from constructive Galois connections should note specifically that Darais & Van Horn work with total abstraction/concretization maps, while this paper's `no_left_adjoint_of_partial` starts from an undefined-point witness. The current text says this but could be made one sentence more precise: the non-adjointness proof uses the undefined-point witness to derive contradiction from the adjunction universal quantifier, which is a proof shape unavailable in total-map constructive settings.

**m5. `transfer_false_to_true` (CompositionExample.lean / TransferChainExample.lean) appears in the catalog but is not discussed in the manuscript body.**

`transfer_false_to_true` in `TransferExample.lean` (theorem count: 1) and `transfer_code_to_api` / `transfer_api_to_req` in `TransferChainExample.lean` (theorem count: 2) are listed in the catalog with no manuscript reference. Either add a one-line description of what these establish, or note they are internal sanity examples subsumed by the main transfer discussion.

**m6. LOC count (1703) includes example files.**

§4.4 states LOC for `paper/lean/UadfU0` is 1703 total. Given that `Examples/` and `CaseStudy/` are included, a breakdown (e.g., core definitions + theorems: N lines; examples + case study: M lines) would help readers calibrate the mechanization effort.

---

## 5. Required Revision List

**R1** (addresses M1): Add a paragraph in §6.1 that either (a) gives a concrete argument for why the `Option.bind`-based partial preimage with heterogeneous carriers does not reduce to a standard Mathlib composition, or (b) explicitly reframes the contribution as methodological packaging (assumption-interface design + counterexample witnesses) rather than mathematical identity novelty. Unify with the "interface-level and methodological" framing in §6 preamble.

**R2** (addresses M2): Provide one of: (a) a container specification (Docker, Nix flake) for the build environment, or (b) a clearly scoped environmental assumptions section in §9 listing OS, `rg` version, and `wc` behavior. Add a `command -v rg || exit 1` check in `reproduce_formal.sh`. Clarify the `42 jobs` count.

**R3** (addresses M3): In §5.2, explicitly state what `CaseStudy/PasswordPolicy.lean` adds beyond `ArtifactBundleExample.lean`. Link the PasswordPolicy case study to at least one RQ or claim boundary, or reposition it as an appendix-level validation.

**R4** (addresses M4): Move the interpretation of `UStar` parametricity ("their value is to make assumption strength explicit and machine-checkable") to earlier in the paper — at minimum to §1.2 or the abstract — so readers do not read §3.8 as a limitation disclosure before seeing the design rationale.

**R5** (addresses m1): In §2.3, replace the pedagogical composite with either exact source quotations with inline file references, or pure prose + theorem-signature references pointing to the canonical files.

**R6** (addresses m3): Add one sentence in §3.3 or §2.6 explaining `UAndOn_subset_UAndMayOn` and its role in the must/may split.

**R7** (addresses m5): In §4.4 or §5, add a one-line description of `transfer_false_to_true`, `transfer_code_to_api`, and `transfer_api_to_req`, or explicitly note they are internal sanity examples subsumed by the main Transfer section.
