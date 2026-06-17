# Reviewer #2 — Formal Methods Venue Review

**Paper:** UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization

---

## 1. Overall Recommendation

**Minor Revision**

The paper presents a mechanized Lean4 kernel for multi-layer specification comparison under partial projections. The mechanization integrity appears solid: zero `sorry`, explicit axiom audit, theorem-to-file traceability, and counterexample-backed failure boundaries. The contributions are well-scoped and the non-claims section is commendably honest. The primary concerns are (a) insufficient differentiation from directly comparable mechanized work, (b) unclear novelty positioning for `RQ1`/`RQ2` which are listed as "supporting only," and (c) some reproducibility gaps that a reader would encounter trying to independently verify the build.

---

## 2. Strengths

**S1. Disciplined assumption disclosure.** The assumption matrix (Appendix `assumption_matrix.md`) is a genuine contribution to mechanization practice. Explicitly pairing each theorem with its failure mode and fallback claim goes beyond what most mechanized papers provide.

**S2. Counterexample-backed boundaries.** `TransferCounterexample.lean` (§5.3) and `AdequacyCounterexample.lean` (§5.4) are mechanized falsifications of the same theorems proven in the main development. This is methodologically sound: it confirms that `hproj` and one-sided adequacy obligations are real constraints, not redundant hypotheses.

**S3. Honest non-claims section (§0.2).** Explicitly listing five non-claims up front — including no extractor correctness and no standalone novelty for any single guardrail theorem — sets appropriate expectations. This is rarer than it should be.

**S4. Axiom audit (§4.3).** Per-theorem `#print axioms` results, with explicit explanation of why `Classical.choice` and `Quot.sound` appear, is exactly what a formal-methods reviewer needs. The disclosure that `lifted_transfer` carries no axioms while `preimage_compose` uses `Classical.choice` is informative and honest.

**S5. Scoped Mathlib-free design with explicit tradeoff acknowledgment.** §2.1 acknowledges the tradeoff of an empty package list. This is a legitimate design choice for an assumption-exposure artifact, and the manuscript states it rather than hiding it.

---

## 3. Major Issues

**M1. Related-work differentiation is insufficiently precise (§7).**

The paper names seven related lines (abstract interpretation, institutions, view consistency, BX, Galois connections, etc.) and gives definition-level differences in §7.7. However, the comparisons remain at the level of "we do X, they do Y" without showing that a naive combination of existing Lean/Mathlib infrastructure could *not* serve the stated purpose.

Specifically: Mathlib's `Set.preimage`, `GaloisConnection`, and `Order.BoundedOrder` provide large parts of the order-theoretic substrate. §6.1 ("Concrete delta against baseline theorem libraries") acknowledges this but only argues that *this specific combination* is novel. For venues like CPP or ITP, that argument requires showing a concrete attempt to assemble the claimed interface from existing Mathlib components and identifying exactly where it fails (e.g., because `carrier : ι -> Type` is heterogeneous in a way `Set.preimage` cannot accommodate without universe-level manipulation, or because partial projections force a must/may split that has no Mathlib counterpart). The current prose does not reach that level of precision.

**Required action:** Either (a) exhibit a minimal Lean snippet showing where direct Mathlib reuse breaks for the heterogeneous/partial case, or (b) cite a specific Mathlib theorem whose statement is closest and state the interface gap at the type-signature level.

---

**M2. `RQ1`/`RQ2` are simultaneously demoted and used (§1.3 vs §3.2).**

§1.3 says "Primary RQs for this formal paper are `RQ3`, `RQ4`, and `RQ5`. `RQ1` and `RQ2` are supporting questions." But §3.2 ("Supporting RQ linkage") introduces `RQ1` and `RQ2` answers as the basis for `lifted_subset_preimage_domain` and `U0_witness_projects_to_some_domain`, which are then used in transfer and ideal-root proofs. If these are only "supporting," the paper must either (a) remove the RQ framing entirely and treat them as definitional infrastructure, or (b) promote them to co-equal RQs and adjust the contribution claim accordingly. As written, the RQ-to-theorem matrix in §1.5 lists `RQ1`/`RQ2` with full theorem anchors, making the "supporting only" designation confusing.

**Required action:** Resolve the inconsistency. Either demote `RQ1`/`RQ2` to infrastructure definitions with no RQ label, or integrate them as full RQs with appropriate weight in the evaluation criteria (§1.4).

---

**M3. Reproducibility gap: hash check command is split across contexts (§4.4 vs §9).**

§4.4 gives an artifact integrity check using `rg` from `paper/lean` after `cd`. §9 gives a manifest hash check that must be run from "repository root (not from `paper/lean` after `cd`)". A reviewer attempting to verify these steps independently will encounter a working-directory mismatch that is easy to get wrong. The `build_evidence.md` appendix records outputs but does not record the hash value of `lake-manifest.json` itself, only the command to compute it.

More importantly, `build_evidence.md` records `Build completed successfully (42 jobs)` but does not record the Lean toolchain version in the output — the `lean-toolchain` file content (`v4.27.0`, per §4.3) is referenced in the manuscript but the hash of that file is not reported in the appendix.

**Required action:** (a) Consolidate all verification steps into a single shell script with explicit working-directory setting; (b) record the expected manifest hash value and `lean-toolchain` hash in `build_evidence.md` so a reviewer can compare rather than compute; (c) clarify what "42 jobs" means relative to source-file count (§4.4 says "is a build-graph execution count and is not expected to equal source-file count" — this should also appear in or near the build evidence appendix).

---

**M4. `UAndOn_empty_eq_univ` operational consequence is stated but not fully threaded (§3.3, §8).**

§3.3 states that operational use of `UAndOn` as a consistency signal must enforce non-empty active sets. §8 (Limitations) lists this as item 5. However, neither the main theorem family nor the examples show what breaks in practice when this constraint is violated — there is a counterexample for `hproj` absence (`TransferCounterexample.lean`) and for `E ≠ proj` (`AdequacyCounterexample.lean`), but no mechanized example showing `UAndOn` vacuous-truth misuse. Given that §3.3 explicitly flags this as a policy-sensitive failure mode, the absence of a mechanized vacuous-truth example is inconsistent with the paper's stated methodology of "counterexample-backed boundaries."

**Required action:** Either (a) add a mechanized `UAndOnEmptyCounterexample` showing a model where `UAndOn_empty_eq_univ` causes a spurious consistency signal if the non-empty check is omitted, or (b) explicitly justify why this case is treated differently from `hproj`-absence and `E ≠ proj` counterexamples.

---

## 4. Minor Issues

**m1. `semanticPullback` motivation is deferred too late (§3.6 preamble).**
The abstract relation `E` is introduced in §3.6 with motivation "separating `proj` from `E` allows theorem-level reasoning before committing to a concrete extractor." This motivation should appear earlier — at minimum in §1.1 or as a named design choice in §2 — because `E` affects how the reader should interpret all adequacy-related claims. As written, a reader of §§1–2 has no indication that an abstract `E` distinct from `proj` will appear.

**m2. `checkConsistent_iff_allThree` scope is unclear (§5.2).**
The PasswordPolicy case study (§5.2) proves equivalence over a "constrained interval domain." The manuscript does not state what `Ω` is in this instantiation, what `carrier` types are used, or how the three layers map to the abstract index type `ι`. A one-sentence instantiation table (similar to the `ArtifactBundleExample` description in §5.1) would make this example self-contained.

**m3. `consistent_transport_left` is listed in the theorem catalog but not discussed in the manuscript.**
`Transfer.lean` exports both `lifted_transfer` and `consistent_transport_left`. The latter appears in the catalog (Appendix `theorem_catalog.md`) but has no corresponding discussion in §3.4 or §4.5 beyond the traceability table. If it is a corollary of `lifted_transfer`, say so; if it is a separate result, give a one-line statement.

**m4. Plural "paper" framing in §0 could confuse single-submission readers.**
§0 describes a "two-paper strategy." If this manuscript is submitted as a standalone to FM/ITP/CPP/TACAS, reviewers will not have access to the engineering paper. §0.2 non-claim 4 says "No claim that behavior of the engineering-paper PoC pipeline is a direct semantic proof of all formal assumptions" — this is good, but the manuscript should also state explicitly that the formal paper is self-contained and does not require the engineering paper for any theorem proof.

**m5. LOC count (§4.4) includes example files.**
"1690 LOC under `paper/lean/UadfU0`" covers the full directory including `Examples/` and `CaseStudy/`. A breakdown (core definitions + theorems vs. examples) would help reviewers assess proof density. This is minor but relevant for CPP-style artifact evaluation.

---

## 5. Required Revision List

| # | Priority | Action |
|---|---|---|
| R1 | Major | Address M1: exhibit concrete Lean-level interface gap where Mathlib reuse breaks for the heterogeneous-carrier/partial-projection combination. |
| R2 | Major | Address M2: resolve `RQ1`/`RQ2` framing inconsistency — either demote to infrastructure or promote to co-equal RQs. |
| R3 | Major | Address M3: consolidate verification steps into a single script; record expected hash values in `build_evidence.md`; clarify "42 jobs." |
| R4 | Major | Address M4: add mechanized vacuous-truth counterexample for `UAndOn_empty_eq_univ` misuse, or justify its omission relative to other counterexamples. |
| R5 | Minor | Address m1: introduce abstract `E` and its motivation in §1 or §2, not first in §3.6. |
| R6 | Minor | Address m2: add instantiation table for PasswordPolicy example (§5.2). |
| R7 | Minor | Address m3: add one-line description of `consistent_transport_left` in §3.4. |
| R8 | Minor | Address m4: add explicit statement that the formal paper is self-contained independent of the engineering paper. |
| R9 | Minor | Address m5: provide LOC breakdown separating core from examples/case-study. |
