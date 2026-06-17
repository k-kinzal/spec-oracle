# Formal-Methods Paper Review: UAD/f Two-Operator Kernel under Partial Projections

**Reviewer #1 (Strictest)**
**Target venues: FM / ITP / CPP / TACAS / FASE / Formal Aspects**

---

## 1. Overall Recommendation

**Major Revision** (borderline reject at top-tier FM/ITP/CPP; conditional accept possible at FASE/Formal Aspects with revisions addressed)

The mechanization appears technically sound and the assumption-audit methodology is a genuine engineering contribution. However, the paper has significant problems with novelty positioning, scope of contribution versus claim, and traceability gaps that would cause rejection at FM, ITP, or CPP. The paper is better positioned for FASE or Formal Aspects, where methodology papers with modest but careful formal contributions are accepted—but even there, the issues below must be addressed.

---

## 2. Strengths

1. **Assumption-explicit methodology is genuine.** Making `hproj`, `hA`, and `hcomm` explicit theorem arguments (rather than prose) is a real methodological improvement over informal multi-layer specification literature. The assumption matrix (Appendix B) is well-structured and directly checkable.

2. **Counterexample mechanization is sound practice.** Providing `transfer_fails_without_hproj`, `AdequacyCounterexample`, and `ContradictoryLayers` as executable proof artifacts—not prose—is the correct approach. This distinguishes the work from typical specification papers.

3. **`#print axioms` disclosure is thorough.** Explicitly auditing axiom footprints per theorem (§4.3, items 6–10) and explaining the asymmetry between `lifted_transfer` (no axioms) and `preimage_compose` (Classical.choice) is precise and commendable.

4. **`UAndOn_empty_eq_univ` vacuous-truth warning is operationally important.** Calling this out as a mechanized requirement (not just a prose caveat) is the right level of rigor.

5. **Reproducibility infrastructure is concrete.** The `reproduce_formal.sh` script with hash-locked manifest, `sorry` count check, and core-theorem membership check is an appropriate artifact contract. The scope limitation ("same manifest + toolchain, not CI replay") is honestly stated.

6. **Must/may split is correctly motivated.** The policy-sensitivity argument (§2.6, §3.6.2) for why `semanticPullbackMay` must include the `proj=none` branch is technically correct and not obvious.

---

## 3. Major Concerns (Blocking)

### M1. Novelty claim is under-argued relative to FM/ITP/CPP standards

The paper explicitly acknowledges in §6 that "theorem identities are mostly classical" and the contribution is "interface-level and methodological." This honest framing is correct but creates a positioning problem: the paper does not sufficiently argue why this particular combination—heterogeneous carriers + Option-partiality + assumption auditing—requires *new proof ideas* that were not already available through Mathlib instantiation or a straightforward Lean port of known categorical results.

**Specific deficiency:** §6.1 lists five "what this kernel adds" bullets, but none of them argues that the *proofs themselves* required novel proof techniques. The paper must either:
- (a) Demonstrate a specific proof step in `preimage_compose` or `lifted_transfer` where the `Option` partiality creates a structurally new proof obligation (not just "we had to discharge an extra branch"), or
- (b) Explicitly reframe the contribution as a *library design* paper (suitable for CPP's library track) rather than a *theorem* paper.

Currently the paper tries to claim both and fully satisfies neither.

### M2. The `UStar` section (§3.8) is structurally disconnected from the main RQ framework

`UStar` is declared a "supporting conditional linkage" contribution, but the paper devotes substantial space to six theorems around it and includes it in the supporting-lemma count of 33. The problem: `UStar` is an *uninstantiated parameter*. Theorems of the form "if `UStar ⊆ lifted(i)` for all active `i`, then `UStar ⊆ UAndOn(active)`" are set-theoretically trivial by unfolding definitions. The paper does not argue why these conditional linkage theorems have non-obvious proofs or why mechanizing them adds value beyond stating them as definitions.

**Required fix:** Either (a) remove the `UStar` section from the main paper and relegate it to an appendix as a "parametric template," or (b) provide a concrete instantiation where `UStar` is given meaning and the domain-restriction step (global vs. `projDomOn`) makes a non-trivial difference that would be missed without mechanization.

### M3. The five RQs are not all answered at the same level of rigor

The paper states "Primary RQs for this formal paper are RQ3, RQ4, and RQ5" and demotes RQ1/RQ2 to "supporting." However, the resolution policy for RQ1 (§1.3) states it is "resolved when heterogeneity is carried through theorem statements without universe/typing collapse." This is a *meta-claim about Lean elaboration*, not a theorem. There is no formal artifact that witnesses RQ1's resolution in the same way that, say, `lifted_transfer` witnesses RQ4.

**Required fix:** Either remove RQ1/RQ2 from the formal claim list (since they are typing artifacts, not theorems), or provide a named Lean `example` or `theorem` that explicitly instantiates the model with two layers of different `carrier` types and verifies that the same `lifted_transfer` theorem applies, thereby demonstrating heterogeneity is not just definitional but operational.

### M4. Traceability matrix (Table 1.5) references files not listed in §9's artifact package

The RQ-to-theorem matrix in §1.5 cites `paper/lean/UadfU0/Definitions/Model.lean` and `paper/lean/UadfU0/U0Spec/Construction.lean` for RQ1. But the reproduce script and §9 artifact list do not include `Definitions/` as a separately reproducible unit with hash verification. A reviewer cannot verify the cited file content matches the claimed theorem names without running the full build.

**Required fix:** Either (a) add per-file SHA256 hashes for the key source files cited in the traceability matrix to `build_evidence.md`, or (b) add a `reproduce_formal.sh` step that explicitly checks for `mem_preimage_iff` in the expected file path using `rg`, analogous to the existing core-theorem membership check.

### M5. The non-adjointness theorem (§3.7) is classified as "not standalone mathematical novelty" but occupies a full section with RQ-level framing

The paper is internally inconsistent: §3.7 is listed in the core-theorem count (16 theorems, where `no_left_adjoint_of_partial` is explicitly listed), yet the prose says it is "not claimed as standalone mathematical novelty" and is "a mechanized guardrail." If it is a guardrail, it should be in the supporting-lemma count. If it is core, the novelty claim must be substantiated.

**Concretely:** The proof in §3.7 is a simple contradiction from a singleton instantiation of an assumed left adjoint. This is a routine exercise. Classifying it as a "core theorem" inflates the core count. The paper should either:
- Demote it to supporting (and update all counts in §4.6), or
- Argue why this specific proof in the partial-projection setting requires an insight not present in, e.g., Darais & Van Horn (2016) [Ref 11].

### M6. Build evidence is a single self-reported local run with no external validation

The `build_evidence.md` records "one reproducible local run." At FM/ITP/CPP, artifact evaluation typically requires either a CI/CD log from a public repository or a Docker/Nix environment specification. The claim "reproducibility scope is 'same manifest + same Lean toolchain + same script revision', not bit-identical CI/container replay" is honest but insufficient for artifact evaluation at those venues.

**Required fix for FM/ITP/CPP submission:** Add a `Dockerfile` or `flake.nix` that pins the exact Lean version and elan channel, and runs `reproduce_formal.sh` as its entrypoint. For FASE/Formal Aspects, the current level may suffice if the artifact is publicly accessible.

---

## 4. Minor Concerns

### m1. Password policy case study (§5.2) is underspecified as a "case study"

The `checkConsistent_iff_allThree` theorem is stated to be about "a closed-form consistency check equivalent to existence of shared witness across three lifted layers." But the paper does not state what the domain (`β_i`), admissibility predicates (`A(i)`), and projections (`proj_i`) are for the password policy model. Without this, a reviewer cannot assess whether this is a meaningful domain application or a toy. The file reference `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` is not included in the files provided for review.

### m2. The `semanticPullback` vs `preimage` distinction (§3.6) could be sharpened

The motivation for introducing abstract relation `E` separate from `proj` is correct, but the paper's example (`EPlus1`) uses an artificially shifted numerical relation. A more convincing example showing where this matters in practice (e.g., a regex extractor that normalizes representations) would strengthen the must/may adequacy section.

### m3. Reference list has gaps for the mechanization context

The paper cites Darais & Van Horn [11] for Galois connections and Mathlib [12] for comparison, but does not cite:
- Sozeau & Tabareau's mechanization of setoid/quotient types in Coq (relevant to `funext`/`propext` usage patterns)
- Any prior Lean4 mechanization of specification semantics (e.g., work from the Lean4 community on order theory beyond Mathlib)

This is not a blocking concern but weakens the related-work positioning.

### m4. The `UAndOn_antitone` theorem name should clarify the monotonicity direction

The theorem is listed as "core" but the paper's English description (§3.3, item 2) says "active-layer expansion has opposite monotonicity effects." `antitone` in Lean/Mathlib means `∀ a ≤ b, f b ≤ f a` on ordered types. The paper should state the exact order on active-set predicates (set inclusion `⊆` on `ι → Prop`) used in the theorem signature, since this is not the standard lattice-indexed order and may confuse readers familiar with Mathlib's `Antitone`.

### m5. LOC count (1703) is cited informational but not contextualized

1703 lines for 72 theorems is ~24 lines/theorem average. For a Lean4 formalization this is reasonable, but FM/ITP reviewers may want to know whether this includes comments, blank lines, and definition/notation overhead, or only proof lines. A brief breakdown (e.g., definitions: ~N lines, proofs: ~M lines) would help assess proof complexity.

---

## 5. Required Revision Checklist

Items marked **[Blocking]** must be resolved before any top-tier FM/ITP/CPP submission. Items marked **[Required for FASE/Formal Aspects]** are blocking for those venues. Items marked **[Recommended]** improve the paper but are not blocking.

| # | Item | Severity |
|---|---|---|
| R1 | Reframe or substantiate novelty claim: either demonstrate a structurally new proof step required by partiality, or explicitly reposition as a library/methodology contribution. | **[Blocking]** |
| R2 | Resolve the `UStar` structural disconnect: remove from main text or provide a concrete non-trivial instantiation. | **[Blocking]** |
| R3 | Fix RQ1/RQ2 resolution policy: provide a named Lean artifact (theorem or example) that operationally witnesses heterogeneous-carrier reuse, or remove RQ1/RQ2 from formal claim list. | **[Blocking]** |
| R4 | Add per-file SHA256 hashes or `rg`-based existence checks for files cited in the traceability matrix to `reproduce_formal.sh` / `build_evidence.md`. | **[Blocking]** |
| R5 | Resolve `no_left_adjoint_of_partial` classification: demote to supporting (update all counts in §4.6) or substantiate why it is core-level novelty relative to [Ref 11]. | **[Blocking]** |
| R6 | Add container reproducibility (Dockerfile or Nix flake) for FM/ITP/CPP artifact track. | **[Required for FASE/Formal Aspects]** |
| R7 | State the domain/admissibility/projection definitions for the PasswordPolicy case study in the main text, not only by file reference. | **[Required for FASE/Formal Aspects]** |
| R8 | State the exact order on `ι → Prop` used in `UAndOn_antitone` signature. | **[Recommended]** |
| R9 | Add a prose or code example where `E ≠ graph(proj)` arises from a realistic extractor scenario (not only the artificial `EPlus1` shift). | **[Recommended]** |
| R10 | Add missing related-work citations for Lean4 mechanization of order-theoretic structures. | **[Recommended]** |

---

**Summary judgment:** The mechanization is technically credible and the assumption-audit methodology has genuine value. The paper is not ready for FM/ITP/CPP as submitted due to the novelty-framing gap (M1), structural disconnection of `UStar` (M2), and traceability/reproducibility gaps (M4, M6). With the blocking items addressed, the paper has a reasonable chance at **FASE** or **Formal Aspects of Computing**. FM/ITP/CPP would additionally require the novelty argument to be substantially strengthened or the venue to be matched to a methodology/library track rather than a theorem track.
