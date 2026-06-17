## Review of "UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization"

**Reviewer #3 | Formal Methods Track (FM/ITP/CPP/TACAS/FASE/Formal Aspects)**

---

## 1. Overall Recommendation

**Weak Reject / Major Revision Required**

The paper presents a mechanized Lean4 kernel for multi-layer specification comparison under partial projections. The artifact appears technically sound (no `sorry`, 74 theorems, reproducible build), and the authors are admirably honest about scope limitations. However, the paper's primary contribution remains underdeveloped as a *research claim*. It reads more like a well-engineered library artifact than a paper making a defensible scientific argument. With substantial restructuring of the contribution framing and resolution of the blocking concerns below, this could be suitable for a methodology/library track at ITP or CPP.

---

## 2. Strengths

1. **Assumption-explicit interface discipline.** The systematic surfacing of `hproj`, `hA`, and `hcomm` as explicit theorem arguments, backed by mechanized failure witnesses (`transfer_fails_without_hproj`, `naive_totalization_adds_spurious_witness`), is the paper's clearest and most defensible contribution.

2. **Honest scope control.** The non-claims section (§0.2), the 8-item limitations section (§8), and the careful "classical overlap vs. mechanization-specific value" separation (§6) demonstrate uncommon intellectual honesty. Reviewers benefit enormously from this transparency.

3. **Must/may split with policy motivation.** The explicit `Option`-first treatment, the non-adjointness guardrail (§3.7), and the `preimageMay` family are coherent engineering choices that are motivated and mechanized.

4. **Counterexample completeness.** All four counterexample files cover meaningfully distinct failure modes (missing `hproj`, `E ≠ proj`, totalization, vacuous meet), which collectively validate the non-triviality of the theorem interfaces.

5. **Reproducibility infrastructure.** The hash-pinned `reproduce_formal.sh`, `Dockerfile.fm`, assumption matrix, and theorem catalog constitute a thorough artifact package that exceeds typical FM paper standards.

---

## 3. Major Concerns (Blocking)

### M1. The "contribution" and "novelty" claims are insufficiently argued

The paper repeatedly hedges novelty ("modest by design", "not a claim of novel algebraic identities", "mostly classical"), but never completes the argument for why the paper is *interesting* beyond being a well-typed Lean library.

**The core question a reviewer must be able to answer: what would a researcher who reads this paper know or be able to do that they could not do before?**

The current answer appears to be: "they have a typed partial-projection kernel with explicit assumption interfaces." But this is a description of an artifact, not a scientific contribution. The paper needs to argue one of:
- (a) This kernel design pattern is *transferable* and shows how to build similar audited kernels for other multi-layer frameworks; or
- (b) The mechanization exposed a *non-obvious* difficulty (e.g., a proof attempt that failed before the explicit interface was added); or
- (c) The kernel is *practically useful* as a substrate and some real system benefits from instantiating it.

None of (a)-(c) is argued convincingly. §6 ("What Mechanization Added Beyond Textbook Identities") is the right section for this but currently reads as a checklist rather than a scientific argument.

**Required action:** Add a focused ~0.5-page argument in §6 or a new §6.2 that answers the above question with concrete evidence. A single worked non-trivial proof attempt that *required* explicit interface redesign would suffice for (b).

### M2. RQ1/RQ2 resolution policy is stated but not evaluated

§1.3 states resolution policies for RQ1 and RQ2, but §1.5 and §3 never verify these policies are *actually satisfied*. The RQ-to-theorem table (§1.5) points to theorems, but does not demonstrate that heterogeneity is "carried through theorem statements without universe/typing collapse" (the RQ1 resolution criterion) or that `A(i) ⊆ D(i)` is "consumed as witness-validity infrastructure in later theorems" (the RQ2 resolution criterion).

The reader is told these questions are "resolved" but must trust the claim without a direct check. Given the paper's own emphasis on explicit assumption auditing, this is inconsistent.

**Required action:** For each RQ1/RQ2, add a 3-5 sentence proof sketch demonstrating that the resolution criterion is met. For RQ1, show explicitly where `carrier : ι -> Type` appears in a transfer or composition theorem signature. For RQ2, show the chain from `admissible_subset_domain` through `lifted_subset_preimage_domain` to a later theorem.

### M3. The relationship between the formal kernel and the stated motivation is never formally established

§1.1 motivates the work with the problem of cross-layer comparison when "ideal complete root specification `U*` is usually unavailable." The proposed solution is to "construct root-side operators from partial projections." But the paper never formally states what *problem* the kernel *solves* — i.e., what property a user of this kernel gains over a user who has no such kernel.

The ideal-root linkage theorems (§3.8) come closest, but they are conditional on `UStar` as a parameter. There is no theorem that says, in effect: "given only partial projections `{proj_i}`, operator `U0` serves as a sound approximation of `U*` in the following sense."

**Required action:** State and prove (or explicitly acknowledge as open) a theorem connecting `U0` to `U*` under some natural sufficient condition. If this is genuinely outside scope, say so explicitly in §0.2 and explain why the kernel is still useful without it.

### M4. Related work is thin on mechanized multi-view consistency literature

§7 covers abstract interpretation, institutions, BX, and Galois connections but omits directly relevant mechanization work:
- Mechanized multi-view consistency in Isabelle (e.g., Brucker/Wolff on Formal Cartesian Products of Views)
- ViewPoint weaving formalized in theorem provers
- Mechanized contract languages (JML/Frama-C verification lines) where assumption interfaces for layer transfer are explicit

The "definition-level differences" paragraphs in §7.2–§7.5 are good but presuppose the reader knows these related lines well. Without citations to specific mechanized implementations, the claims of differentiation are not verifiable.

**Required action:** Add 2-3 citations to directly mechanized multi-view or multi-layer consistency work and update the differentiation arguments to reference specific theorem/definition names from those works.

---

## 4. Minor Concerns

### m1. Section 0 length vs. content density mismatch

§0 (Scope, Split, Quality Bar) is 6 subsections covering 5+ pages worth of framing. Much of this material belongs in §1 or §4. The abstract itself is reasonably crisp; §0 undercuts this by over-qualifying before any technical content appears. Consider merging §0.1–§0.3 into §1 and cutting §0.

### m2. `UAD/f` vs. `UDA/f` inconsistency

The title uses "UAD/f" but `docs/conversation.md` (referenced in CLAUDE.md) uses "UDA/f". The paper acknowledges this is a "local name" (§0, Terminology note) but does not explain why the ordering changed. A footnote clarifying the ordering choice would prevent confusion.

### m3. `semanticPullback` motivation could be tightened

§3.6 introduces `E` as separate from `proj` with a 4-point motivation, but the practical `E ≠ graph(proj)` case is buried in a sub-bullet. The `EPlus1` model (offset-by-one extractor) is described but never given a sentence explaining what real-world scenario it models. This makes the counterexample feel arbitrary. One sentence connecting `EPlus1` to a concrete extractor failure mode (e.g., off-by-one in a regex capture group) would help.

### m4. Axiom audit is incomplete

§4.3 audits 6 selected theorems but not all 15 primary theorems. The paper states primary theorem set in §4.6 — the axiom audit should cover all 15, or explicitly state why the 6 selected are representative and axiom footprints of the remainder are implied.

### m5. `lake-manifest.json` is empty but not explained contextually

§2.1 mentions "packages: []" with a brief design-choice note, but this is architecturally significant. Readers unfamiliar with Lake will not understand that this means *zero* external Lean dependencies. A one-sentence clarification ("no Lean packages beyond the Lean4 core are imported") would prevent confusion with a misconfigured manifest.

### m6. LOC count (1807) appears in §4.4 without context

1807 lines for 74 theorems is ~24 lines/theorem average. Without context this number is hard to evaluate. A brief note on file-size distribution (e.g., "X lines are definitions, Y lines are proofs, Z lines are examples") would help readers calibrate artifact density.

### m7. The paper claims "Mathlib-free" but uses `propext`, `Classical.choice`, `Quot.sound`

These are Lean4 kernel axioms, not Mathlib, so the claim is technically correct. But a reader skimming §4.3 may conflate "Lean kernel axioms" with "Mathlib axioms." Sentence: "These are Lean4 kernel axioms, not Mathlib imports" should appear immediately when `Classical.choice` is first mentioned.

---

## 5. Required Revision Checklist

**Blocking (must be resolved before acceptance):**

- [ ] **M1.** Add substantive argument in §6 for the paper's contribution beyond artifact description: either a proof-design lesson, a transferable pattern, or a practical use case with evidence.
- [ ] **M2.** For RQ1 and RQ2, provide explicit 3-5 sentence proof sketches demonstrating that the stated resolution criteria are satisfied in the mechanization.
- [ ] **M3.** State and prove (or explicitly scope-exclude in §0.2 with justification) a theorem connecting `U0` to `U*` under natural sufficient conditions, addressing the "why does the kernel solve the motivation problem" gap.
- [ ] **M4.** Add 2-3 citations to mechanized multi-view or multi-layer consistency work and update §7 differentiation arguments accordingly.

**Non-blocking (expected for final version):**

- [ ] **m1.** Restructure §0 — merge into §1 or cut; move framing content closer to where it is needed.
- [ ] **m2.** Add footnote explaining UAD/f vs. UDA/f ordering.
- [ ] **m3.** Add one sentence connecting `EPlus1` to a concrete extractor failure scenario.
- [ ] **m4.** Extend axiom audit to all 15 primary theorems or justify why the 6 selected are representative.
- [ ] **m5.** Clarify "packages: []" means zero external Lean dependencies.
- [ ] **m6.** Add context for LOC count (definition/proof/example breakdown).
- [ ] **m7.** Clarify that `propext`/`Classical.choice`/`Quot.sound` are Lean4 kernel axioms, not Mathlib imports, at first mention in §4.3.
