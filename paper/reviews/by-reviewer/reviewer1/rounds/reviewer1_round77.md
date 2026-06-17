## Formal-Methods Venue Review — Reviewer #1 (Strictest)

---

### 1. Overall Recommendation

**Major Revision Required — Not Yet Acceptable**

The artifact is substantially complete and the mechanization infrastructure is credible. However, several blocking issues must be resolved before the paper can be accepted at FM/ITP/CPP/TACAS/FASE/Formal Aspects. The core problem is a mismatch between what the paper *claims to contribute* (a novel kernel with explicit assumption interfaces) and what it *actually demonstrates* (a well-engineered formalization of standard set-theoretic identities with a partial-option wrapper). The framing work needed to bridge this gap is non-trivial.

---

### 2. Strengths

1. **Mechanization discipline is genuine.** Zero `sorry`, explicit axiom audits per theorem, and traceability to specific `.lean` files are all exemplary for a library-style FM submission.

2. **Counterexample engineering is a real contribution.** `TransferCounterexample`, `AdequacyCounterexample`, `TotalizationCounterexample`, and the failure-mode witnesses make the assumption matrix *executable*, not just documentary. This is exactly what ITP/CPP reward.

3. **Assumption matrix + theorem catalog.** The appendix structure (`assumption_matrix.md`, `theorem_catalog.md`, `reproduce_formal.sh`) meets or exceeds artifact standards for CPP/FASE.

4. **Partiality discipline is correctly handled.** The must/may split, `UAndOn_empty_eq_univ` vacuous-truth trap, and `no_left_adjoint_of_partial` guardrail are all correctly identified as non-trivial under `Option`-based projections. The paper is right that totalization can introduce spurious witnesses.

5. **Role-separation transparency.** The §4.6 breakdown (15 primary / 34 supporting / 25 example) and the explicit non-claim list (§0.2) demonstrate self-awareness that is atypical and valuable.

---

### 3. Major Concerns (Blocking)

#### M1. Novelty claim is insufficiently operationalized — the "delta" argument is circular

Section 6.1 argues that the delta over Mathlib-style baseline is "explicit assumption-interface design + mechanized boundary auditing." But this argument is almost entirely self-referential: the paper claims novelty because it makes things explicit that others leave implicit. That is a valid *methodological* contribution, but it needs a concrete falsifiability test.

**Required:** Identify at least one theorem in this kernel whose *statement* cannot be directly derived by instantiating a Mathlib API (e.g., `GaloisConnection`, `Set.preimage_mono`, `Order.Frame`). The paper currently gestures at this (§6.1, bullet 2–5) but does not provide a formal delta proof. For CPP/ITP, reviewers will ask: could this kernel be reproduced in ~200 lines of Mathlib? If yes, the contribution reduces to "we did it without Mathlib," which is a reproducibility choice, not a scientific contribution.

Concretely: the `preimage_compose` theorem under `Option.bind` is the strongest candidate. The paper should state precisely what Mathlib theorem it *does not reduce to* and why, with a proof sketch or a pointer to a failed Mathlib instantiation attempt.

#### M2. RQ framing does not match the actual theoretical contribution

The five RQs read like engineering validation questions, not research questions at FM/ITP level. "Can we define X consistently?" and "Can Y be typed without hidden assumptions?" are not research questions — they are design validation checks.

**Required:** Either (a) reframe as a single *theorem-level* claim ("Theorem T is provable in this model but not in prior model M under the same interface"), or (b) explicitly adopt the "library paper" / "tool paper" track framing used at CPP, and restructure the abstract/introduction accordingly. The current hybrid is unconvincing to venue reviewers.

#### M3. The `UStar` linkage section (§3.8) is formally vacuous as presented

`UStar` is a parameter with no construction obligation. The theorems in `IdealRoot.lean` say: "if `UStar` satisfies P, then inclusion Q follows." This is tautological at the level stated — it is just universal quantification over predicates satisfying a hypothesis. The paper acknowledges this ("conditional linkage theorems rather than a construction of `UStar`") but does not explain why the conditional form is *useful* rather than trivially true.

**Required:** Either (a) provide a non-trivial instance where `UStar` satisfies the hypothesis and the conclusion is non-obvious, or (b) remove `UStar` from primary results and relegate it entirely to "proof-obligation templates." As it stands it weakens the primary-theorem count artificially.

#### M4. Related work section does not engage with the closest prior work

§7 lists standard references but does not engage with:

- **Siek & Taha (2006) gradual typing** and its Option/partiality handling — directly relevant to must/may split and undefined-observation semantics.
- **CASL/Common Algebraic Specification Language** partial-function handling — this paper reinvents partial-algebra preimage composition from scratch and does not acknowledge it.
- **Event-B partial functions and guard conditions** — the `hcomm` assumption in `preimage_compose` is structurally similar to well-definedness conditions in Event-B.

**Required:** Add 2–3 paragraphs situating the kernel's partial-function handling against these lines. The non-adjointness result in particular must be compared to known non-existence results in CASL-style partial-algebra semantics.

#### M5. Reproducibility contract is underspecified for the venue

The current reproducibility claim is "same manifest + same Lean toolchain + same script revision." For FM/TACAS artifact evaluation, this is insufficient:

- The `reproduce_formal.sh` script calls `lake clean` + `lake build` but does not verify the *output* beyond `Build completed successfully`. A broken build that produces a `sorry`-free but semantically wrong compilation would pass.
- The hash check covers `lake-manifest.json` and `lean-toolchain` but the Lean source files themselves are not hashed.
- The Dockerfile uses `ubuntu:24.04` with `apt-get` (non-pinned package versions), making the container non-reproducible over time.

**Required:** (a) Add source-file hash verification to `reproduce_formal.sh`, (b) pin all apt packages in `Dockerfile.fm` with exact version strings, (c) clarify whether artifact evaluation requires network access (elan downloads toolchain at container build time — this may fail in air-gapped evaluation environments).

---

### 4. Minor Concerns

#### m1. Axiom audit is incomplete for primary theorems

The axiom audit in §4.3 lists axioms for 6 selected theorems. For a CPP/ITP submission, *all 15 primary theorems* should have their `#print axioms` output recorded. The asymmetric coverage raises the question: do the unlisted theorems have unexpected axiom dependencies?

#### m2. Theorem count inflation from `example` declarations

The paper counts `74` theorem declarations. `Examples/TwoLayer.lean` is listed as having 0 theorem declarations ("example declarations only"). Are `example` declarations in *other* files excluded consistently? The counting methodology should be stated as a grep/rg command reproducible by reviewers, not just a prose claim.

#### m3. §0 "Scope, Split, and Quality Bar" is editorially inappropriate in a submission

This section reads as author self-assessment ("theorem novelty is modest by design"). While the intent (honesty about scope) is admirable, framing like "methodology/library-style formalization tracks where X and Y are valued as first-class results" tells the PC chair which track to route the paper to, which is not the author's role. Rename or restructure as a "Paper Organization" section.

#### m4. LaTeX math rendering will be broken

The manuscript uses `\[...\]` display math and `$...$` inline math inconsistently, and several formulas use non-standard Unicode (e.g., `α`, `β`, `ι` in code blocks mixed with LaTeX). Venue submissions require consistent `.tex` source. The `.md` format here is not submission-ready.

#### m5. The password-policy case study (§5.2) is trivial

Three interval constraints with identity projections is not a meaningful case study for FM/ITP. The constraint `req: minLen ≤ n ≤ maxLen, api: minLen ≤ n, code: n ≤ maxLen` is a textbook intersection example. Either (a) replace with a non-trivial case (e.g., a protocol state machine with heterogeneous carrier types), or (b) explicitly label it as a "warm-up example" and not a "case study."

#### m6. `Classical.choice` in `preimage_compose` should be eliminated or justified

The paper notes that a constructivity-preserving re-proof is "outside this scope." For ITP/CPP where constructive foundations matter, this is a significant omission. At minimum, add a remark explaining *why* the proof style forces `Classical.choice` here (is it the witness-reconstruction step?) and whether an `Option.casesOn`-based proof would avoid it.

#### m7. Missing forward reference for `PasswordPolicy.lean` in the theorem-catalog file listing

`theorem_catalog.md` lists `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` but the main manuscript §5.2 refers to it. The appendix is consistent, but there is no corresponding entry in the `reproduce_formal.sh` traceability checks for `checkConsistent_iff_allThree`. Add it.

---

### 5. Required Revision Checklist

| # | Item | Blocking? | Section |
|---|---|---|---|
| R1 | Provide a concrete non-reducibility argument showing `preimage_compose` or `lifted_transfer` cannot be derived by direct Mathlib instantiation | Yes (M1) | §6.1 |
| R2 | Reframe RQs as theorem-level claims or adopt explicit library/tool-paper track framing | Yes (M2) | §1.3, Abstract |
| R3 | Either provide a non-trivial `UStar` instance or remove `UStar` from primary results | Yes (M3) | §3.8, §4.6 |
| R4 | Add 2–3 paragraphs on CASL partial functions, gradual typing, and Event-B guard conditions | Yes (M4) | §7 |
| R5 | Add Lean source-file hash verification to `reproduce_formal.sh` | Yes (M5) | §9, appendix |
| R6 | Pin apt package versions in `Dockerfile.fm`; document network requirements | Yes (M5) | appendix |
| R7 | Record `#print axioms` output for all 15 primary theorems | No (m1) | §4.3 |
| R8 | Make theorem-count methodology reproducible via explicit rg/grep command | No (m2) | §4.6, catalog |
| R9 | Rename/restructure §0 to remove author self-assessment tone | No (m3) | §0 |
| R10 | Convert manuscript to `.tex` with consistent math formatting | No (m4) | — |
| R11 | Replace or relabel password-policy case study | No (m5) | §5.2 |
| R12 | Justify or eliminate `Classical.choice` in `preimage_compose` | No (m6) | §4.3 |
| R13 | Add `checkConsistent_iff_allThree` to `reproduce_formal.sh` traceability checks | No (m7) | appendix |

---

**Summary judgment:** The mechanization artifact is solid and the assumption-discipline philosophy is sound. The paper is not ready because (M1) the novelty argument is self-referential, (M2) the RQ structure does not fit FM venue norms, (M3) the `UStar` section is logically vacuous, (M4) closest related work is missing, and (M5) the reproducibility contract has concrete gaps. None of these are fatal — all are addressable in a major revision.
