# Formal-Methods Venue Review — Reviewer #1 (Strictest)

---

## 1. Overall Recommendation

**Major Revision**

The mechanization artifact appears internally consistent and the assumption-auditing methodology is a legitimate contribution. However, the submission has significant weaknesses in novelty positioning, scope of the formal claim bundle, and missing details that block acceptance at FM/ITP/CPP-tier venues.

---

## 2. Strong Points

**SP1. Assumption-explicit theorem signatures.** The explicit surfacing of `hproj`, `hA`, `hcomm`, and sound/complete obligations as named theorem arguments (rather than prose assumptions) is methodologically sound and useful. The assumption matrix (appendix) is well-structured.

**SP2. Mechanized counterexamples.** `TransferCounterexample.lean` and `AdequacyCounterexample.lean` do real work: they demonstrate that the named hypotheses are not vacuous. This is good practice and strengthens formal credibility.

**SP3. Axiom audit (§4.3).** Per-theorem `#print axioms` disclosure is commendable and rarely done this carefully in venue submissions.

**SP4. Must/may separation.** The explicit `Option`-based partiality with separate must-side (`preimage`) and may-side (`preimageMay`) theorem families is a principled design choice, and the policy-sensitivity argument (§3.3) is coherent.

**SP5. RQ-to-theorem traceability matrix (§1.5, §4.5).** The two-table traceability structure is a genuine quality signal.

---

## 3. Major Concerns (Must-Fix)

**MC1. Novelty claim is under-supported relative to the abstract.**

The abstract promises "a formal-methods contribution" but §6 ("What Mechanization Added Beyond Textbook Identities") explicitly concedes that the mathematical content is largely classical: inverse-image monotonicity, LUB/GLB identities, contradiction/non-consistency duality. The actual novelty claim collapses to: *"this specific typed kernel is packaged and machine-checked end-to-end."* That is a mechanization contribution, not a formal-methods result. For FM/ITP/CPP/TACAS, a packaging contribution of 1690 LOC requires either (a) a theorem that is technically non-trivial to prove in Lean (e.g., required novel tactics, a dependent-type encoding challenge), or (b) a negative result with broader implications than a local guardrail. Neither is demonstrated.

The manuscript must either (a) identify one theorem whose Lean encoding required a non-trivial technical insight beyond library application, or (b) reposition the submission explicitly as a verified-infrastructure paper and argue why that category deserves acceptance at a formal-methods venue.

**MC2. `no_left_adjoint_of_partial` (§3.7) is explicitly disclaimed as non-novel but still presented as a headline result.**

§3.7 states: *"It is not claimed as standalone mathematical novelty."* Yet it appears in the main theorem body, in §6's per-theorem hardness summary, and in §7.5's related-work positioning. This inconsistency will confuse reviewers. The theorem's proof sketch (5 steps using a trivial instantiation of the adjunction) is elementary. Either elevate this to a result with consequences (e.g., connect to implications for governance workflow correctness) or demote it to a supporting lemma and remove headline treatment.

**MC3. RQ-to-theorem mapping for RQ1 and RQ2 is underspecified.**

§1.3 marks RQ1 and RQ2 as "supporting questions," then §3.1 and §3.2 answer them with foundational lemmas listed as "not novelty claims." The RQ framework then effectively reduces to three primary RQs (RQ3–RQ5). But RQ3's answer ("join/meet separation") is proved by the monotonicity/antitone pair, which is standard order theory. RQ4's answer (`lifted_transfer`, `preimage_compose`) is non-trivial under partiality but the proof sketch in §3.4–§3.5 is short (5–6 steps each). RQ5's answer (adequacy decomposition into sound/complete) is definitionally almost immediate once `semanticPullback` is defined. The manuscript must demonstrate that these RQ answers constitute *research contributions* at the theorem level, not just useful infrastructure.

**MC4. The `semanticPullbackMay` `none`-branch policy (§3.6.2) is not formally characterized.**

§3.6.2 states that including `proj_i(x) = none` in `semanticPullbackMay` is "an operational comparability choice." But no theorem characterizes what happens when different layers use different none-policies (one must, one may). The interaction between must- and may-side operators across layers under mixed policies is left entirely to prose. For a paper claiming to be assumption-explicit, this gap is significant: a reviewer can construct a scenario where `UAndOn` (must-side) and `UAndMayOn` (may-side) give contradictory layer-consistency verdicts with no theorem boundary flagging the mismatch.

**MC5. The `UStar` ideal-root section (§3.8) is parametric to the point of vacuity.**

`UStar` is an explicit parameter — it is never constructed, constrained, or grounded. The headline theorem `UStar_inter_projDomOn_subset_UAndOn` is then conditional on `hNecessaryOnDom`, which is an assumption that `UStar` already agrees with each lifted layer on the projection domain. This is close to assuming the conclusion. The paper must clarify what non-trivial content these theorems provide beyond restating their own hypotheses in set-inclusion form. Alternatively, the section should be demoted to a remark or moved to an appendix.

---

## 4. Minor Concerns

**mC1. §2.1 design choice for empty `packages: []`.**
The decision to avoid Mathlib is principled, but it means that 1690 LOC re-proves infrastructure available in Mathlib in 10–20 lines. The paper acknowledges this tradeoff but does not quantify the re-proof burden. A table of "Mathlib API we would use if imported vs. our local equivalent" would clarify the scope.

**mC2. Theorem count inflation from examples and trivial declarations.**
The theorem catalog shows that of 70 theorem declarations, at least 16 are in `Examples/` files and 3 (`subset_refl`, `subset_trans`, `set_ext`) are in `Definitions/Model.lean` as local re-proofs of standard facts. The headline "70 theorems" overstates the core theoretical content. Separate counts by role category (as promised in §4.6 but not actually provided numerically) would improve transparency.

**mC3. §5.2 `PasswordPolicy.lean` case study is described but not linked to a formal research question.**
`checkConsistent_iff_allThree` is presented as a "mechanized sanity theorem" but it does not appear in the RQ-to-theorem matrix. If it is not evidence for any claim, it should be removed or its evidentiary role stated.

**mC4. Reference list is thin for the target venues.**
11 references is sparse for FM/ITP/CPP. In particular: no citation to Coq/Isabelle/Agda mechanizations of similar preimage/Galois structures (e.g., Affeldt et al. on partial functions in Coq, or Nipkow/Paulson Galois connection mechanizations). Related-work §7 should cite directly comparable mechanization papers, not only conceptual prior work.

**mC5. Build evidence (appendix `build_evidence.md`) is a snapshot, not reproducible CI.**
The file records `~/.elan/bin/lake build` output but does not provide a Nix flake, Docker image, or GitHub Actions workflow. FM/TACAS artifact evaluation increasingly requires pinned-environment reproducibility. "Manifest hash check" via Python is a start but not sufficient.

**mC6. §0.2 Non-claim 4 creates ambiguity.**
"No claim that PoC behavior is a direct semantic proof of all formal assumptions" — the phrase "PoC behavior" is undefined in the manuscript. If this refers to engineering-paper artifacts, say so explicitly. As written, a reviewer may wonder whether there is unreported empirical evidence being quietly disclaimed.

---

## 5. Required Revisions Checklist

- [ ] **[MC1]** Identify at least one theorem or encoding whose Lean proof required a technically non-trivial insight (not just applying standard tactics); describe that insight explicitly. If none exists, reposition the contribution as verified infrastructure and argue for that category at the target venue.
- [ ] **[MC2]** Resolve inconsistency around `no_left_adjoint_of_partial`: either (a) elevate by connecting to a broader consequence (e.g., governance workflow soundness), or (b) demote to supporting-lemma status and remove from §3's main theorem body and §6's per-theorem hardness summary.
- [ ] **[MC3]** For RQ3–RQ5, provide explicit argumentation for why each answer constitutes a *research contribution* beyond a useful infrastructure component. This may require adding a "difficulty" subsection per RQ or expanding §6 with concrete proof-engineering challenges.
- [ ] **[MC4]** Add a theorem (or explicit remark with a formal counterexample) characterizing what happens under mixed must/may layer policies. Alternatively, explicitly state as a limitation in §8 with a falsifying scenario.
- [ ] **[MC5]** Either (a) constrain `UStar` non-trivially (e.g., require it to be derived from a specific class of sources) and prove a non-vacuous consequence, or (b) demote §3.8 to an appendix remark and remove it from the main theorem contribution list.
- [ ] **[mC2]** Provide theorem counts broken down by role (core, supporting, example) as promised in §4.6, with actual numbers.
- [ ] **[mC3]** Either add `checkConsistent_iff_allThree` to the RQ traceability matrix with a stated evidentiary role, or remove the `PasswordPolicy.lean` case study from §5.
- [ ] **[mC4]** Add at least 5 directly comparable mechanization papers to §7; for each, state the specific definition-level or theorem-level difference.
- [ ] **[mC5]** Provide a pinned-environment reproducibility artifact (Nix flake or equivalent) or justify why the manifest-hash approach is sufficient for the target venue's artifact requirements.
- [ ] **[mC6]** Define "PoC behavior" in §0.2 Non-claim 4 or replace with a precise referent.
