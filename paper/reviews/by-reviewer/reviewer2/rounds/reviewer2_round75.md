# Formal-Methods Venue Review: UAD/f Two-Operator Kernel under Partial Projections

**Reviewer #2 — Balanced but Rigorous**
**Target venues:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

## 1. Overall Recommendation

**Weak Accept / Major Revision Required**

The paper presents a coherent, self-aware mechanized kernel contribution in Lean4. The authors are admirably honest about what they do and do not claim. The mechanization is non-trivial and the assumption-auditing methodology is sound in intent. However, the paper has significant structural problems that would prevent acceptance at FM/ITP/CPP in current form: the novelty framing is defensive to the point of undermining confidence in the contribution, the relation-to-prior-work section lacks depth, and the reproducibility scope is narrower than a formal-methods venue would require. These are fixable issues.

---

## 2. Strengths

**S1. Honest scope management.**
The non-claims section (§0.2) is exemplary. Few papers explicitly enumerate what they do not prove. This disciplined boundary-setting raises trust in what is claimed.

**S2. Assumption-matrix as a first-class artifact.**
The appendix `assumption_matrix.md` and the per-theorem fallback-claim column is a genuinely useful contribution to mechanization methodology. Making hypotheses non-redundant via mechanized counterexamples (`transfer_fails_without_hproj`, `AdequacyCounterexample`) is strong practice.

**S3. Partiality as a first-class citizen.**
The treatment of `Option`-typed projections as a first-class concern — not a post-hoc footnote — is the paper's strongest technical distinguisher. The non-adjointness theorem (`no_left_adjoint_of_partial`) and the must/may split are direct consequences of this design choice, and the paper argues the case consistently.

**S4. Axiom footprint disclosure.**
Explicitly running `#print axioms` on core theorems and reporting asymmetric footprints (`lifted_transfer: no axioms` vs `preimage_compose: [propext, Classical.choice, Quot.sound]`) with explanations is above the bar for ITP/CPP.

**S5. RQ-to-theorem traceability matrix (§1.5).**
The mapping from research questions to Lean file/theorem names is concrete and checkable. This is the right structure for a mechanization paper.

**S6. Vacuous-truth edge case (§3.3).**
`UAndOn_empty_eq_univ` being mechanized and its operational implication being called out explicitly is the kind of detail that separates serious mechanization from superficial proof-scripting.

---

## 3. Major Concerns (Blocking)

**M1. Novelty claim is systematically undermined by the authors themselves.**

Section 6.1 ("Concrete delta against baseline theorem libraries") correctly identifies that the mathematical identities are classical. However, the paper then claims the contribution is "an auditable contract layer under partiality." This framing is too vague to evaluate as a research contribution at FM/ITP/CPP. The question a program committee will ask is: *what specific design decision or theorem structure is not achievable by straightforward instantiation of Mathlib's `Set.preimage_comp`, `GaloisConnection`, or `PartialOrder` APIs?*

The paper gestures at this (heterogeneous carriers + partiality + domain/admissibility separation in one model signature) but does not make it crisp. A table comparing the proposed `Model ι α` signature against the closest Mathlib interface, identifying the structural gap, would suffice. As written, "methodology contribution" is not a claim that FM/ITP program committees have consensus on accepting.

**M2. Related work is thin for target venues.**

Section 7 cites institutional frameworks, BX, and abstract interpretation at a high level, but does not engage technically with specific mechanization lines:

- **Isabelle/HOL set algebra**: `Image.thy`, `Fun.thy` contain preimage composition lemmas for total functions. The paper should explain why these do not subsume `preimage_compose` even modulo `Option` lifting.
- **HOL4 / Coq developments** on partial maps and domain theory (e.g., PFUN libraries, Scott domains in Coq) are not discussed.
- **Mechanized abstract interpretation** (e.g., work by Cachera et al., or Blazy/Laporte in Coq) is cited only at the 1977 Cousot level.
- The claim that "direct baseline reuse is insufficient" (§6.1) needs a specific reference to an attempt or a concrete impossibility argument, not only a prose claim.

This gap is blocking for CPP/ITP, which expect precise comparison with existing Lean/Coq/Isabelle libraries.

**M3. `UStar` parametricity obscures a foundational gap.**

Throughout §3.8, `UStar` is described as a "parameter predicate" with the framing that this is a feature (assumption-auditing). However, the central motivation of the paper — multi-layer specification comparison needs a root-side criterion but `U*` is unavailable — is never formally resolved. `U0` and `UAnd` are constructed from projections, but the question of whether they constitute an adequate *substitute* for `UStar` in any formal sense is not answered. The paper explicitly says it does not claim this, but then §3.8's linkage theorems (`UStar_subset_UAndOn`) presuppose `UStar` as input. The reader is left asking: what is the formal relationship between the `U0` the paper constructs and the `UStar` the paper parametrizes over? Even a negative result (they are not comparable in general) would close this gap.

**M4. Reproducibility claim scope is understated relative to submission.**

Section §4.4 and §9 correctly scope reproducibility to "same manifest + same Lean toolchain + same script revision." However:

- The `lean-toolchain` hash is recorded but not version-pinned in a way that a reviewer can verify independently without knowing `elan` availability. The toolchain version string should be stated in the manuscript body, not only in an appendix hash.
- `lake-manifest.json` with `packages: []` means Mathlib is absent, which is architecturally significant and mentioned in §2.1. This should be stated explicitly in §9 as a reproducibility *asset* (no network fetches), not buried in a design-choice footnote.
- The `42 jobs` figure in build evidence with the explanation "not expected to equal source-file count" will confuse reviewers; a one-sentence explanation of what `lake` job granularity means would help.

**M5. Password-policy case study (§5.2) is underpowered.**

`checkConsistent_iff_allThree` is described as a "mechanized sanity theorem for constrained interval domain." For a formal-methods venue, a case study must demonstrate that the general theorems solve a problem that would otherwise require ad hoc reasoning. The current case study shows that a closed-form Boolean check over three layers is equivalent to an existential witness — this is nearly tautological once the model is in place. To be convincing, the case study should either: (a) show a cross-layer inconsistency that the kernel detects, with evidence that the inconsistency is non-trivial, or (b) show that an extractor proof obligation from §3.6.1 is discharged for a realistic (not toy) extractor.

---

## 4. Minor Concerns

**m1. Lean4 toolchain version should appear in the manuscript body.**
`v4.27.0` appears in §4.3 as a toolchain string reference, but reviewers will check this against the lean-toolchain file hash; a direct statement of the version string in the body reduces friction.

**m2. `SpecSet α := α -> Prop` vs Mathlib `Set α`: design choice cost is not analyzed.**
§2.1 correctly notes the `lake-manifest.json` has `packages: []` and acknowledges reduced Mathlib interface reuse. There is no analysis of what was made harder by this choice (e.g., no `Finset` API, no `simp` lemma sets). A brief cost/benefit sentence would help readers calibrate.

**m3. `Classical.choice` in `preimage_compose` warrants a comment in the proof sketch.**
§4.3 note 7 explains this at the axiom-audit level, but §3.5's proof skeleton does not flag where classicality enters. A reader re-reading §3.5 after §4.3 has to reconnect these manually.

**m4. Figure or diagram for the two-operator model is missing.**
The `U0`/`UAnd` separation, partial projection, must/may split, and domain/admissibility structure have enough moving parts that a single commutative diagram or Hasse-diagram figure would substantially aid comprehension, especially for FASE/TACAS audiences less specialized in order theory.

**m5. `UAndOn_subset_UAndMayOn` is listed as supporting but its operational role is implicit.**
In §2.6 the must/may cross-family relation is said to be "explicit only through named inclusion theorems such as `preimage_subset_preimageMay` and `UAndOn_subset_UAndMayOn`." But the paper never shows a scenario where a user would need this bridge. A one-sentence example would anchor it.

**m6. The `E ≠ graph(proj)` motivation (§3.6) uses `EPlus1` as a structural witness, not a realistic model.**
The paper acknowledges this. However, a brief mention of what kind of real extraction scenario motivates the `EPlus1` pattern (e.g., semantic normalization with hash-consing, NLP extraction with synonym collapse) would help reviewers assess whether the generality is operationally motivated or purely formal.

**m7. Abstract is dense and difficult to parse on first read.**
The abstract lists 5+ theorem families in one paragraph. For FM/ITP, the abstract should lead with the engineering motivation, state the one-sentence contribution, then enumerate theorems. Currently the theorem list precedes the motivation.

**m8. References list is thin (13 items) for the breadth of related-work claims.**
§7 discusses institutions, BX, abstract interpretation, refinement calculus, and mechanized Galois connections. 13 references cannot adequately support this scope. At CPP/ITP, reviewers will notice missing citations (e.g., Paulin-Mohring on partial functions in Coq, any HOL4 work on option-typed maps, recent ITP papers on multi-view consistency).

---

## 5. Required Revision Checklist

**Blocking (must fix before acceptance):**

- [ ] **R1.** Add a precise structural comparison table between `Model ι α` and the closest Mathlib/HOL/Isabelle interface for partial-map preimage composition. Demonstrate concretely (not in prose) why direct instantiation does not achieve the same theorem interface.
- [ ] **R2.** Expand §7 with at minimum 5–8 specific mechanization-paper citations from HOL4/Coq/Lean libraries dealing with partial maps, domain/admissibility separation, or multi-view consistency, with one-sentence technical differentiators for each.
- [ ] **R3.** Address the `UStar` gap: state formally (or as a theorem/proposition, even if negative) the relationship between the constructed `U0` and the parametric `UStar`. If no formal relationship exists by design, explain why this is acceptable for the paper's claims and make this explicit in §3.8 rather than implicitly deferring it.
- [ ] **R4.** Strengthen the case study in §5.2: add at least one example that exercises a non-trivial cross-layer result using the general theorems (not just the closed-form Boolean equivalence). Alternatively, discharge one extractor proof obligation from §3.6.1 for a realistic extractor description.
- [ ] **R5.** State the Lean toolchain version string (`leanprover/lean4:v4.27.0`) in the manuscript body (§4.3 or §9), not only in the appendix hash. Explain in §9 that `packages: []` eliminates network-fetch dependencies as a reproducibility property.

**Non-blocking (strongly recommended):**

- [ ] **R6.** Rewrite the abstract to lead with motivation, then one-sentence contribution, then theorem families.
- [ ] **R7.** Add a figure (commutative diagram or Hasse diagram) illustrating the `U0`/`UAnd`/partial-projection/must-may structure.
- [ ] **R8.** In §3.5's proof skeleton, flag the proof step where `Classical.choice` enters, cross-referencing §4.3 note 7.
- [ ] **R9.** Expand the references list to at least 20–25 items, covering mechanization literature for partial functions and multi-view consistency.
- [ ] **R10.** Add a one-sentence operational motivation for the `EPlus1` counterexample pattern (§3.6) connecting it to a realistic extraction scenario.
