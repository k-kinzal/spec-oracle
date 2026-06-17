## Formal Methods Paper Review — Reviewer #3

**Paper:** "UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization"

---

### 1. Overall Recommendation

**Weak Reject / Major Revision Required**

The paper presents a clean, well-scoped Lean4 mechanization with commendable assumption transparency. However, several blocking issues prevent acceptance at FM/ITP/CPP/TACAS/FASE/Formal Aspects: the novelty case is underargued relative to venue expectations, the prior-work positioning contains definition-level gaps, and the contribution framing oscillates between "methodology" and "result" in ways that will confuse reviewers and PC members. These are fixable with revision but require non-trivial restructuring.

---

### 2. Strengths

1. **Assumption transparency is genuine and well-executed.** Explicit `hproj`/`hA`/`hcomm` arguments, the assumption matrix appendix, and the mechanized counterexample (`transfer_fails_without_hproj`) are exactly the kind of auditable interface that formal-methods venues increasingly value.

2. **`sorry`-free build with traceability.** The reproduce script, hash checks, and theorem-to-file table are done correctly. The `sorry`-count hard check is the right engineering choice.

3. **Must/may split is a real design decision.** The paper makes a defensible choice about undefined-point policy and mechanizes it end-to-end, including the `preimage_subset_preimageMay` bridge theorems. This is not a free lunch.

4. **Non-adjointness guardrail is useful.** `no_left_adjoint_of_partial` is a concise, checkable statement that blocks a common intuition error. The connection to total-map Galois-connection libraries is appropriately hedged.

5. **Counterexamples for dropped assumptions.** `TransferCounterexample.lean` and `AdequacyCounterexample.lean` demonstrate that hypotheses are non-redundant. This is mechanization hygiene done right.

6. **Self-aware scope management.** §0.2 non-claims are specific and honest. The two-paper split is declared upfront.

---

### 3. Major Concerns (Blocking)

#### M1. Novelty argument is too thin for the target venues

The paper repeatedly hedges ("theorem identities are mostly classical," "not new set theory") without then providing a compelling affirmative case that the *combination* is novel at the required level.

For FM, ITP, CPP, or TACAS, a "methodology/library-style" submission still needs to articulate: *what would a careful user of Mathlib's `Set.preimage_*` + `GaloisConnection` infrastructure get wrong that your kernel prevents?* Section 6 attempts this but remains prose-level. The "concrete delta" in §6.1 lists five items but does not show, e.g., a failed Mathlib port attempt or an explicit formal statement that *cannot* be stated with standard APIs without your kernel's structure.

**Required fix:** Add a subsection with a formal claim of the form: "Theorem X cannot be stated in library L with the same assumption transparency because…" and mechanize at least one such impossibility or import-attempt sketch. Alternatively, strengthen the library-methodology claim with a comparative proof-effort table referencing actual Mathlib theorem names and their assumption footprints.

#### M2. Related-work positioning is definitionally incomplete

Sections §7.1–§7.7 name the right families (abstract interpretation, institutions, BX/TGG, Galois connections) but the "definition-level differences" are stated at a high level and are not always accurate:

- §7.2 claims difference from institutions by saying "this kernel fixes one root-space predicate semantics." But institutions are parameterized over signatures too; the distinction needs to be at the level of satisfaction condition and morphism structure, not just "we fix one root space." A referee familiar with Goguen/Burstall will find this insufficient.
- §7.5 claims difference from Darais/Van Horn constructive Galois connections by pointing to undefined-point witnesses. This is correct but should reference the specific total-map assumption in their development (e.g., their `α -> γ` abstraction function) and show precisely where your `Option`-returning projection breaks their interface.
- Reference 9 (Mossakowski/Hets) is listed but not discussed. Hets is the closest mechanized prior work in spirit (heterogeneous semantics, formal tool chain). The absence of a concrete comparison is a gap.

**Required fix:** For at least the institutions and Darais/Van Horn lines, add a 3–5 sentence formal comparison identifying the specific structural incompatibility, not just a prose-level claim. Engage with Mossakowski/Hets explicitly.

#### M3. `UStar` treatment is insufficient as a paper-level claim

§3.8 and §7.8 introduce `UStar` as a "parametric predicate" and offer conditional linkage theorems. The paper is correct that it cannot construct `UStar`. However, the current treatment does not explain *what problem these theorems solve for a user of the kernel.* If `UStar` is fully opaque, the theorems read as: "if your ideal root satisfies condition C, then it relates to your operators"—which is nearly trivial and adds limited value beyond the definition.

The `UStar` linkage family (6 theorems, classified as "supporting") currently has no compelling use-case demonstration. The password-policy case study uses identity projections and trivial domains, so `UStar` never appears there under real partial-observability conditions.

**Required fix:** Either (a) remove `UStar` from the paper's claim boundary and relegate to appendix-only, or (b) provide a mechanized example where `UStar` is instantiated to a non-trivial predicate and the domain-restricted linkage theorem (`UStar_inter_projDomOn_subset_UAndOn`) does non-trivial work compared to the global form. Option (a) is lower-effort.

#### M4. RQ1/RQ2 "resolution" criteria are self-referential

The resolution policy for RQ1 states it is resolved "when heterogeneity is carried through theorem statements without universe/typing collapse." This is a criterion the paper itself defines and then self-certifies. A reviewer cannot independently assess whether "universe/typing collapse" was a real risk that was actually avoided, or whether the heterogeneous carrier structure is cosmetically complex.

Similarly, RQ2's resolution via `lifted_subset_preimage_domain` and `U0_witness_projects_to_some_domain` — these are supporting lemmas (classified in §4.6 as part of the 34-count). The paper doesn't explain why these two lemmas specifically constitute resolution of the RQ, vs. being infrastructure.

**Required fix:** For RQ1, add a concrete statement: "Without dependent indexing (`carrier : ι -> Type`), theorem T would require universe polymorphism or type collapse in the following way…" For RQ2, make explicit what the theorem guarantees that is non-obvious — e.g., that root witnesses under `U0` are domain-valid at projection-defined layers.

---

### 4. Minor Concerns

**m1. Theorem count inflation risk.** The 73-theorem count includes `subset_refl`, `subset_trans`, `set_ext` in `Definitions/Model.lean`. These are local re-proofs of standard facts. At venues like CPP or ITP, reviewers may flag this as padding. Consider either importing these from Lean core or labeling them explicitly as "local infrastructure" in the catalog header.

**m2. Password-policy case study is too trivial.** Identity projections (`proj _ n = some n`) and `D = True` mean the model is essentially a flat predicate intersection check. It validates notation but not the partial-projection semantics the paper is built around. A case study with `proj` that is genuinely partial (some inputs map to `none`) would be more convincing.

**m3. Abstract in §0 oversells.** The phrase "failure boundaries are mechanized as executable counterexamples" is accurate but the abstract implies a broader scope than the three counterexample files cover. The word "executable" may confuse readers (Lean proofs are not typically run as programs). Clarify.

**m4. `Classical.choice` asymmetry explanation is deferred.** §4.3 notes that `preimage_compose` uses `Classical.choice` while `lifted_transfer` does not, and attributes this to "extensional set equality vs. one-way subset." This is correct but the explanation is spread across footnote-style items 7–10. A one-sentence direct explanation ("set equality via `funext`/`propext` over existential witnesses requires classical choice for unique witness selection in this style") would be cleaner.

**m5. Dockerfile is correct but untested claim.** §9 says the Dockerfile "provides a pinned replay container recipe" but does not pin Lean toolchain inside the image (it uses `elan-init.sh` from the network). This makes the container non-deterministic. Pin the toolchain version in the `RUN curl elan-init.sh` line, or note this as a limitation.

**m6. Composition example scope.** `preimage_compose` is called "non-trivial under partiality" (§3.5) because the `none` branch must be eliminated. This is true, but the current explanation says the result "collapses to standard total preimage-composition identities" for total maps. This sentence is only true modulo the `Option` wrapper — for a reviewer unfamiliar with Lean's elaboration it may read as claiming total-map composition is trivially covered. Tighten this.

**m7. Section 0 is structurally awkward.** Having §0 titled "Scope, Split, and Quality Bar" before §1 "Problem Statement" is unusual. This is a style issue but may trigger desk-rejection flags at more traditionally structured venues (FM, TACAS). Consider merging §0 into an Introduction section.

---

### 5. Required Revision Checklist

#### Blocking (must fix before acceptance)

- [ ] **[M1]** Provide a formal or semi-formal argument distinguishing the kernel's assumption transparency from what Mathlib's `Set.preimage_*` + `GaloisConnection` APIs would yield directly. At minimum, identify one theorem that cannot be expressed with the same obligation structure using off-the-shelf Mathlib.
- [ ] **[M2a]** Add a 3–5 sentence formal comparison with institution-style frameworks (Goguen/Burstall), identifying the specific structural incompatibility at the satisfaction-condition or morphism level.
- [ ] **[M2b]** Strengthen the Darais/Van Horn comparison: cite their specific total-map assumption and show where `Option`-returning projection breaks their interface.
- [ ] **[M2c]** Engage explicitly with Mossakowski/Hets (Ref. 9) — either include a paragraph-level comparison or remove the reference and replace with a more directly comparable cited work.
- [ ] **[M3]** Either remove `UStar` from paper-level claims (appendix-only) or add a mechanized example with a non-trivial `UStar` instantiation showing the domain-restricted linkage doing real work.
- [ ] **[M4a]** Add a concrete statement explaining what "universe/typing collapse" risk RQ1's heterogeneous carrier design avoids, with a specific example or counter-scenario.
- [ ] **[M4b]** Clarify what `lifted_subset_preimage_domain` / `U0_witness_projects_to_some_domain` guarantee that is non-obvious, and why these constitute RQ2 resolution.

#### Non-blocking but strongly recommended

- [ ] **[m2]** Replace or augment the password-policy case study with an example featuring genuinely partial projections (some `proj i x = none` at non-trivial points).
- [ ] **[m5]** Pin the Lean toolchain version inside the Dockerfile (`elan toolchain install` with a fixed version tag), or explicitly document the non-determinism.
- [ ] **[m7]** Restructure §0 into a conventional Introduction to avoid desk-rejection at FM/TACAS.
- [ ] **[m1]** Label `subset_refl`, `subset_trans`, `set_ext` in the theorem catalog as "local infrastructure re-proofs" and exclude them from count narratives to avoid reviewer skepticism.
- [ ] **[m4]** Consolidate `Classical.choice` asymmetry explanation into a single sentence in §4.3.
