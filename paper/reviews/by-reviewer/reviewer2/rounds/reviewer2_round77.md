## Review: UAD/f Two-Operator Kernel under Partial Projections

---

### 1) Overall Recommendation

**Weak Accept** (with minor revisions required)

The paper presents a well-scoped Lean4 mechanization of a partial-projection specification kernel. The contribution is methodological rather than mathematically novel, but the authors are admirably upfront about this. The explicit assumption-interface discipline, mechanized counterexamples, and must/may split under partiality constitute a genuine, reusable formal artifact. The submission is honest about its limitations and carefully calibrated to library/methodology tracks at the target venues.

The primary concern is that the paper's positioning at FM/TACAS-level venues requires a stronger argument for why this particular formalization was non-trivial *to mechanize* (beyond the mathematical content). The current presentation partially addresses this in §6 but could be sharpened. No blocking correctness issues were identified.

---

### 2) Strengths

1. **Assumption transparency.** Every non-trivial theorem carries its hypotheses as explicit arguments. The assumption matrix (Appendix) systematizes this in a way that is directly useful to practitioners extending the kernel.

2. **Mechanized failure boundaries.** The counterexample suite (`TransferCounterexample`, `AdequacyCounterexample`, `TotalizationCounterexample`) is not decorative — each counterexample corresponds to a dropped hypothesis in a main theorem. This is the right way to demonstrate hypothesis necessity.

3. **Must/may split is crisp.** The decision to make the `proj_i(x) = none` branch first-class (rather than defaulting to non-membership or membership) and to expose it as an operational policy choice is technically sound and honestly scoped.

4. **Self-aware non-claims.** The §0.2 non-claims list and §8 limitations are unusually specific. The paper does not overreach: extractor correctness, statistical validity, and temporal semantics are all explicitly out of scope.

5. **Reproducibility infrastructure.** The hash-pinned manifest, `reproduce_formal.sh`, and optional Dockerfile represent a solid artifact package for this class of paper.

6. **`UAndOn_empty_eq_univ` as an explicit guardrail.** Surfacing the vacuous-truth edge case and making it a named theorem is exactly the kind of mechanization hygiene that distinguishes careful formalization from naive encoding.

---

### 3) Major Concerns (blocking)

**M1: Weak justification for why the composition theorem (`preimage_compose`) required mechanization effort under partiality.**

§3.5 claims non-triviality because the `none` branch must be "eliminated constructively," and §6 notes the axiom footprint difference from `lifted_transfer`. However, the paper does not show a plausible *incorrect* proof attempt that would typecheck under a totality assumption but fail here. The `TotalizationCounterexample` addresses a different angle (spurious witnesses from default-filling, not from proof-level branch omission). A reviewer familiar with Lean4's `Option.bind` behavior may regard the branch analysis as straightforward, and the paper does not preempt this objection. The delta claim in §6.1 item 2 ("must discharge impossible `none` branches induced by bind-commutation") needs a concrete mechanization witness — either a `sorry`-proof stub that fails, or an explicit description of which tactic step requires the `hcomm` assumption that would be unavailable under a totalized encoding.

*Resolution:* Add a brief mechanized note (even a `-- this case is impossible without hcomm` comment block promoted to the manuscript) or reference the exact proof step in `Composition.lean` that discharges the `none`-branch contradiction, and explain why the corresponding step would be unavailable or incorrect in a totalized encoding.

**M2: `RQ1`/`RQ2` resolution criteria are stated but their "operational consumption" evidence is thin in the main text.**

§1.3 states resolution criteria for the supporting RQs: `RQ1` is resolved when heterogeneity is "carried through theorem statements without universe/typing collapse," and `RQ2` when `A(i) ⊆ D(i)` is "consumed as witness-validity infrastructure." However, `HeterogeneousTransferWitness.lean` is mentioned only in the traceability matrix and §5.1 bullet, with no excerpt or proof sketch in the body. For a formal paper at ITP/CPP, the claim that heterogeneous carriers are handled non-trivially deserves at least one sentence explaining what would go wrong with a universe-collapsing encoding (e.g., what coercions would be needed, and why they complicate transfer theorem statements).

*Resolution:* One paragraph in §3.2 (or §5.1) explicitly noting what a carrier-collapsing encoding would require and why `carrier : ι -> Type` avoids it. Does not need to be long — two or three sentences suffice.

**M3: The `UStar` parametricity claim needs a clearer epistemological status.**

§3.8 says `UStar` is a "theorem parameter" and theorems are "conditional linkage." This is stated correctly, but the paper does not address whether any concrete system *can* instantiate `UStar` in a non-trivial way. A reader at a formal methods venue will ask: if `UStar` is always parametric and never constructed, what is the practical value of the linkage theorems beyond tautological generality? The paper's answer (these are assumption-audit contracts) is defensible, but it should be stated explicitly in §3.8 or §7.8 rather than left implicit.

*Resolution:* One or two sentences in §3.8 stating the epistemological claim: these theorems show *what conditions on `UStar` are sufficient* for linkage, and their value is that the conditions are machine-checkable when a concrete `UStar` candidate is proposed — even if this paper does not propose one.

---

### 4) Minor Concerns

**m1: Terminology: "UAD/f" vs "UDA/f".**  
The abstract uses "UAD/f" and §0 note 1 uses "UAD/f", but the project directory is named `UadfU0` and the CLAUDE.md context refers to "UDA/f model." The manuscript should pick one spelling and use it consistently throughout (including in the Lean file paths and artifact names). Currently there is inconsistency between the prose and the artifact namespace.

**m2: Axiom report in §4.3 is incomplete for key supporting theorems.**  
The axiom audit covers 6 theorems. The `no_left_adjoint_of_partial` entry (`[propext]`) is informative. However, `UStar_inter_projDomOn_subset_UAndOn` is listed as "no axioms" — this is unexpected for a theorem over existentially quantified predicates; is it constructive? A brief note clarifying whether the no-axiom result is because the proof is fully constructive (no `sSup`/`Classical.choice` anywhere in the proof term) would be helpful.

**m3: §5.2 ("Password-policy case theorem") — domain `D = True` is noted as a "toy case."**  
The paper acknowledges this but does not explain what happens when `D ≠ True`. The `ArtifactBundleExample` is described as having non-trivial domain separation, but §5.1 does not give a concrete example of what a domain constraint looks like or why it matters for the proof. One sentence would suffice.

**m4: Reference list is thin on mechanization-focused related work.**  
The paper cites Darais/Van Horn (constructive Galois connections) and the Mathlib community paper, but not recent ITP/CPP submissions on partial-function formalization in Lean4. While exhaustive coverage is not required, at least one recent venue-relevant mechanization paper (post-2020, Lean4/Isabelle/Coq on partial maps or option-valued functions) would strengthen the related work positioning.

**m5: §6 "What Mechanization Added" is somewhat repetitive.**  
§6.1 ("Concrete delta against baseline theorem libraries") partially re-states §6 bullet points. Consider merging or condensing these into a single coherent argument. The current structure makes it easy to miss that items 1–5 in §6 and items 1–5 in §6.1 are saying related (but not identical) things.

**m6: `lake-manifest.json` is empty (`packages: []`) — this is noted in §2.1.**  
The design rationale (expose all assumptions through minimal Lean-core dependency surface) is stated, but the tradeoff (reduced Mathlib reuse) is only mentioned once. At FM/TACAS, reviewers may ask whether the manual reproduction of basic set lemmas (`subset_refl`, `subset_trans`, `set_ext` in `Definitions/Model.lean`) is worth the portability benefit. A sentence in §4.1 or §6.1 acknowledging this explicitly would preempt the objection.

---

### 5) Required Revision Checklist

- [ ] **[M1]** Add mechanization witness or proof-step reference showing why `preimage_compose`'s `none`-branch discharge is non-trivial under `Option.bind` (vs. totalized encoding). Can be a proof excerpt or explicit reference to `Composition.lean` line with explanation.

- [ ] **[M2]** Add one paragraph (§3.2 or §5.1) explaining what a carrier-collapsing encoding of heterogeneous layers would require and why the `carrier : ι -> Type` approach avoids those complications.

- [ ] **[M3]** Add 1–2 sentences to §3.8 stating the epistemological role of the `UStar` parametric theorems: they are assumption-sufficiency contracts, useful when a concrete candidate is proposed.

- [ ] **[m1]** Standardize "UAD/f" vs. "UDA/f" spelling throughout manuscript, appendices, and artifact references.

- [ ] **[m2]** Add a note to the §4.3 axiom audit clarifying why `UStar_inter_projDomOn_subset_UAndOn` has no axioms (constructive proof? no existentials introduced?).

- [ ] **[m4]** Add at least one post-2020, venue-relevant mechanization reference on partial-function or option-valued formalization in an interactive theorem prover.

- [ ] **[m5]** Consolidate or cross-reference §6 and §6.1 to reduce repetition and sharpen the delta narrative.
