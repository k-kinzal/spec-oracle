# Formal-Methods Venue Review — Reviewer #3

**Paper:** *UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization*
**Venues considered:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

## 1. Overall Recommendation

**Weak Reject — Major Revision Required**

The paper is carefully assembled and shows genuine mechanization effort. The assumption-audit framing is appealing, the axiom disclosure is disciplined, and the artifact scaffold is unusually complete. However, the paper as submitted does not clear the bar for any of the target venues on the criterion that matters most: **technical novelty**. The contribution is primarily organizational (making implicit assumptions explicit in a particular domain model) rather than mathematical or proof-theoretic. The prior-work positioning is superficial and does not engage with closely adjacent mechanized work. Several claimed "non-trivial" results reduce to straightforward exercises once the definitions are written down. These are blocking concerns. The paper needs a substantial revision before it can compete at FM/ITP/CPP/TACAS.

---

## 2. Strengths

- **Axiom audit discipline.** The per-theorem `#print axioms` disclosure (§4.3) is rare and genuinely useful. Distinguishing `Classical.choice` from package-level axioms shows proof-engineering maturity.
- **No `sorry`.** The mechanization is complete; no placeholder proofs.
- **Assumption-failure counterexamples.** `TransferCounterexample.lean` and `AdequacyCounterexample.lean` make the hypothesis non-redundancy argument executable rather than prose-only. This is the methodologically strongest part of the paper.
- **Clean scope boundary.** The explicit non-claims list (§0.2) and the two-paper split are good practice and reduce overpromising.
- **Reproducibility scaffold.** Hash-locked manifest, single-command replay script, and expected output values are all present.

---

## 3. Major Concerns (Blocking)

### M1 — Novelty claim is too weak for target venues

The paper repeatedly acknowledges that the mathematical identities are classical (§6, §6.1). The stated contribution is an "assumption-audited interface" and a "methodology contribution." At FM/ITP/CPP this requires a much stronger argument for why this specific interface could not be built by a competent Lean user in a few days by instantiating Mathlib's `GaloisConnection`, `Set.preimage_*`, and `OrderIso` APIs. Section 6.1 attempts a delta argument ("direct baseline reuse is insufficient") but the argument is informal and not convincing:

- The claim that `preimage_compose` is non-trivial because `Option.bind` introduces an extra `none`-branch is correct but describes a routine pattern match, not a deep result.
- The claim that `lifted_transfer` requires a "same-root witness" is correct but this is a standard existential-witness reconstruction step, not a theorem that required new insight.

**Required action:** Either (a) identify and prove a theorem that is genuinely surprising or requires a non-obvious technique, or (b) reframe the contribution explicitly as a *reusable library* contribution and demonstrate reuse by having a second non-trivial development build on it. Neither is currently present.

### M2 — Prior-work engagement is superficial

Section 7 lists nine related areas but engages with none of them at definition level except for a brief paragraph each. The paper cannot be reviewed against the state of the art because:

- No comparison with Isabelle/HOL mechanizations of partial functions (e.g., Huffman & Kuncar's HOLCF, or partial-function libraries). The `Option`-based partiality treatment may already exist verbatim.
- No engagement with the mechanized institution literature (Mossakowski et al. have Isabelle/HOL formalizations; Diaconescu has Coq work). The dismissal ("narrower but executable") is not substantiated.
- The Galois-connection line cites Darais & Van Horn 2016 but does not compare formally. Constructive Galois connections already handle partiality through *approximating* functions. Does `no_left_adjoint_of_partial` add anything beyond a direct corollary of their framework? This is unaddressed.

**Required action:** For each of the three most closely adjacent lines (constructive Galois connections, mechanized institutions, partial-function Isabelle/HOL work), provide a precise definition-level comparison: which theorems overlap, which are genuinely new, and which are strictly weaker.

### M3 — "UAD/f Two-Operator Kernel" novelty is not established

The central claim of separating `U0` (join) and `UAnd` (meet) into distinct root-side operators is presented as a contribution (§3.3, RQ3), but:

- LUB/GLB characterizations of union/intersection are standard lattice theory.
- The observation that `∀ i, P i` is antitone in the active set while `∃ i, P i` is monotone is a logic-101 fact.
- `UAndOn_empty_eq_univ` (∀ over empty domain is vacuously true) is equally elementary.

The paper claims these are "not novelty claims" in some places (§3.1) but then counts `U0On_monotone`, `UAndOn_antitone`, `UAndOn_subset_U0On`, `UAndOn_empty_eq_univ`, and `consistent_iff_exists_UAndOn_pair` in the "core theorem interfaces (RQ3–RQ5): 16" count (§4.6), implying they contribute to the core novelty. This is inconsistent.

**Required action:** Remove these elementary lattice facts from the core-theorem count or provide a compelling argument for why their combination in this specific typed partial-projection setting yields a result that could not be immediately anticipated by any order-theorist.

### M4 — `PasswordPolicy` case study is too narrow to support generalization

The PasswordPolicy case study (§5.2) operates on a closed bounded-interval domain with three layers and a `checkConsistent` boolean predicate. The equivalence theorem (`checkConsistent_iff_allThree`) is presented as a "mechanized sanity theorem" but:

- The domain is so small that the theorem is essentially a decision-procedure unfolding.
- No argument is made for why this domain is representative of the general `Model ι α` setting.
- The paper explicitly excludes temporal/state-transition semantics (§8), which covers most non-trivial engineering specification scenarios.

**Required action:** Either (a) add a second case study in a structurally different domain (e.g., a protocol layer, a type-system fragment) to demonstrate that the kernel is not purpose-built for interval constraints, or (b) downgrade the case study to an example and remove any language suggesting broader applicability.

### M5 — `UStar` parametricity is an unfulfilled promise

Section 3.8 ("Ideal-root linkage") introduces `UStar` as a parametric ideal-root predicate and proves conditional linkage theorems. However:

- `UStar` is never constructed or instantiated anywhere in the paper.
- The theorems in `IdealRoot.lean` are trivially conditional: if you assume `UStar ⊆ lifted(i)` for all active `i`, then `UStar ⊆ UAndOn(active)` by intersection. This is a one-line proof.
- The "observability-domain restriction" variant requires `UStar ∩ projDom(i) ⊆ lifted(i)`, which is equally immediate.

Claiming these as a separate theorem family (6 theorems in the supporting count) while acknowledging `UStar` is never instantiated weakens the paper's integrity.

**Required action:** Either prove a non-trivial property of `UStar` by constructing a concrete instance (even a toy one), or remove `IdealRoot.lean` from the contribution claims and relegate it to a discussion appendix.

---

## 4. Minor Concerns

**m1 — Notation inconsistency.** The paper uses both `A(i)` and `Ui(i)` for the admissible set (§2.2), with a footnote calling it a "compatibility alias." This creates unnecessary cognitive overhead. Pick one notation and use it consistently throughout.

**m2 — §6 "Per-theorem hardness summary" is self-assessed.** The claims that `lifted_transfer` "is not a set-theory tautology" and `preimage_compose` "is not immediate under partiality" are made by the authors without external validation. These assessments may be accurate but require either a citation to a comparable development that fails to handle these cases, or a proof-complexity argument.

**m3 — Lean toolchain version not future-proofed.** The paper pins `leanprover/lean4:v4.27.0`. Given Lean4's rapid release cadence, the build may silently break within months of publication. The reproducibility claim should be qualified with a container/Nix specification or a statement about expected forward-compatibility horizon.

**m4 — `lake-manifest.json` with `packages: []`.** The design choice to avoid Mathlib is explained as exposing assumptions through minimal dependency. This is defensible, but it also means the paper re-implements set-level infrastructure (`subset_refl`, `subset_trans`, `set_ext`) that exists in Lean4 core. These 3 theorems in `Definitions/Model.lean` are noise in the theorem count. They should either be replaced with `Lean.Set` stdlib equivalents or justified more explicitly.

**m5 — Abstract is too long and reads as a table of contents.** The abstract lists 8 theorem families and 5 contribution bullets. For FM/ITP/CPP audiences, a 150-word abstract that states the central result and why it is hard is more effective.

**m6 — Reference list is incomplete.** Given the Lean4 mechanization, the paper should cite: (a) Lean4 Mathlib specifically (not just "the mathlib Community CPP 2020" which refers to Lean3 Mathlib); (b) Buzzard et al.'s experience reports on Lean4 formalization practice; (c) at least one prior Lean4-specific partial-function or `Option`-monad formalization for comparison.

**m7 — §7.5 Galois-connection positioning is imprecise.** The paper says the non-adjointness theorem "blocks silent import of total-map Galois intuitions." This framing suggests the audience might otherwise make this error, which is condescending to the FM audience. Reframe as a precise boundary condition result.

---

## 5. Required Revision Checklist

- [ ] **[M1]** Identify at least one theorem that is technically surprising or requires a non-obvious proof technique; alternatively, reframe as a library contribution and demonstrate non-trivial downstream reuse.
- [ ] **[M2]** Add definition-level comparison with constructive Galois connections (Darais & Van Horn 2016), mechanized institution work (Mossakowski et al.), and Isabelle/HOL partial-function libraries. State precisely which theorems overlap and which are new.
- [ ] **[M3]** Resolve the inconsistency between claiming elementary lattice facts as "non-novelty" in prose while counting them in the core-theorem novelty tally (§4.6). Revise the count and the claim language accordingly.
- [ ] **[M4]** Add a second structurally distinct case study, or explicitly downgrade the existing case study to an example with no generalization claim.
- [ ] **[M5]** Either instantiate `UStar` concretely in at least one example, or remove `IdealRoot.lean` theorems from contribution claims.
- [ ] **[m1]** Unify `A(i)` / `Ui(i)` notation throughout.
- [ ] **[m3]** Add a container spec (Docker/Nix) or qualify the reproducibility claim with an explicit forward-compatibility scope.
- [ ] **[m4]** Replace home-rolled `subset_refl` / `subset_trans` / `set_ext` with Lean4 stdlib equivalents or justify their inclusion in the theorem count.
- [ ] **[m5]** Shorten the abstract to ≤200 words focused on the central result and its difficulty.
- [ ] **[m6]** Update references to include Lean4 Mathlib, and at least one prior Lean4 `Option`-monad or partial-function formalization.
