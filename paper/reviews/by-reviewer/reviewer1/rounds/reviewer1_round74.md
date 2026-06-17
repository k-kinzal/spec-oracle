# Formal-Methods Paper Review: UAD/f Two-Operator Kernel under Partial Projections

**Reviewer #1 (Strictest)**
**Target venues: FM / ITP / CPP / TACAS / FASE / Formal Aspects**

---

## 1. Overall Recommendation

**Major Revision**

The mechanization appears technically sound and the presentation is thorough, but several issues around novelty framing, assumption scope, and claim precision require substantive revision before the paper meets the bar for the listed venues.

---

## 2. Strong Points

1. **Assumption auditability.** The explicit assumption matrix (§3.4, §3.5, §3.6, Appendix) and per-theorem axiom disclosure (§4.3) are exemplary. Same-root linkage (`hproj`) being surfaced as a non-redundant hypothesis with a mechanized counterexample (`transfer_fails_without_hproj`) is a genuine contribution to proof-engineering practice.

2. **Must/may discipline.** The explicit split between `preimage`/`preimageMay` and the mechanized counterexample in `AdequacyCounterexample.lean` make the partiality boundary visible in a way that prose specifications cannot.

3. **Vacuous-truth edge case.** `UAndOn_empty_eq_univ` being mechanized and surfaced as an operational warning (§3.3, §5.3) shows disciplined awareness of edge cases that are often silently elided in informal treatments.

4. **Traceability apparatus.** The RQ-to-theorem matrix (§1.5), theorem-to-file table (§4.5), and role breakdown (§4.6) give reviewers a clear audit path. The `reproduce_formal.sh` script with locked hashes is appropriate rigor.

5. **Honest non-claims.** §0.2 explicitly disclaims extractor correctness, statistical validity, and full constructivity. This prevents scope inflation.

---

## 3. Major Concerns (must-fix)

### M1. Novelty framing is circular: "combination-level novelty" needs independent grounding

§6 ("What Mechanization Added Beyond Textbook Identities") and §6.1 both retreat to *combination-level novelty*: the claim is that no existing library bundles exactly this set of definitions together. This framing is unfalsifiable and insufficient for FM/ITP/CPP. The following must be addressed:

- **M1a.** The paper must articulate what *new theorem-level insight* arises that could not be directly obtained by instantiating existing Mathlib/Isabelle partial-function and order-theory APIs with the given definitions. §6.1 lists "baseline capabilities" but does not show that combining them into this package requires non-trivial proof engineering beyond assembly.
- **M1b.** `no_left_adjoint_of_partial` (§3.7) is stated in §3.7 as "not claimed as standalone mathematical novelty" and is called a "guardrail." If this is the closest theorem to a genuinely new result, its formal significance needs sharper framing—or the paper must identify which theorem, if any, constitutes the core formal result. Currently the manuscript oscillates between presenting itself as a library contribution and as a theorem contribution without committing to either.

### M2. `UStar` is purely parametric—ideal-root theorems are conditional trivialities

§3.8 and `U0Spec/IdealRoot.lean` introduce `UStar` as "an explicit theorem parameter." The theorems (e.g., `UStar_inter_projDomOn_subset_UAndOn`) are then direct unfolding of definitions once the necessary-condition hypothesis is granted:

> `hNecessaryOnDom : ∀ i, active i → (fun x => x ∈ UStar ∧ x ∈ M.projDom i) ⊆ M.lifted i`

Given this hypothesis, the theorem conclusion is essentially propositional logic. The paper does not explain what proof difficulty was overcome, and these 6 theorems occupy a full section (§3.8). Either justify why these are non-trivial, or demote to "supporting lemmas" in the role breakdown, adjusting the core-theorem count of 22 accordingly.

### M3. Adequacy abstraction over `E` is underspecified in relation to `proj`

§3.6 introduces abstract relation `E` and `semanticPullback(E,S)`. The soundness/completeness hypotheses are:
- Sound: `∀ x y, proj_i x = some y → E x y`
- Complete: `∀ x y, E x y → proj_i x = some y`

Under these definitions, `E = graph(proj_i)` is the only relation satisfying *both* sides simultaneously (for must semantics). The decomposition into `preimage_subset_semanticPullback_of_sound` and `semanticPullback_subset_preimage_of_complete` is then trivial by substitution. The paper claims the separation "allows theorem-level reasoning before committing to a concrete extractor implementation" (§3.6 motivation point 3), but:

- **M3a.** The interesting case—where `E` differs from `graph(proj)`—is handled only by the counterexample `AdequacyCounterexample.lean`. The paper should explain what class of relations `E` is intended to represent in practice and why the abstract theorems add reasoning power beyond direct use of `proj`.
- **M3b.** The adequacy counterexample (`EPlus1`) shows the decomposition is non-trivial under a specific divergence, but `EPlus1` is not connected to any realistic extractor model. The paper should either (a) provide a realistic motivating `E ≠ proj` scenario, or (b) clarify this is purely a proof-structure demonstration.

### M4. Reproducibility check has a brittle exact-LOC assertion

`reproduce_formal.sh` (and §4.4) hard-codes `LOC = 1703` and `theorem_count = 72`. Reviewers cannot verify these without running the build, and any legitimate editorial change (adding a comment, renaming a theorem) would break the script. For submission:

- **M4a.** The LOC check should be demoted to an informational output, not a hard failure assertion.
- **M4b.** The theorem count check should be replaced by a named-theorem membership check (i.e., verify the 22 core theorems by name, not by count), since count is sensitive to refactoring.

---

## 4. Minor Concerns

### m1. §2.3 labels code as "Pedagogical composite excerpt"—this risks misrepresenting the mechanization

§2.3 states the excerpt is a "pedagogical composite across" two files. If a reviewer or artifact evaluator reads this as a single coherent Lean block and attempts to typecheck it, it will fail. Use a clear visual separator or restructure so that each file's excerpt is separately identified.

### m2. Axiom footprint asymmetry explanation (§4.3, items 7–10) is verbose but incomplete

The explanation for `Classical.choice` appearing in `preimage_compose` (item 7) says it appears "because witness reconstruction is expressed through extensional equality over existential branches." However, the paper does not show why a constructive proof was not possible. For ITP/CPP audiences, the expected question is: *is this a limitation of the proof style or of the theorem itself?* A one-sentence answer ("the extensional equality proof style chosen here is not constructive; a constructive variant is possible but not developed") would suffice.

### m3. §7 (Related Work) positional statements are imprecise on Institutions

§7.2 states this paper contributes "a narrower but executable kernel" versus institutional frameworks. However, the `SpecSet α := α -> Prop` encoding with heterogeneous index is already a fragment of what Hets/CASL handle. The paper should acknowledge whether any part of the kernel is directly encodable as an Hets theory and whether that has been checked—or explicitly disclaim this comparison.

### m4. `RQ1` and `RQ2` resolution criteria (§1.3) are operational, not epistemological

The resolution policy states "`RQ1` is considered resolved when heterogeneous inverse-image definitions are type-correct and reused in core theorem families." This is a *mechanization criterion*, not a research question answer. RQ1 asks "Can we define induced inverse images consistently..."—the answer should explain *what difficulty was overcome*, not only that the definition type-checks.

### m5. §5.2 references `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` but this file is not in the provided submission files

The theorem catalog lists `PasswordPolicy.lean` with 4 theorems, but this file does not appear among the reviewed files. If it is part of the submission, it should be included. If excluded for space, the paper should note this and clarify whether these theorems are in the LOC/count totals.

### m6. `consistent_transport_left` is listed as a "derived corollary" in §3.4 but not in the core-22 or example-23 counts

Per the theorem catalog, `consistent_transport_left` is in `Transfer.lean` (theorem count: 2). The manuscript description (§3.4) calls it a "derived corollary" but the role breakdown (§4.6) does not explicitly assign it. Clarify whether it is a supporting lemma.

---

## 5. Required Revisions Checklist

| # | Section | Required action |
|---|---|---|
| R1 | §6, §6.1 | Replace "combination-level novelty" with a specific formal claim: either identify a theorem whose proof required non-obvious proof-engineering under this partiality model, or reframe the contribution as a *library design* contribution with explicit comparison to what an instantiation of Mathlib APIs would produce. |
| R2 | §3.7 | Either promote `no_left_adjoint_of_partial` as the central formal novelty and develop its significance, or explicitly state the paper's primary contribution is methodological/library-level (not theorem-level novelty). Pick one framing and be consistent throughout. |
| R3 | §3.8 | Justify non-triviality of ideal-root theorems given parametric `UStar`, or reclassify them as supporting lemmas and update §4.6 core-theorem count. |
| R4 | §3.6, §3.6.1 | Add a realistic motivating example for `E ≠ graph(proj)` where one-sided adequacy still holds and the decomposition provides actionable guidance; or clarify this is a proof-structure artifact. |
| R5 | `reproduce_formal.sh` | Remove hard-fail LOC assertion; replace theorem-count assertion with named-theorem membership check for the 22 core theorems. |
| R6 | §2.3 | Restructure or clearly label the "pedagogical composite" so that file boundaries are explicit and no excerpt is misread as a standalone typecheckable block. |
| R7 | §1.3 | Rewrite RQ1/RQ2 resolution criteria to state *what formal difficulty was overcome*, not only that type-checking succeeded. |
| R8 | §5.2 | Include `PasswordPolicy.lean` in the submission artifact, or add an explicit exclusion note and verify LOC/count totals exclude it consistently. |
