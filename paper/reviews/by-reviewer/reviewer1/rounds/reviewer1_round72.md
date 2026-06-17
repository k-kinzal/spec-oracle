# Formal-Methods Paper Review — Reviewer #1 (Strict)

---

## 1. Overall Recommendation

**Major Revision**

The mechanization appears technically solid and the assumption-audit methodology is commendable. However, the paper has significant framing problems that prevent acceptance: novelty claims are under-specified at theorem level, the RQ-to-contribution mapping contains gaps, and several definitions lack semantic grounding that reviewers at FM/ITP/CPP will expect.

---

## 2. Strong Points

1. **Assumption-audit discipline**: The explicit `hproj`/`hA`/`hcomm` hypothesis interfaces and the corresponding counterexample mechanizations (`TransferCounterexample.lean`, `AdequacyCounterexample.lean`) are methodologically strong. This is the clearest value-add over informal treatments.

2. **Must/may split mechanization**: Explicitly separating `preimage`/`preimageMay` and `semanticPullback`/`semanticPullbackMay` with named bridge theorems is architecturally clean.

3. **Non-adjointness guardrail**: `no_left_adjoint_of_partial` is a precise, mechanized boundary condition. The proof skeleton is tight.

4. **Theorem-to-file traceability**: The §4.5 table and `theorem_catalog.md` cover all 70 declarations with file references. This is above average for mechanized papers.

5. **Axiom disclosure**: Per-theorem `#print axioms` reporting (§4.3) with explanation of why `Classical.choice`/`Quot.sound` appear is thorough and reviewer-friendly.

6. **Non-claims section (§0.2)**: The explicit enumeration of what is *not* claimed is unusually careful and prevents overclaiming.

---

## 3. Major Concerns (Must-Fix)

### M1. Novelty framing is too diffuse; no single theorem-level novelty statement

**Location**: §0.1 Claims, §6, §6.1

The paper frames novelty as "combination-level: one auditable kernel that simultaneously fixes heterogeneous carriers, partial projections, assumption interfaces, and counterexample-backed boundary theorems." This is a packaging claim, not a theorem-level novelty claim.

FM/ITP/CPP reviewers will ask: *which theorem, if any, is not derivable from existing library primitives by short composition?*

The paper explicitly says in §6.1: "we do not claim these mathematical identities are new." But it does not provide a single theorem whose *statement* is new relative to prior work. The "combination" framing is insufficient: combination papers require a technical property of the combination (e.g., impossibility of achieving it by composition of simpler pieces, or a proof that joint assumptions create non-trivial interdependencies).

**Required revision**: State at least one theorem (or theorem family) where the joint structure—partial projection + heterogeneous carriers + assumption interface—is *necessary* for the theorem to be statable or provable. Provide a brief argument. Alternatively, reframe explicitly as a methodology/infrastructure paper and justify that framing against the target venues' stated scope.

---

### M2. RQ1 and RQ2 are marked "supporting" but never resolved in the paper body

**Location**: §1.3, §1.5, §3.1, §3.2

The traceability matrix (§1.5) states: "Primary RQs for this formal paper are RQ3, RQ4, and RQ5. RQ1 and RQ2 are supporting questions."

However:
- RQ1 asks whether heterogeneous inverse images can be defined *consistently*. "Consistent" is never formally defined. The paper shows a definition exists but does not state a consistency theorem (e.g., well-typedness under dependent-index substitution, or coherence under reindexing).
- RQ2 asks whether `A(i) ⊆ D(i)` can be "lifted into root-side witness validity guarantees." The answer is given by `lifted_subset_preimage_domain` and `U0_witness_projects_to_some_domain`, but neither the question nor the answer is articulated precisely in prose. A reader cannot reconstruct what "lifted validity guarantee" means formally.

**Required revision**: Either promote RQ1/RQ2 to full problem statements with formal answers, or remove them from the RQ list and fold the relevant lemmas into a "definitional infrastructure" subsection without RQ framing.

---

### M3. `SpecSet` alias vs. Mathlib `Set` — design choice is under-justified

**Location**: §2.1

The paper states: "`SpecSet α := α -> Prop` — this is a local alias in `UadfU0.Definitions.Model`, not a direct use of Mathlib `Set α`."

The stated reason is "to expose all assumptions through a minimal Lean-core dependency surface." This is a legitimate choice, but:

1. The paper claims in §6.1 that the delta over "standard theorem-library practice" includes combining heterogeneous carriers with partial projections. But without Mathlib, lemmas like `preimage_monotone` and `preimage_union` must be reproved. The paper does not compare proof complexity or correctness risk against the Mathlib approach.
2. Reviewers at CPP/ITP will ask: does the Mathlib-free approach introduce any proof gaps or unverified assumptions that Mathlib would have covered? The paper asserts no `sorry` but does not argue that the reproved lemmas are equivalent to their Mathlib counterparts in all relevant senses.

**Required revision**: Add a paragraph explicitly justifying the Mathlib-free choice beyond dependency surface minimization. Either argue it is strictly equivalent (possibly with a statement), or acknowledge the tradeoff in §8 (Limitations).

---

### M4. `semanticPullback` and abstract relation `E` — motivation is circular

**Location**: §3.6, motivation paragraph

The motivation for introducing abstract `E` states: "separating them allows theorem-level reasoning before committing to a concrete extractor implementation, this separation is required to express mismatched cases (`E ≠ graph(proj)`) where one-sided adequacy still holds."

But the notion of "adequacy" is defined *in terms of `E`*. If `E = graph(proj)`, adequacy collapses to set-equality. The separation is only non-trivial when `E ≠ graph(proj)`. The paper does not state what conditions on `E` are required for the theorems to be informative (non-trivial), nor does it give a formal characterization of the class of `E` for which the one-sided results are strict (i.e., one holds without the other).

The `AdequacyCounterexample.lean` provides one instance (`EPlus1`), but one example does not characterize the class.

**Required revision**: Add a remark or theorem stating a sufficient condition (or necessary-and-sufficient condition) on `E` under which one-sided adequacy is strict (i.e., sound holds without complete or vice versa). Even an informal statement with a proof sketch suffices.

---

### M5. `IdealRoot.lean` theorems — `UStar` as theorem parameter is under-explained

**Location**: §3.8

`UStar : SpecSet α` is described as "an explicit theorem parameter denoting ideal-root predicate (it is not constructed by this kernel; theorem statements are parametric in `UStar`)."

This design choice is not explained in relation to the problem statement. The paper's abstract and §1.1 motivate the problem as: "ideal complete root specification `U*` is usually unavailable in practice." Then §3.8 takes `UStar` as a free parameter. This means the theorems in `IdealRoot.lean` say: *if you have `UStar` and it satisfies `hNecessaryOnDom`, then...* — which is conditional on having `UStar` in the first place.

Reviewers will ask: what does this buy beyond the trivial observation that if assumptions hold then conclusions follow? The connection between "unavailability of `U*`" (§1.1) and "parameterize over `UStar`" (§3.8) is not made explicit.

**Required revision**: Add a paragraph in §3.8 explaining the methodological value: is the point that these theorems give *sufficient conditions* practitioners can check? That they characterize the *gap* between `UStar` and `UAndOn`? State what the theorems are actually being used to show at a conceptual level.

---

## 4. Minor Concerns

### m1. §4.6 Role-group counts are not self-consistent with theorem catalog

The paper states: core theorem interfaces = 22, supporting lemmas = 27, example-level = 21 (total = 70). But the theorem catalog (`theorem_catalog.md`) does not annotate which category each theorem falls into. Reviewers cannot independently verify the split. The `CaseStudy/PasswordPolicy.lean` theorems (4) are not mentioned in the role-group breakdown.

**Fix**: Add a column to `theorem_catalog.md` with role category per theorem, or add a footnote explaining how `PasswordPolicy` theorems are counted.

---

### m2. §3.3 "policy-sensitive under partiality" claim is asserted but not formalized

The paper states: "`U0`/`UAnd` separation here is not only order-theoretic; it is policy-sensitive under partiality." This is an interesting claim but it is not supported by a theorem. It is an informal interpretation.

**Fix**: Either formalize this (e.g., a theorem showing that different `none`-handling policies yield different `U0`/`UAnd` relationships), or qualify the sentence as informal motivation.

---

### m3. §7 Related Work lacks explicit comparison to Alloy/Z/Event-B multi-view consistency literature

The paper cites Nuseibeh et al. (ViewPoints, 1994) and Wirsing/Knapp (2004) but does not compare with more recent multi-view consistency mechanization work (e.g., Semeráth et al. on partial model consistency, or Macedo et al. on Alloy-based consistency checking). Given the target venues include FASE and TACAS, this gap will be noticed.

**Fix**: Add 1–2 sentences per relevant recent work, or add a paragraph acknowledging the gap.

---

### m4. §2.3 "Pedagogical composite excerpt" note is confusing

The comment "(Pedagogical composite excerpt across ... canonical placement is listed in §2.5)" implies the excerpt may not compile as-is. For a formal-methods paper, reviewers expect all code excerpts to either compile standalone or be clearly marked as simplified.

**Fix**: Either provide a file path and line range that reviewers can verify in the artifact, or state explicitly that the excerpt is simplified and what is omitted.

---

### m5. Abstract overpromises on "failure modes that arise only under partial projections"

The abstract states the paper has "emphasis on failure modes that arise *only* under partial projections." But the non-adjointness theorem (`no_left_adjoint_of_partial`) and the `none`-branch composition are the only examples given. The claim "only" is not established; it is possible that similar failure modes appear in other settings (e.g., partial functions in classical set theory).

**Fix**: Weaken "only" to "specifically" or "primarily," or add a brief argument for why these failure modes cannot arise in total-map settings.

---

## 5. Required Revisions Checklist

| # | Location | Required action | Priority |
|---|---|---|---|
| R1 | §0.1, §6, §6.1 | State one theorem or theorem family whose stateability/provability depends on the joint structure (partiality + heterogeneity + assumption interfaces), or reframe as methodology paper with explicit venue justification | Must-fix (M1) |
| R2 | §1.3, §1.5, §3.1–3.2 | Resolve RQ1/RQ2 with formal answers or remove from RQ list | Must-fix (M2) |
| R3 | §2.1 | Justify Mathlib-free design choice with proof-equivalence argument or acknowledge tradeoff in §8 | Must-fix (M3) |
| R4 | §3.6 | Characterize conditions on `E` under which one-sided adequacy is strict (formal or informal with proof sketch) | Must-fix (M4) |
| R5 | §3.8 | Explain methodological value of parametric `UStar` relative to the unavailability motivation in §1.1 | Must-fix (M5) |
| R6 | `theorem_catalog.md`, §4.6 | Add role-category column or footnote; clarify PasswordPolicy theorem counting | Minor (m1) |
| R7 | §3.3 | Formalize "policy-sensitive under partiality" claim or qualify as informal | Minor (m2) |
| R8 | §7 | Add coverage of recent multi-view consistency mechanization (post-2010) | Minor (m3) |
| R9 | §2.3 | Clarify compilability status of code excerpt or provide artifact line references | Minor (m4) |
| R10 | Abstract | Weaken "only" to "specifically/primarily" regarding partial-projection-exclusive failure modes | Minor (m5) |
