## Formal-Methods Venue Review: Strictest Reviewer Assessment

---

## 1. Overall Recommendation

**Weak Reject / Major Revision Required**

The paper is methodologically careful and the mechanization infrastructure is solid. However, it does not yet meet the acceptance bar for FM/ITP/CPP/TACAS at any of these venues in its current form. The primary obstacles are: (a) the novelty framing is insufficiently differentiated from what direct Mathlib instantiation would yield, (b) the "methodology/library-style track" positioning is not adequately grounded in a comparison to existing Lean4/Isabelle library-style papers at those venues, and (c) several theorem-level claims contain precision gaps that a reviewer can identify without running Lean. The paper is a borderline case for FASE or Formal Aspects if the framing issues are fixed.

---

## 2. Strengths

1. **Explicit assumption interfaces.** The `hproj`/`hA`/`hcomm` argument pattern is genuinely cleaner than embedding assumptions as prose side-conditions. The assumption matrix appendix is useful.

2. **Mechanized failure witnesses.** `TransferCounterexample.lean` and `AdequacyCounterexample.lean` are the strongest parts of the paper. Providing executable counterexamples for dropped assumptions is the correct methodology for an interface-contract contribution.

3. **Honest non-claims section (§0.2).** The paper explicitly disclaims extractor correctness, statistical validity, and temporal semantics. This is the right approach and reduces reviewer false-positives.

4. **Reproducibility completeness.** Hash-pinned manifest, Dockerfile, `reproduce_formal.sh` with hard checks for `sorry`-count and primary-theorem membership is close to best-practice for a Lean artifact submission.

5. **Must/may split with explicit policy.** The `preimageMay`/`semanticPullbackMay` separation with an explicit inconclusive-observation policy is a practically motivated design choice that is correctly mechanized.

6. **Axiom audit disclosure (§4.3).** Per-theorem `#print axioms` results are reported, and the asymmetry between `lifted_transfer` (no axioms) and `preimage_compose` (classical) is explained. Few mechanization papers do this.

---

## 3. Major Concerns (Blocking)

### M1. Novelty framing versus Mathlib baseline is insufficiently sharp

Section 6.1 claims the delta over Mathlib is the "combination" of heterogeneous carriers + partial projections + domain/admissibility separation in one model. However, the paper does not demonstrate that this combination cannot be straightforwardly assembled from `Set.preimage_mono`, `Set.preimage_comp`, `GaloisConnection`, and `Finset`/`iSup`/`iInf` in Mathlib. A Mathlib-aware reviewer will ask: if we define `carrier : ι → Type`, `proj : (i : ι) → α → Option (carrier i)`, and `preimage` using `Option.elim`, what is the obstacle to reusing existing Mathlib infrastructure for §3.2–§3.5?

The paper's answer ("we want a Mathlib-free dependency surface") is a packaging preference, not a theorem-level gap. The five delta points in §6.1 are real, but they are stated too abstractly to evaluate. Specifically: the paper does not show a concrete Mathlib instantiation attempt that fails or requires non-trivial adaptation. Without this, the claim "direct baseline reuse is insufficient" is unverifiable.

**Required:** Either (a) provide a concrete failed-instantiation argument, e.g. a Lean snippet showing where the Mathlib path breaks and why, or (b) reframe the contribution as explicitly pedagogical/self-contained and position accordingly—but then address why this is publishable as a research paper rather than a Lean tutorial.

### M2. RQ framing does not match theorem-level resolution

RQ1 asks "can we define induced inverse images consistently with heterogeneous carriers?" The answer is a definition—`preimage` in `Model.lean`—which is trivially yes. The RQ framing implies there is a non-trivial obstacle; the paper must state what that obstacle is. Similarly, RQ2 ("can `A(i) ⊆ D(i)` be lifted?") has an obvious yes-answer unless there is a typing or universe obstacle. If the obstacle is universe polymorphism or a Lean4-specific elaboration issue, state it explicitly.

RQ3–RQ5 are better but still loose. "Can `U0` and `UAnd` be defined coherently in one model?" is not a research question without specifying what coherence means formally. The paper uses LUB/GLB characterizations for this but does not explain why a trivial definition (`fun x => ∃ i, ...` and `fun x => ∀ i, ...`) requires research-level justification.

**Required:** For each RQ, state precisely (a) what obstacle makes the answer non-obvious, and (b) what would a negative answer to the RQ mean formally.

### M3. Transfer theorem (`lifted_transfer`) novelty justification is insufficient

The paper claims `lifted_transfer` is "not a set-theory tautology because same-root witness linkage is required." This is true, but the theorem is a straightforward implication over existentials. The non-triviality claim rests entirely on the counterexample (`TransferCounterexample.lean`). However, a reviewer familiar with dependently-typed set formalization will recognize this as an instance of the general pattern: "codomain-only relational transfer fails; you need a correlated witness." This pattern appears in countless mechanization papers (e.g., simulation proofs, abstraction relations in verified compilers).

The paper needs to explain what is specific to the UAD/f setting that makes this instance worth a published theorem, beyond "we mechanized it and showed the counterexample."

**Required:** Either (a) show that the combination of partial projections + heterogeneous carriers creates a non-trivial proof obligation not present in the standard simulation/bisimulation pattern, or (b) reframe `lifted_transfer` as infrastructure (supporting, not core) and strengthen the novelty anchor to `preimage_compose` under `Option.bind` or the adequacy decomposition.

### M4. Adequacy decomposition: abstract `E` justification is incomplete

Section 3.6 separates `proj` from `E` "to allow theorem-level reasoning before committing to a concrete extractor." This is methodologically sound. However, the paper does not characterize the space of relations `E` for which adequacy is non-trivial. The `EPlus1` counterexample shows soundness can hold while completeness fails, but this is immediate from the definitions. The formal contribution would be stronger if the paper stated: what is the weakest condition on `E` under which `preimage_eq_semanticPullback` holds? (Answer: `E = graph(proj)` is sufficient but the paper does not prove it is necessary, or characterize the gap.)

**Required:** State whether `preimage_eq_semanticPullback` characterizes exactly the `E = graph(proj)` case or a wider class, and mechanize this characterization or explicitly disclaim it.

### M5. Composition theorem scope is overstated relative to proof complexity

Section 3.5 says `preimage_compose` is non-trivial under partiality because "impossible `none` branches must be eliminated constructively." The proof skeleton described is a straightforward case analysis. The classical axiom usage in the axiom audit (`Classical.choice` appearing) suggests the proof goes through classical reasoning over existentials—which is fine but undermines the constructivity framing. The paper says "a constructivity-preserving re-proof is outside this scope," but then cannot claim constructive novelty. This leaves the theorem's status unclear: is it a constructive result with a classical proof-of-convenience, or is it inherently classical?

**Required:** Clarify the constructivity status of `preimage_compose` precisely. If the proof is classical, do not frame the `none`-branch elimination as a constructive contribution.

### M6. Reproducibility contract has one ambiguity that can fail reviewer validation

`reproduce_formal.sh` runs `rg -n '\bsorry\b' UadfU0` and checks for zero matches. However, `sorry` in a string literal or comment would also match `\bsorry\b` with ripgrep's default. Conversely, `sorry` used as a local variable name would pass. More importantly: the script does not verify that the built artifact corresponds to the source (no `.olean` hash check or `lake build --fresh`). A reviewer who runs `lake build` on a pre-cached environment may get a false positive.

**Required:** Add `lake clean` before `lake build` in `reproduce_formal.sh`, or document explicitly why cached builds are acceptable. Also tighten the `sorry` grep pattern to Lean keyword context (e.g., line-level check excluding comments and strings, or use `--type lean`).

---

## 4. Minor Concerns

### m1. Notation inconsistency: `Ui` vs `A`

The paper introduces `Ui(i) := A(i)` as a "compatibility alias" but uses both interchangeably across sections. §2.2 says "throughout this paper, `Ui` and `A` denote the same predicate"—but the theorem signatures use `M.Ui j` while the mathematical notation uses `A(j)`. Reviewers checking theorem statements against mathematical prose must mentally substitute. Pick one notation or add a single-line mapping table at first use.

### m2. `UStar` linkage theorems are categorized as supporting but discussed at length

`UStar_*` theorems occupy most of §3.8 and appear in the assumption matrix. If they are supporting (as §4.6 states), the paper should either promote them to primary (with a corresponding RQ) or reduce §3.8 to a paragraph. The current length creates a false impression of centrality.

### m3. RQ-to-theorem traceability matrix (§1.5) duplicates §4.5

Table in §1.5 and table in §4.5 cover overlapping ground. Merge or cross-reference to reduce confusion.

### m4. Abstract does not state the Lean4 toolchain version

The abstract mentions "Lean4 mechanization" but the toolchain version (`v4.27.0`) only appears in §4.3. The abstract should include the toolchain version since it affects reproducibility interpretation.

### m5. Definition-placement note in §2.5 is implementation detail, not scientific content

The note that "`U0` is placed in `Definitions/Model.lean` as core root-side union operator" while `UAndOn` is placed elsewhere is a file organization detail. Move to appendix or footnote.

### m6. References list is thin for Lean4/ITP venues

For CPP or ITP, reviewers will expect citations to: recent Lean4 mechanization papers (e.g., Mathlib4 CPP 2024), view consistency formalizations in Isabelle/HOL (Gogolla et al.), and the Hets paper (Mossakowski) which is listed but not discussed in the body. The `de Moura and Ullrich` reference for Lean4 should use the correct CADE 2021 citation. Reference 9 (Mossakowski) is incomplete (no page/volume numbers).

### m7. `UAndOn_empty_eq_univ` vacuous-truth discussion is repeated

The vacuous-truth edge case is mentioned in §3.3, §5.3, and §8. Consolidate to one location with back-references.

### m8. Lean definition excerpts in §2.3 should note whether they are verbatim

The excerpts say "exact file-local snippets" but the surrounding `variable` context is described separately. A reviewer trying to reproduce manually needs to know whether copying the excerpt into a fresh file works. Clarify.

---

## 5. Required Revision Checklist

| # | Priority | Item |
|---|---|---|
| R1 | Blocking | Provide concrete Mathlib-instantiation comparison showing where the partial/heterogeneous combination forces deviation from baseline APIs (addresses M1) |
| R2 | Blocking | For each RQ, state the formal obstacle that makes the answer non-obvious; reformulate RQ1/RQ2 if they reduce to trivial definitions (addresses M2) |
| R3 | Blocking | Justify `lifted_transfer` as a published result beyond "counterexample exists"; show what is UAD/f-specific (addresses M3) |
| R4 | Blocking | Characterize or disclaim: does `preimage_eq_semanticPullback` hold iff `E = graph(proj)`, or for a wider class? (addresses M4) |
| R5 | Blocking | Clarify constructivity status of `preimage_compose`; do not frame classical proof as constructive contribution (addresses M5) |
| R6 | Blocking | Add `lake clean` to `reproduce_formal.sh` or justify cached builds; tighten `sorry` detection pattern (addresses M6) |
| R7 | Minor | Unify `Ui`/`A` notation throughout |
| R8 | Minor | Reduce §3.8 to proportional length or promote `UStar_*` to a primary RQ |
| R9 | Minor | Merge §1.5 and §4.5 tables |
| R10 | Minor | Add toolchain version to abstract |
| R11 | Minor | Move definition-placement notes to appendix |
| R12 | Minor | Expand related-work references for Lean4/ITP venue expectations |
| R13 | Minor | Consolidate vacuous-truth discussion to one section |
| R14 | Minor | Clarify that Lean excerpts in §2.3 are verbatim and self-contained |

---

**Summary judgment:** The mechanization infrastructure is credible and the assumption-auditing methodology is the right approach. The paper's ceiling is FASE or Formal Aspects if M1–M3 are addressed; FM/ITP/CPP/TACAS require a more convincing novelty argument. The reproducibility infrastructure (minus M6) is one of the stronger aspects and should be preserved.
