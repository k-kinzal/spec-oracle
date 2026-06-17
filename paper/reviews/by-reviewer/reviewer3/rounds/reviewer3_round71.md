## Reviewer #3 — Formal Methods Venue Review

**Submission:** "UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization"
**Target venues:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

## 1. Overall Recommendation

**Minor Revision**

The paper is on a credible trajectory for acceptance at ITP or CPP (FM/TACAS would require stronger positioning against prior mechanization work). The formal kernel is coherent, the claim/non-claim separation is unusually disciplined, and the mechanization is presented with commendable transparency. However, several items require clarification before acceptance: a terminological imprecision in §0.1, an underspecified traceability chain for §2.3 definition placement, an unresolved tension in §6 novelty framing, and missing quantification in the assumption matrix.

---

## 2. What is Already Acceptance-Level

**A. Claim/non-claim discipline (§0.1–§0.2)**
The explicit separation of claims from non-claims is exemplary and rare. Specifically, Non-claim §0.2.4 ("No claim that PoC behavior is a direct semantic proof") directly pre-empts a common reviewer objection. This should be preserved unchanged.

**B. Assumption-audited theorem design (§3.4–§3.6, Assumption Matrix)**
The pattern of naming proof obligations (`hproj`, `hA`, `hcomm`, `hSound`, `hComplete`) as named theorem arguments rather than prose side-conditions is methodologically sound. The assumption matrix in `appendix/assumption_matrix.md` is precise and complete for the listed core theorems. The fallback-claim column is particularly valuable.

**C. Mechanized failure-mode counterexamples (§5.3–§5.4)**
`transfer_fails_without_hproj` and `semanticPullback_not_subset_preimage_EPlus1` are non-trivial mechanized artifacts. These directly serve the stated goal of auditing assumption necessity, and their interpretation in §5.3–§5.4 is accurate.

**D. Axiom disclosure (§4.3)**
The per-theorem `#print axioms` disclosure is precise and matches expected behavior (`lifted_transfer` has no axioms; `preimage_compose` uses `Classical.choice` via extensional equality; `no_left_adjoint_of_partial` uses only `propext`). The explanation of *why* `Classical.choice` appears (extensional branch-elimination rather than a constructive normalization claim) is correct and honest.

**E. Reproducibility metadata (§4.4, §9)**
The combination of manifest hash, toolchain pin (`v4.27.0`), and portable hash-check command is sufficient for artifact replay. The build-evidence appendix records job count (42 jobs), LOC (1690), and theorem count (70) consistently across §4.4 and the appendix.

**F. Non-adjointness theorem (§3.7)**
The proof skeleton is correct and the non-claim framing ("mechanized guardrail, not standalone mathematical novelty") is appropriate. The theorem usefully blocks a class of unsound reasoning patterns.

---

## 3. Blocking Issues

**B1. §0.1 Claim 1 — "self-contained" is falsified by the axiom disclosure**

Claim §0.1.1 states "a self-contained typed UAD/f kernel." However, §4.3 discloses dependency on `propext`, `Classical.choice`, and `Quot.sound` for several core theorems, and explicitly notes these are "Lean4 core-level constants." The term "self-contained" will be read by a formal-methods reviewer as constructively closed or axiom-free. The paper is not axiom-free; it is *dependency-bounded* (Mathlib-free) and *axiom-disclosed*.

**Required fix:** Replace "self-contained" in §0.1 Claim 1 with a term that accurately characterizes the scope, for example: "Mathlib-free, axiom-disclosed typed UAD/f kernel." This is a one-sentence change but is logically necessary to avoid the claim contradicting §4.3.

**B2. §2.3 vs §2.5 — definition placement inconsistency**

§2.3 states "Definitions in `paper/lean/UadfU0/U0Spec/Construction.lean`" for the Lean excerpt that includes `preimage`, `Ui`, `lifted`, `U0On`, `UAndOn`, `U0`, and `UAnd`. However, §2.5 states: "Definition-placement note: `U0` is placed in `Definitions/Model.lean` as core root-side union operator. `UAndOn`/`UAnd` are placed in `U0Spec/Construction.lean`."

These two notes are in tension. The excerpt in §2.3 contains both `U0` and `UAndOn` under the label `U0Spec/Construction.lean`, but §2.5 says `U0` is in `Definitions/Model.lean`. The traceability table in §4.5 lists must/may operator laws (including `U0`-related ones) under `U0Spec/Construction.lean`.

**Required fix:** §2.3 must either (a) split the Lean excerpt to show which definitions are in which file, or (b) add an explicit note that the excerpt is a pedagogical composite and refers readers to §2.5 for canonical file placement. Without this fix, a reviewer attempting to verify the mechanization against the manuscript will encounter an immediate inconsistency.

**B3. §6 novelty framing — delta claim is asserted but not bounded against prior Lean mechanizations**

§6.1 states the delta against "baseline theorem libraries" but the comparison is generic ("standard total-function APIs"). The paper targets FM/ITP/CPP venues where specific prior Lean4 mechanizations are expected comparators (e.g., Mathlib's `Set.preimage`, `GaloisConnection`, or `Order.CompleteLattice` APIs, and any prior institution or multi-view mechanizations).

The paper explicitly chooses to not import Mathlib (noted in §2.1 as a design tradeoff). This is a legitimate choice, but it creates an obligation: the paper must characterize what Mathlib *would* and *would not* provide for the specific theorems claimed, and why the presented kernel adds value beyond composing Mathlib primitives.

The current §6.1 is written at the level of informal prose ("standard total-function APIs do not carry this full assumption interface"). This is likely correct but is unverified. A reviewer familiar with Mathlib's `GaloisConnection` and `Set.image`/`Set.preimage` API would ask: could `lifted_transfer` or `preimage_compose` be stated and proved in 20 lines using Mathlib's `Option.bind` lemmas and `Set.preimage_comp`?

**Required fix:** §6.1 must either (a) cite specific Mathlib theorem names that are closest analogues and state exactly what is missing from those analogues, or (b) explicitly bound the novelty claim to the *combination* (heterogeneous carriers + partial projections + named assumption interface + counterexample mechanization in one package) rather than to individual lemma novelty. Option (b) is already partially present in §6.1 item 1 but needs to be made the leading claim, with the Mathlib comparison subordinate to it.

---

## 4. Minor Editorial Issues

**M1. §1.3 / §1.5 — RQ1 and RQ2 role asymmetry not flagged in abstract**

The abstract lists five theorem families (transfer, composition, adequacy, non-adjointness, ideal-root linkage) but does not mention that RQ1 and RQ2 are "supporting questions" (this is stated only in §1.3). A reader scanning the abstract will expect RQ1/RQ2 to be primary. Either remove RQ1/RQ2 from the abstract implicit framing, or add the "primary/supporting" distinction to §1.2.

**M2. §3.3 — "same-root linkage" term introduced without cross-reference**

§3.4 introduces "same-root linkage" as the key property named `hproj`. §3.3 does not use this term, but it is conceptually needed for the `UAndOn_subset_U0On` proof (which requires at least one element in the active-set lifted predicate). A forward reference to §3.4 would aid readability.

**M3. §4.3 item 7 — "constructive rewriting...is possible in principle" is unverified**

The paper states: "constructive rewriting with explicit branch witnesses is possible in principle, but this manuscript fixes a concise extensional-equality proof style." This claim ("possible in principle") is an unverified assertion. If not verified, it should be weakened to "we do not claim constructive normalization; the axiom footprint is as reported."

**M4. §5.2 — PasswordPolicy case theorem scope**

The theorem catalog confirms `PasswordPolicy.lean` contains 4 theorems. §5.2 mentions only `checkConsistent_iff_allThree` and `req_projection_adequacy`. The other two theorems (`checkConsistent_true_implies_allThree`, `allThree_implies_checkConsistent_true`) are the proof directions that compose `checkConsistent_iff_allThree`. These should be referenced explicitly so the count is traceable.

**M5. §9 — hash check command uses relative path `paper/lean/lake-manifest.json`**

The hash check command in §9 uses path `paper/lean/lake-manifest.json` but the build command uses `cd paper/lean` first. These imply different working directories. A reviewer running the hash check from the repo root will succeed, but running it after `cd paper/lean` will fail with a path error. Add an explicit note: "run from repository root, not from `paper/lean`."

**M6. Assumption matrix — `UStar_subset_UAndOn` and `UStar_subset_UAnd` not in matrix**

The theorem catalog lists `UStar_subset_UAndOn` and `UStar_subset_UAnd` in `IdealRoot.lean`. These are not in the assumption matrix. While the assumption matrix covers core theorems, these two are close enough to `UStar_inter_projDomOn_subset_UAndOn` that their distinct premise structure (no domain restriction vs. domain-restricted) should be noted. The matrix row for `UStar_inter_projDomOn_subset_UAndOn` should cross-reference the simpler `UStar_subset_UAndOn` variant and explain what additional assumption the domain-restriction version drops (i.e., `UStar_subset_UAndOn` requires a stronger premise that `UStar` is globally necessary, not just on `projDomOn`).

---

## 5. Final Checklist to Reach Acceptance

| # | Item | Severity | Location |
|---|---|---|---|
| 1 | Replace "self-contained" in Claim §0.1.1 with "Mathlib-free, axiom-disclosed" | **Blocking** | §0.1 |
| 2 | Resolve §2.3 vs §2.5 definition-file placement conflict (split excerpt or add explicit composite note) | **Blocking** | §2.3, §2.5 |
| 3 | Bound §6.1 novelty delta against specific Mathlib comparators or make combination-level claim the lead | **Blocking** | §6.1 |
| 4 | Clarify RQ1/RQ2 "supporting" status in §1.2 or abstract | Minor | §1.2, Abstract |
| 5 | Add forward reference from §3.3 to §3.4 for "same-root linkage" term | Minor | §3.3 |
| 6 | Weaken "constructive rewriting possible in principle" to undisputed claim | Minor | §4.3 item 7 |
| 7 | Reference all 4 PasswordPolicy theorems in §5.2 for count traceability | Minor | §5.2 |
| 8 | Clarify working-directory context for hash-check command in §9 | Minor | §9 |
| 9 | Add `UStar_subset_UAndOn` vs `UStar_inter_projDomOn_subset_UAndOn` contrast to assumption matrix | Minor | appendix/assumption_matrix.md |

Items 1–3 must be resolved before acceptance. Items 4–9 can be addressed in a camera-ready pass. The formal content of the mechanization, the claim/non-claim discipline, and the reproducibility packaging are already at acceptance level. The revision required is editorial and framing-level, not mathematical.
