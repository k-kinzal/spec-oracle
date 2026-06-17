# Reviewer #3 Report: UAD/f Two-Operator Kernel under Partial Projections

**Venue target:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

## 1. Overall Recommendation

**Minor Revision**

The paper presents a coherent, well-scoped mechanized kernel. The claim/non-claim separation is admirably explicit, the assumption matrix is well-structured, and the theorem-to-file traceability is unusually thorough for a submission of this type. The blocking issues below are real but addressable without fundamental rework.

---

## 2. What Is Already Acceptance-Level

**Claim/non-claim discipline (§0.1–0.2):** The explicit non-claims list is rare and valuable. Distinguishing "no proof that a concrete regex or LLM extractor satisfies adequacy assumptions" from what is proven removes a large class of reviewer objections preemptively.

**Assumption matrix (appendix):** The table format mapping each theorem to its required assumptions and the failure mode if removed is publication-ready. This is stronger than typical supplementary material.

**Axiom audit (§4.3):** Per-theorem `#print axioms` disclosure with explanation of *why* `Classical.choice` appears in `preimage_compose` but not `lifted_transfer` (the proof-shape asymmetry note) is exactly the right level of rigor for ITP/CPP.

**Counterexample completeness (§5.3–5.4):** Mechanizing both `transfer_fails_without_hproj` and the adequacy `E ≠ proj` counterexample in executable Lean demonstrates that hypotheses are non-redundant rather than cosmetic. This is a genuine contribution of the mechanization approach.

**Reproducibility script (`reproduce_formal.sh`):** Hash-pinned, exit-on-error, checks theorem count, sorry count, and LOC. This meets or exceeds artifact requirements at most target venues.

**Partiality-specific non-adjointness (§3.7):** The proof skeleton is clean and the guardrail framing is appropriately modest ("not claimed as standalone mathematical novelty").

---

## 3. Blocking Issues

### B1. `UAndOn_subset_UAndMayOn` listed in §4.5 traceability table but absent from theorem catalog count category

**Section §4.5** includes `UAndOn_subset_UAndMayOn` in the must/may operator laws row of the traceability table. However, **§4.6 and the theorem catalog** list the 22-count "core theorem interfaces" set, and `UAndOn_subset_UAndMayOn` is not in that set. It is also not listed in the supporting lemma section of the catalog file (`U0Spec/Construction.lean` lists 19 theorems, which can be cross-checked). If `UAndOn_subset_UAndMayOn` is a theorem declaration (not just a lemma with a different keyword), it must appear in the count reconciliation explicitly. If it is omitted from the 22-count intentionally, the traceability table entry needs a note explaining why it is in the table but not in the core-theorem count.

**Required fix:** Either add `UAndOn_subset_UAndMayOn` to the 22-count set with justification, or add a footnote to the traceability table clarifying its role-category placement.

---

### B2. `consistent_transport_left` mentioned in §3.4 but absent from theorem catalog

**Section §3.4** states: "Derived corollary `consistent_transport_left` (same file) transports pairwise consistency along proved lifted-subset relations." The theorem catalog for `paper/lean/UadfU0/InterLayer/Transfer.lean` lists only `lifted_transfer` and `consistent_transport_left`—wait, checking the catalog: the catalog lists exactly two theorems for `Transfer.lean`: `lifted_transfer` and `consistent_transport_left`. However, the role-category breakdown in §4.6 lists `lifted_transfer` as core (it appears in the 22-count list), but `consistent_transport_left` is not in the 22-count list. Under the accounting: 72 − 22 − 23 = 27, so it must be in the supporting-lemma count. This is defensible but the manuscript never explicitly places `consistent_transport_left` in any named category, creating an implicit gap. A reviewer counting from §3.4's prominent discussion of this corollary will expect to find it in the core set or see a clear reason it is not.

**Required fix:** Add `consistent_transport_left` to the supporting-lemma list in §4.6 explicitly, or justify why the 22-count core set excludes it despite the prominence of §3.4's treatment.

---

### B3. `reproduce_formal.sh` LOC check will fail on any reviewer machine with different whitespace behavior from `wc -l`

The script uses:
```bash
loc_total="$(wc -l $(rg --files UadfU0) | tail -n 1 | awk '{print $1}')"
if [ "$loc_total" != "1703" ]; then
```

`wc -l` on macOS produces leading spaces; `awk '{print $1}'` strips them, so this is portable. However, `rg --files UadfU0` without a `--` separator or explicit path may behave differently depending on whether the reviewer's `ripgrep` version expands the argument as a directory or a pattern. More critically, `$(rg --files UadfU0)` expands to a **space-separated list** passed as shell word-split arguments to `wc -l`, which will fail if any filename contains spaces and will produce different totals if the file ordering differs across platforms (though `wc -l` summing is order-independent). The deeper issue: the `tail -n 1` extracts the grand total line, which depends on `wc -l`'s grand-total format—this format is standard on POSIX but the exact whitespace is implementation-defined.

The hash checks are solid. The LOC check as written is fragile and could produce a false failure on a reviewer's machine, causing them to reject the artifact as non-reproducible when the Lean proofs are fine.

**Required fix:** Replace the LOC check with a more portable form:
```bash
rg --files UadfU0 | xargs wc -l | tail -n 1 | awk '{print $1}'
```
or document clearly that the LOC check is informational and should not cause `exit 1` on mismatch. Alternatively, convert the LOC check to a range check (`[ "$loc_total" -ge 1700 ]`) with a comment that exact count may vary by platform newline handling.

---

### B4. `UStar` parametricity not adequately distinguished from prior constructions in the related-work section

**Section §3.8** and the theorem family `UStar_subset_UAndOn` treat `UStar` as a pure theorem parameter ("it is not constructed by this kernel; theorem statements are parametric in `UStar`"). This is a correct and important design choice. However, §7 (related work) does not distinguish this parametric treatment from ideal-specification constructions in the refinement calculus tradition (Back and von Wright, ref 5) or in specification-refinement frameworks. A reader familiar with Back/von Wright will ask: is `UStar` the same as the "angelic specification" or "weakest prespecification" in that tradition? The paper does not engage with this.

This matters for acceptance at FM/FASE because parametric ideal-root treatment is the theoretical novelty of §3.8, and without positioning it against the refinement tradition, reviewers from that community cannot assess whether it is new or a re-presentation.

**Required fix:** Add 2–3 sentences in §7 (or a new §7.8) distinguishing the parametric `UStar` treatment from Back/von Wright ideal specifications: specifically, note that Back/von Wright construct the weakest specification from a given set of programs, whereas here `UStar` is an arbitrary predicate parameter and theorems give conditions under which layers' lifted sets approximate it—making the theorems conditional soundness/completeness results rather than construction theorems.

---

## 4. Minor Editorial Issues

**M1. §2.3 composite excerpt labeling.** The note "(Pedagogical composite excerpt across … canonical placement is listed in §2.5)" is correct but appears *inside* the code block's comment section in the manuscript. This will likely render oddly in conference proceedings. Move the pedagogical note to a caption or footnote outside the code block.

**M2. §3.3 "Difference from total-map-only intuition" paragraph.** The third bullet says "Therefore `U0`/`UAnd` separation here is not only order-theoretic; it is policy-sensitive under partiality." This is the key claim of §3.3 but it is introduced as a bullet without a theorem citation. The preceding bullets reference specific theorem names; this concluding one does not. Cite `UAndOn_subset_UAndMayOn` or `preimage_subset_preimageMay` here.

**M3. §4.3 item 4.** "does not use `open Classical`" — this phrasing is technically accurate but potentially misleading for ITP/CPP audiences who know that `Classical.choice` is still accessible without `open Classical`. The sentence already continues with the correct explanation, but the opening clause may cause a double-take. Consider rewriting to: "Core files do not use `open Classical` or `open Finset`; however, `Classical.choice` remains accessible as a kernel-level constant and appears in some proof terms as disclosed in the axiom audit below."

**M4. §6.1 reference note.** "these baseline APIs are cited for comparison (for example Mathlib-style interfaces), not imported dependencies of this artifact." — Lean readers will want to know the *specific* Mathlib lemma names being compared to (e.g., `Set.preimage_mono`, `Set.preimage_comp`). Without these, the delta claim in §6.1 reads as prose assertion rather than technically grounded comparison. Add specific Mathlib API names in parentheses.

**M5. §9 manifest hash.** The SHA256 in the script is:
```
8c098d788704fb7c279c7004a1f492723bd892acf2500483665ae39e7a00a6e7
```
This is 63 hex characters. SHA256 produces 64 hex characters. This appears to be a truncated hash (missing leading or trailing character). Verify and correct.

**M6. RQ-to-theorem matrix (§1.5).** `RQ2` resolution policy (§1.3) says it resolves when `lifted_subset_preimage_domain` and `U0_witness_projects_to_some_domain` are used. The matrix in §1.5 lists `Construction.lean` as the file but `U0_witness_projects_to_some_domain` is in the `Construction.lean` theorem list (catalog confirms: it is item 19 of 19). However, `lifted_subset_preimage_domain` is listed in §3.1 as a foundational lemma (supporting, not novelty) and is also in `Construction.lean`. The matrix is correct but this cross-reference is hard to follow because §3.1 explicitly calls these "support lemmas" while §1.3 calls them RQ2 resolution evidence. Add a sentence in §3.2 explicitly saying "these two theorems, classified as support lemmas in §3.1, operationally resolve RQ2 as specified in §1.3."

---

## 5. Final Checklist to Reach Acceptance

- [ ] **B1:** Resolve `UAndOn_subset_UAndMayOn` role-category discrepancy between §4.5 traceability table and §4.6 theorem-count set.
- [ ] **B2:** Explicitly categorize `consistent_transport_left` in §4.6 supporting-lemma list.
- [ ] **B3:** Fix or relax the LOC check in `reproduce_formal.sh` for cross-platform portability; or document it as informational only.
- [ ] **B4:** Add §7.8 or extend §7 to position parametric `UStar` against the Back/von Wright refinement calculus tradition.
- [ ] **M5:** Verify and correct the 63-character SHA256 hash (should be 64 hex digits).
- [ ] **M4:** Add specific Mathlib API names (`Set.preimage_mono`, `Set.preimage_comp`, `GaloisConnection`) in §6.1 delta comparison.
- [ ] **M6:** Add cross-reference sentence in §3.2 bridging §3.1's "support lemma" label with §1.3's "RQ2 resolution" claim.
- [ ] **M1–M3:** Editorial fixes as noted (code block caption placement, missing theorem citation in §3.3, `open Classical` phrasing in §4.3).
