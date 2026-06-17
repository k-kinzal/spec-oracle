# Review: UAD/f Two-Operator Kernel under Partial Projections

**Reviewer #3 — Acceptance-Focused / Strict on Logical Consistency**

---

## 1. Overall Recommendation

**Minor Revision**

This paper presents a clean, well-scoped mechanized kernel with explicit assumption auditing—exactly the kind of contribution FM/ITP/CPP venues value. The claims are honest, the non-claims are unusually precise, and the theorem-to-file traceability is stronger than typical submissions. The blocking issues below are real but fixable without structural rework.

---

## 2. What is Already Acceptance-Level

**Claim/non-claim discipline (§0.1–0.2)** is exemplary. The paper explicitly disavows extractor correctness, statistical validity, and standalone novelty for individual guardrail theorems. This precision is rare and should be preserved exactly as-is.

**Assumption matrix (appendix)** is a genuine contribution to reproducibility practice. The fallback-claim column is particularly valuable—it tells a reader what survives if a hypothesis fails.

**Counterexample-backed assumption boundaries (§3.3, §5.3–5.4)** are mechanized, not just asserted. `transfer_fails_without_hproj` and `AdequacyCounterexample.lean` serve as executable falsification witnesses. This directly addresses the core concern in formal-methods review: are the hypotheses necessary or decorative?

**Non-adjointness guardrail (§3.7)** is correctly scoped. The paper does not overclaim mathematical novelty; it frames the theorem as a mechanized guard against importing total-map intuitions. This framing is appropriate for TACAS/FASE audiences.

**Axiom audit (§4.3)** is unusually transparent. Reporting per-theorem axiom footprints (`#print axioms`) distinguishes this from papers that disclose axioms only at the library level.

**RQ-to-theorem traceability matrix (§1.5)** correctly separates primary from supporting RQs and maps each to specific Lean files. This is sufficient for artifact evaluation.

---

## 3. Blocking Issues

### B1. `UStar_subset_UAndOn` assumption inconsistency between manuscript and assumption matrix

**§3.8** states the theorem requires `hNecessaryOnDom` (domain-restricted premise: `∀ i, active i → (UStar ∩ projDom(i)) ⊆ lifted(i)`). But the assumption matrix lists `UStar_subset_UAndOn` as requiring the *global* premise `∀ i, active i → UStar ⊆ lifted i`. These are logically distinct—the global form does not follow from domain restriction alone under partial projections.

The Lean signature shown in §3.8 uses `hNecessaryOnDom` (domain-restricted). If that is the actual mechanization, then the assumption matrix entry for `UStar_subset_UAndOn` (which states global necessity) is incorrect and misleads the reader about what is actually proven. If the global form is also mechanized separately, both variants need distinct theorem names and entries.

**Required fix**: Reconcile §3.8 Lean signature with the assumption matrix. If the mechanized theorem uses domain restriction, the matrix must say so; if a separate global theorem exists, name it explicitly.

### B2. `preimage_compose` axiom footprint inconsistency

**§4.3** reports `Classical.choice` in the axiom footprint of `preimage_compose` and explains this arises from "witness reconstruction expressed through extensional equality over existential branches." However, §3.5 describes the proof as constructive branch analysis on `Option` with explicit witness reconstruction in both directions. A proof that explicitly names witnesses in both the `some` and `none` branches should not require `Classical.choice` unless the extensional equality step (`set_ext` / `funext`) triggers classical reasoning.

The paper acknowledges this (§4.3 item 7) but does not explain *why* `Classical.choice` is required specifically for `preimage_compose` but *not* for `lifted_transfer` (which also involves existential witnesses). This asymmetry is unexplained and will attract reviewer scrutiny at ITP/CPP.

**Required fix**: Add one sentence explaining the specific proof step where `Classical.choice` enters `preimage_compose` but not `lifted_transfer`. If the cause is `funext`/`propext` interaction with existentials in `set_ext`, say so explicitly.

### B3. Theorem role-group counts (§4.6) are unverifiable from the theorem catalog

§4.6 claims 22 core, 27 supporting, 21 example-level declarations summing to 70. The theorem catalog (appendix) lists theorems by file but does not tag each theorem with its role group. A reviewer cannot verify the 22/27/21 breakdown without manual classification.

For example: `subset_refl`, `subset_trans`, `set_ext` in `Definitions/Model.lean` are counted somewhere—but as core, supporting, or example-level? `consistent_transport_left` in `Transfer.lean` is not mentioned in any manuscript section; its role is unassigned.

**Required fix**: Add a "Role" column (Core / Supporting / Example) to the theorem catalog appendix, or provide a separate mapping table. The 70 total is verifiable from the catalog; the breakdown is not.

### B4. `semanticPullbackMay` contains `proj`-none branch (§3.6.2) — justification is circular

§3.6.2 justifies including `proj_i(x) = none` in `semanticPullbackMay` by saying "may-comparison requires matching the same inconclusive policy on both sides." But this is the *conclusion* the reader needs justified, not a premise. The semantic question is: why should the extraction relation `E` be given a free pass on undefined-observation points when `proj` is undefined? A reviewer at Formal Aspects or FM will ask whether this design choice is uniquely forced or one of several valid options.

**Required fix**: In §3.6.2, add one sentence stating what alternative design was considered and why it was rejected (e.g., "An alternative would be to treat `proj_i(x) = none` as definite non-membership on both sides, but this would make `preimageMay` = `preimage`, collapsing the must/may distinction entirely"). The mechanized `preimage_subset_preimageMay` already implies this; just make the reasoning explicit in prose.

---

## 4. Minor Editorial Issues

**M1. §2.3 label "compilable context"**: The excerpt is described as "pedagogical composite across" two files. At ITP/CPP this phrasing may trigger concerns about whether the excerpt is directly compilable or requires adaptation. Suggest replacing "compilable context" with "illustrative composite" or adding a note that the canonical compilable sources are the individual files listed in §2.5.

**M2. §3.3 "vacuous-truth implication" block**: The three-item list correctly identifies the issue but does not explicitly state that `UAndOn_empty_eq_univ` is *proven in Lean* rather than just asserted. The theorem catalog confirms this (`Construction.lean`), but the manuscript prose should say "mechanized as `UAndOn_empty_eq_univ`" rather than just naming it inline.

**M3. §4.4 "lake job count (42)"**: The note "(42) is a build-graph execution count and is not expected to equal source-file count" is correct but slightly defensive. Consider replacing with a cleaner statement: "42 build jobs reflects parallel compilation of Lean modules; theorem count of 70 is measured independently via `rg`." This prevents a reader from wondering whether the numbers are in tension.

**M4. §6.1 baseline capabilities list**: The three baseline items cite API-style names (`Set.preimage_comp`, `GaloisConnection`) without citations. At CPP/ITP these should have references (Mathlib commit or paper). Since the artifact intentionally excludes Mathlib, an inline note like "available in Mathlib4 as `Set.preimage_comp`; not imported here" would complete the delta argument cleanly.

**M5. References**: Reference 12 (mathlib Community, CPP 2020) is cited in §6.1 context but Mathlib is explicitly not used in the artifact. This is not a contradiction, but the citation placement may confuse readers who assume cited libraries are dependencies. A brief parenthetical "(cited for baseline comparison; not a dependency of this artifact)" would prevent misreading.

**M6. §5.2 `req_projection_adequacy` scope note**: The manuscript correctly notes this is "a concrete instantiation of abstract adequacy interface, not a general proof of extractor correctness." However, the theorem catalog lists it under `CaseStudy/PasswordPolicy.lean` without any role annotation. Given that this theorem instantiates an adequacy template, it sits at the boundary of "example-level" and "supporting." The role-group fix (B3) will resolve this, but flag it explicitly.

---

## 5. Final Checklist to Reach Acceptance

- [ ] **B1**: Reconcile `UStar_subset_UAndOn` assumption description in §3.8 with assumption matrix entry (domain-restricted vs. global premise).
- [ ] **B2**: Explain why `Classical.choice` appears in `preimage_compose` but not `lifted_transfer`, with reference to the specific proof step (likely `funext`/`set_ext` on existential branches).
- [ ] **B3**: Add role annotation (Core / Supporting / Example) to theorem catalog appendix so the 22/27/21 breakdown in §4.6 is independently verifiable.
- [ ] **B4**: Add one sentence in §3.6.2 explaining what alternative design for `semanticPullbackMay`'s none-branch policy was considered and why this design was chosen.
- [ ] **M1**: Clarify "compilable context" label in §2.3 to avoid implying the composite excerpt is standalone-compilable.
- [ ] **M2**: Make explicit that `UAndOn_empty_eq_univ` is mechanized (not just named), in the §3.3 prose.
- [ ] **M3**: Rephrase the §4.4 lake-job-count parenthetical for clarity.
- [ ] **M4–M5**: Add "not a dependency" parenthetical near Reference 12; add source context for baseline API names in §6.1.
- [ ] **M6**: Confirm `req_projection_adequacy` role assignment in the theorem catalog once B3 is resolved.

---

*No issues were found with the overall logical structure of the kernel, the correctness of the theorem statements as written, or the reproducibility infrastructure. The paper is close to acceptance; the blocking issues are precision gaps, not conceptual flaws.*
