# Review: UAD/f Two-Operator Kernel under Partial Projections

**Reviewer #2 — Balanced but Rigorous**
**Target Venues: FM / ITP / CPP / TACAS / FASE / Formal Aspects**

---

## 1. Overall Recommendation

**Major Revision**

The paper presents a well-scoped Lean4 mechanization of a typed partial-projection kernel with explicit assumption auditing. The formal structure is generally sound, reproducibility metadata is above average for the venue, and the non-claim boundaries are unusually explicit. However, several issues must be resolved before acceptance: the novelty justification is weak and partially circular, the prior-work discussion lacks technical depth for FM/ITP audiences, the claim about `Classical.choice` usage is stated but not sufficiently explained, and the relationship between the formal kernel and the motivating application is too loosely connected. None of these are fatal, but together they prevent acceptance at current revision.

---

## 2. Strengths

**S1. Explicit assumption auditing.**
The assumption matrix (Appendix) and per-theorem hypothesis lists (`hproj`, `hA`, `hcomm`) are a genuine methodological contribution. The practice of naming and cataloging what breaks when each assumption is removed is uncommon in mechanization papers and directly serves reproducibility.

**S2. Counterexample mechanization.**
`TransferCounterexample.lean` and `AdequacyCounterexample.lean` provide mechanized negative witnesses. This is the correct way to justify that hypotheses are not redundant, and the paper does this systematically across theorem families.

**S3. Claim/non-claim separation in §0.2.**
The explicit non-claims section is well-written and preempts several predictable reviewer objections. This is good practice at FM/ITP.

**S4. Must/may split with named bridge theorems.**
The must-side / may-side duality in §3.6, with named one-sided theorems and explicit conditions for equality, is a clean interface design. The `semanticPullbackMay` `none`-branch policy is correctly motivated in §3.6.2.

**S5. Reproducibility infrastructure.**
Theorem catalog, build evidence snapshot, manifest hash, and toolchain pin (`leanprover/lean4:v4.27.0`) collectively constitute a reproducible artifact package significantly above the median for mechanization submissions.

**S6. Zero `sorry` count and theorem-to-file traceability.**
Table in §4.5 maps every formal claim to a Lean file. The `sorry`-free confirmation is appropriately operationalized with a reproducible shell command.

---

## 3. Major Issues

**M1. Novelty argument is circular and under-substantiated (§6, §6.1).**

The paper claims its main delta is "a typed theorem interface layer under partiality, not a replacement of general-purpose library lemmas" (§6.1). The concrete delta listed is: heterogeneous carriers + partial projections + explicit transfer/composition hypotheses + must/may split + non-adjointness guardrail + assumption matrix.

The problem is that each item in this list is framed as novel by asserting standard libraries do not carry it, without citing those libraries specifically or demonstrating absence. For FM/ITP this is insufficient. The paper must either:
(a) cite specific Mathlib 4 / Isabelle AFP / Coq stdlib definitions and show they do not cover the claimed interface, or
(b) reframe the contribution as a *synthesis and packaging* contribution and argue why such packaging is venue-appropriate.

Currently §6.1 says "standard total-function APIs do not carry this full assumption interface" — this assertion needs substantiation or the novelty framing needs adjustment.

**M2. Prior-work section (§7) lacks technical comparison depth.**

§7.1–§7.5 pattern is: state what the cited field does, then assert this paper contributes something narrower. The comparisons are at an abstract level that would be appropriate for a workshop extended abstract, not a full FM/ITP paper.

Specifically:
- §7.5 cites Darais & Van Horn (Constructive Galois Connections, ICFP 2016) but §3.7 only states the paper proves non-adjointness under partiality. It is not discussed whether constructive Galois connections are fully total, what the exact definition difference is, or why the partiality result is not a corollary of their framework.
- §7.2 mentions institutions (Goguen/Burstall 1984) but does not discuss whether the satisfaction condition in institutions already handles the heterogeneous carrier problem, or what specifically breaks if one tries to encode the UAD/f kernel as an institutional morphism.

The paper should add 1–2 paragraphs per subsection with technical comparison at definition level, not just thematic positioning.

**M3. `Classical.choice` usage requires better justification (§4.3, item 7).**

The paper discloses that `preimage_compose` depends on `Classical.choice` because "witness reconstruction is expressed through extensional equality over existential branches." This disclosure is good, but the explanation is insufficient for venues (ITP/CPP) that care about constructivity.

Specifically:
- Is `Classical.choice` used to pick a witness from an existential, or does it arise through `funext`+`propext` in a place where classical reasoning is unavoidable?
- The paper states "constructive rewriting with explicit branch witnesses is possible in principle" — if possible in principle, why not provided? The paper should either (a) provide the constructive proof or (b) explain precisely why the added complexity is not worth it relative to this paper's goals, with reference to the specific proof step where classicality enters.

For FM/ITP and CPP this is a relevant design question, not a cosmetic one.

**M4. Connection between formal kernel and motivating application is thin (§1.1, §5).**

The introduction motivates the kernel by multi-layer artifact comparison in engineering settings. The formal artifact (`ArtifactBundleExample.lean`) uses `ReqIR`, `ApiIR`, `CodeIR` as concrete carriers. However:
- The example carriers appear to be trivially typed wrapper types with no domain content.
- The adequacy instantiation (`Eextract_sound`, `Eextract_complete`) is mechanized but the paper does not explain what `extract` actually does in this example — is it identity? A projection? The connection to a real extractor semantics is not made.

The paper's non-claim §0.2 item 1 states "no proof that a concrete regex or LLM extractor satisfies adequacy assumptions." That is fine, but the example in §5.1 should at minimum be described in enough detail that a reader can evaluate what instantiation is being demonstrated. As written, it is unclear whether the example is non-trivial or whether `Eextract_sound/complete` are trivially proved because `E = proj` by construction.

**M5. `UAndOn_empty_eq_univ` edge case has operational implications not fully addressed (§3.3, §8).**

§3.3 and §8 mention that `UAndOn_empty_eq_univ` requires enforcement of non-empty active sets. But the paper does not explain how a user of this kernel is supposed to enforce this. Specifically:
- Is there a typed interface that prevents calling `UAndOn`-based reasoning without a non-empty active set witness?
- Or is enforcement left entirely to the caller?

If enforcement is left to the caller, the assumption matrix should reflect this as an interface-level obligation. If the kernel provides a typed guard, that should be described and pointed to in the Lean sources. As written, the vacuous-truth risk is disclosed but its mitigation is not.

---

## 4. Minor Issues

**m1. Notation inconsistency between §2 and §3.**

§2.4 defines `preimage_i(S)` using set-builder notation with `∃ y ∈ β_i`. In §3.4 the transfer theorem hypotheses are written in prose before the Lean signature. The prose uses `A(j)` and `A(i)` while the Lean uses `M.Ui j` and `M.Ui i`. §2.2 says `Ui(i) := A(i)` is a compatibility alias, but a reader encountering §3.4 before §2.2 will find the alias confusing. Either standardize notation throughout or add a forward reference to §2.2 at first use in §3.

**m2. §4.6 theorem-role breakdown is stated but not provided.**

§4.6 says "Role categories used in this paper: (1) core theorem interfaces, (2) supporting lemmas, (3) example-level theorem declarations." But the breakdown is deferred to `theorem_catalog.md`. The catalog (attached) does not include role categories — it only lists theorem names per file. Either the catalog should be extended to include per-theorem role tags, or §4.6 should include the breakdown inline.

**m3. The `RQ1`/`RQ2` framing feels forced (§1.3, §1.5).**

`RQ1` asks whether `preimage` can be defined consistently with heterogeneous carriers — this is a definition question, not a research question. `RQ2` asks whether `A(i) ⊆ D(i)` can be lifted — this is a straightforward lemma (§3.1 treats it as "foundational, not novelty"). Presenting these as research questions inflates the framing. Consider restructuring `RQ1`/`RQ2` as prerequisites or design questions and reserving the RQ label for `RQ3`–`RQ5` which have genuine theorem content.

**m4. Reference list is missing key mechanization references.**

For ITP/CPP: the paper cites de Moura & Ullrich (Lean 4, CADE 2021) but does not cite the Lean4 Mathlib paper or relevant Lean4 community reports. For TACAS/FASE: the paper would benefit from citing at least one survey of mechanized set-based semantics (e.g., Nipkow & Paulson AFP entries, or Affeldt et al. on partial functions in Coq). The reference list is thin for a full paper submission.

**m5. `build_evidence.md` records "42 jobs" but the number of source files implied by the theorem catalog suggests fewer compilation units.**

This is a minor reproducibility concern: `42 jobs` is the lake job count, which includes compilation units beyond `.lean` files. This is fine, but the paper should clarify that job count ≠ source file count to avoid confusion for artifact evaluators who may expect a 1:1 correspondence.

**m6. Abstract does not mention Lean4 or the toolchain version.**

For formal-methods venues where reproducibility of mechanization is a review criterion, the toolchain version should appear in the abstract or the opening of §4. Currently it only appears in §4.3.

---

## 5. Required Revision List

**R1 [Addresses M1]:** Add a concrete technical comparison to specific Lean4/Mathlib 4 definitions (e.g., `Set.preimage`, `Order.GaloisConnection`) and explain at definition level what the UAD/f kernel provides that those interfaces do not, or reframe the novelty claim as a synthesis/packaging contribution with explicit argument for why such packaging meets venue standards.

**R2 [Addresses M2]:** Extend §7.5 and §7.2 with at least 1 paragraph each of technical, definition-level comparison. For §7.5, explain precisely how the Darais/Van Horn constructive Galois connection framework handles partiality (or does not), and what the exact theorem-level gap is relative to `no_left_adjoint_of_partial`. For §7.2, explain whether institutional satisfaction conditions can already handle heterogeneous carriers and what specifically the UAD/f kernel adds.

**R3 [Addresses M3]:** Either (a) provide a constructive proof of `preimage_compose` without `Classical.choice` and update axiom audit, or (b) add a precise explanation of which proof step introduces `Classical.choice` (with reference to the specific Lean term), and justify why the concise extensional proof style was preferred with explicit acknowledgment of the constructivity tradeoff. This should be added as a footnote or paragraph in §4.3.

**R4 [Addresses M4]:** Expand §5.1 to describe the concrete semantics of `obs`, `extract`, and `E` in `ArtifactBundleExample.lean`. Confirm whether `Eextract_sound/complete` are trivially proved (e.g., if `E = graph(proj)` by construction) or genuinely non-trivial, and explain what this demonstrates about the instantiation pattern.

**R5 [Addresses M5]:** In §3.3 or §4.1, clarify the interface-level mitigation for `UAndOn_empty_eq_univ`. If no typed guard is provided, update the assumption matrix to include "non-empty active set" as a caller obligation for any theorem using `UAndOn` as a consistency signal.

**R6 [Addresses m2]:** Either extend `theorem_catalog.md` to include role tags (core / supporting / example) per theorem, or add the breakdown table inline in §4.6.

**R7 [Addresses m3]:** Restructure §1.3/§1.5 to distinguish design prerequisites (`RQ1`, `RQ2`) from research questions (`RQ3`–`RQ5`), or provide additional justification for why `RQ1`/`RQ2` qualify as research questions at the target venues.

**R8 [Addresses m4]:** Expand the reference list with at least 2–3 citations relevant to Lean4 mechanization practice and partial-function semantics in proof assistants.

---

*Summary: The mechanization discipline, assumption auditing, and reproducibility infrastructure are genuine strengths that distinguish this paper from typical informal specification papers. The major issues (novelty framing, thin prior-work depth, classicality disclosure, and thin example description) are all addressable without restructuring the core results. A focused revision addressing R1–R5 would bring this to minor-revision territory.*
