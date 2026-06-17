## Review: Reviewer #2

---

### 1) Overall Recommendation

**Minor Revision**

The paper presents a well-scoped mechanized kernel for multi-layer specification comparison under partial projections. The theorem-to-file traceability, assumption auditing, and explicit non-claims are commendable. However, several issues require author attention before acceptance: the novelty framing needs sharper positioning, certain reproducibility claims cannot be externally verified from the submission, and some proof-integrity disclosures have gaps or inconsistencies.

---

### 2) Strengths

**S1. Disciplined assumption auditing.** The explicit hypothesis interfaces (`hproj`, `hA`, `hcomm`) in §3.4–3.5, paired with mechanized counterexamples (`TransferCounterexample.lean`, `AdequacyCounterexample.lean`), constitute genuine added value over prose-only presentations. This is the paper's strongest contribution.

**S2. Honest non-claims (§0.2).** The explicit separation of what is not claimed (extractor correctness, statistical validity, engineering-pipeline equivalence) is rare and valuable. It substantially reduces reviewer burden.

**S3. Axiom-level transparency (§4.3).** Per-theorem `#print axioms` reporting is exemplary. The explanation of why `Classical.choice` appears in `preimage_compose` but not in `lifted_transfer` (§4.3, items 10–11) is technically correct and clearly argued.

**S4. Must/may policy split (§2.6, §3.6).** Treating undefined projection points as a first-class policy concern rather than an implementation detail is methodologically sound and distinguishes this work from total-map-only treatments.

**S5. Claim integrity at RQ level (§1.3–1.5).** The RQ-to-theorem traceability matrix is complete and cross-referenced to file paths. This is above the typical bar for mechanized contributions.

---

### 3) Major Issues

**M1. Theorem count consistency: catalog vs. shell script.**

The `reproduce_formal.sh` script checks `theorem_count == "72"` using `rg -n '^theorem '`. The theorem catalog (appendix) lists per-file counts that sum to exactly 72. However, `paper/lean/UadfU0/Examples/TwoLayer.lean` is explicitly noted as "theorem count: 0 (example declarations only)." If additional files exist in `UadfU0` not listed in the catalog (e.g., `AdequacyCounterexample.lean` lists 4 theorems but `TransferCounterexample.lean` also lists 4—both are accounted for), the catalog should explicitly state it is exhaustive. Currently the catalog does not declare itself complete with respect to the file listing. The shell script would silently pass if undisclosed files added theorems that compensated for any catalog error.

*Required action:* Add an explicit statement in the catalog appendix that the listed files constitute the complete set of `.lean` files under `paper/lean/UadfU0`, or provide the file listing from `rg --files UadfU0` as a catalog section.

**M2. LOC check is brittle and potentially misleading.**

The `reproduce_formal.sh` script asserts `loc_total == "1703"` (exact match). This check will fail on any reviewer machine if line-ending conventions differ (CRLF vs. LF) or if build-generated files are included by `rg --files`. The manuscript (§4.4) states "LOC (`paper/lean/UadfU0`): `1703`" but does not disclose whether build artifacts (`.lake/`) are included or excluded. The `rg --files UadfU0` invocation from inside `paper/lean` could match different file sets depending on `.gitignore` and `rg` version.

*Required action:* Either (a) replace the exact LOC check with a bounded range (e.g., `[ "$loc_total" -ge 1690 ] && [ "$loc_total" -le 1720 ]`), or (b) document the exact `rg` invocation scope (source files only, specific extensions) and explain why exact match is reproducible. The manuscript should reflect whichever choice is made.

**M3. `PasswordPolicy.lean` is listed in §5.2 but absent from the file listing in §9.**

Section 9 ("Reproducibility Pointers") lists `paper/lean/UadfU0/CaseStudy` as a directory included in the submission. However, `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` is referenced in the theorem catalog (4 theorems) and §5.2 but is not cross-referenced with a file path in the §4.5 traceability table. The theorem `req_projection_adequacy` is noted in §5.2 as a "concrete instantiation" but does not appear in the §4.5 table at all.

*Required action:* Add `CaseStudy/PasswordPolicy.lean` to the §4.5 traceability table with its four theorems listed. If the case study is intended as a sanity check rather than a core claim, state this explicitly in §4.6.

**M4. `preimage_compose` axiom footprint is inadequately justified for a formal venue.**

§4.3 item 7 states: "`Classical.choice` appears in some equality proofs (for example `preimage_compose`) because witness reconstruction is expressed through extensional equality over existential branches; this paper does not claim constructivity-preserving normalization for those proofs."

This is acceptable as a disclosure, but the paper does not explain whether `Classical.choice` is *necessary* for `preimage_compose` or merely an artifact of the proof strategy chosen. At ITP/CPP, reviewers will ask whether a constructive proof exists. The proof skeleton in §3.5 appears fully constructive (witness extraction in both directions is explicit), which raises the question of whether the `Classical.choice` dependency could be eliminated with a different proof term.

*Required action:* Either (a) confirm that a constructive proof exists and note it was not pursued for concision, or (b) give a brief argument for why `Classical.choice` is genuinely required (e.g., the specific `set_ext` + `funext` interaction in Lean4 that forces it). This is a proof-integrity question, not a stylistic one.

---

### 4) Minor Issues

**m1. §6.1 "concrete delta" subsection: baseline attribution is imprecise.**

§6.1 lists `Set.preimage_comp`-style APIs as the baseline. For CPP/ITP audiences, this should cite specific Mathlib lemma names or module paths (e.g., `Mathlib.Order.GaloisConnection`) rather than informal style-names. Without precise attribution, the delta claim cannot be verified.

**m2. §3.3: `consistent_iff_exists_UAndOn_pair` is listed as a core theorem (RQ3) in §1.5 and §4.6, but its role is never explained in §3.3 prose.**

The theorem name suggests it characterizes pairwise consistency via `UAndOn`, but §3.3 only mentions `Consistent(i,j)` in the role-separation bundle discussion without citing this theorem by name. The reader cannot verify whether this theorem is trivially derivable from §2.7 definitions or requires non-trivial argument.

*Required action:* Add one sentence in §3.3 explaining what `consistent_iff_exists_UAndOn_pair` states and why it is non-trivial given the separation of `U0On`/`UAndOn`.

**m3. §3.7: `no_left_adjoint_of_partial` proof sketch uses "singleton root set `S = {x0}` and universal codomain set `T = ⊤`" but the paper uses predicate encoding (`SpecSet α := α -> Prop`), not Lean's `Set`.**

The proof sketch should clarify what `⊤` means in the `SpecSet` encoding (presumably `fun _ => True`) to avoid notational confusion for readers unfamiliar with the predicate-as-set convention established in §2.1.

**m4. Abstract is slightly over-broad.**

The abstract states the paper proves theorems that are "technically central in this setting." This phrasing invites the question: central to what? The paper's own §6 explicitly clarifies these are not standalone novelty results. The abstract should align with this scoping (e.g., "technically necessary" or "formally required").

**m5. §5.2: `PasswordPolicy.lean` theorem count inconsistency with §4.6.**

§4.6 states example-level declarations are 23, comprising "all theorem declarations under `paper/lean/UadfU0/Examples/*.lean` (19 total)" plus "`CaseStudy/PasswordPolicy.lean` (4 total)." The catalog lists `Examples/TwoLayer.lean` with 0 theorems. If there are 8 example files under `Examples/` and they total 19, the per-file average is ~2.4. This is consistent with the catalog, but the manuscript should confirm no additional `Examples/` files exist beyond those listed.

**m6. §7 (related work) lacks citation for assumption-explicit mechanization lines.**

The paper positions itself against institution frameworks, BX, and Galois connections, but does not cite work on explicit-assumption proof engineering (e.g., work on assumption auditing in Isabelle/HOL or type-class-based hypothesis management). This is a minor positioning gap, not a correctness issue.

---

### 5) Required Revision List

| # | Priority | Section | Action |
|---|---|---|---|
| R1 | Major | Appendix/theorem_catalog.md | Declare catalog completeness (full file listing or explicit exhaustiveness statement) |
| R2 | Major | `reproduce_formal.sh` + §4.4 | Fix brittle exact-LOC check; document exact `rg --files` scope |
| R3 | Major | §4.5 + §5.2 | Add `PasswordPolicy.lean` to traceability table; clarify `req_projection_adequacy` role in §4.6 |
| R4 | Major | §4.3 | Clarify whether `Classical.choice` in `preimage_compose` is necessary or proof-strategy artifact |
| R5 | Minor | §6.1 | Replace style-names with precise Mathlib lemma references |
| R6 | Minor | §3.3 | Add prose explanation of `consistent_iff_exists_UAndOn_pair` content and non-triviality |
| R7 | Minor | §3.7 | Clarify `⊤` notation in `SpecSet` predicate encoding within proof sketch |
| R8 | Minor | Abstract | Replace "technically central" with scoped phrasing consistent with §6 non-claims |
