# Venue-Specific Formal Review: FM/ITP/CPP/TACAS/FASE/Formal Aspects

## 1. Overall Recommendation

**Major Revision**

The mechanization appears technically solid and the paper is unusually careful about assumption disclosure. However, the submission has structural problems that prevent acceptance: the novelty framing is insufficiently sharp for any of the target venues, the positioning against prior work is defensive rather than analytical, and several claims require verification that cannot be performed from the submitted files alone.

---

## 2. Strong Points

1. **Assumption discipline**: The paper's explicit treatment of `hproj`, `hA`, `hcomm` as theorem arguments (not prose conditions) is a genuine methodological contribution. The assumption matrix (appendix) is exemplary.

2. **Counterexample backing**: Mechanized counterexamples (`TransferCounterexample.lean`, `AdequacyCounterexample.lean`) that prove the necessity of assumptions, not just their sufficiency, is the right way to validate a theorem interface. This is stronger than most mechanization papers.

3. **Must/may split with explicit policy disclosure**: §2.6 and §3.6.2 correctly identify that collapsing must/may is a policy decision, and the mechanization keeps them separate. This is semantically careful.

4. **Axiom disclosure** (§4.3): Per-theorem `#print axioms` reporting is exactly what ITP/CPP expect. The asymmetry explanation between `lifted_transfer` (no axioms) and `preimage_compose` (with `Classical.choice`) is honest and well-reasoned.

5. **Non-claims section** (§0.2): Explicit non-claims are rare and valuable at these venues.

---

## 3. Major Concerns (Must-Fix)

### M1. Novelty claim is insufficiently sharpened for any target venue

§6 and §6.1 state the contribution is "combination-level" and "interface-level." This is the weakest possible novelty framing. FM, ITP, CPP, and TACAS all expect at least one of: a new mathematical result, a new proof technique, or a new formal methodology with evidence of applicability beyond the immediate artifact.

The paper explicitly disclaims standalone mathematical novelty for every major theorem (§3.7, §3.3, §3.4). What remains is: a typed kernel that assembles known pieces under explicit assumptions with machine-checked counterexamples. This is publishable at a mechanization track (CPP, ITP) but requires the paper to *argue* why this assembly is non-trivial and what a practitioner or theorist gains from this specific kernel that they could not achieve by combining existing Mathlib APIs.

**Required**: Either (a) identify one theorem that has non-trivial formal content beyond assembly, and argue it, or (b) reframe the paper explicitly as a *methodology contribution* (assumption-audited kernel design) and provide evidence that the methodology generalizes — i.e., show another domain or kernel that benefits from the same pattern.

### M2. Theorem count claim (72) cannot be independently verified from submitted files

§4.4 and the reproducibility script (`reproduce_formal.sh`) count `^theorem` lines via `rg`. However, the manuscript does not include the full Lean source files — only excerpts. The appendix (`theorem_catalog.md`) lists theorem names but not their full statements. A reviewer cannot verify:
- that the 72 declarations match the catalog,
- that the catalog entries in `theorem_catalog.md` are not duplicates of `example` declarations,
- that `sorry`-free status applies to definitions as well as theorem bodies (opaque definitions can hide obligations).

The `reproduce_formal.sh` script checks for `\bsorry\b` as a regexp match but this does not catch `native_decide`, `decide`, or axiom-introducing tactics that may discharge obligations unsoundly.

**Required**: Include full Lean source in the appendix (or a supplementary artifact URL with a frozen hash). Add explicit checks for `native_decide` and `decide` usage in the reproduce script if they appear in the codebase.

### M3. RQ1 and RQ2 are stated as "supporting" but their answers are never formally evaluated

The RQ-to-theorem traceability matrix (§1.5) marks RQ1 and RQ2 as answered by `preimage` definition and `lifted_subset_preimage_domain`. But the paper then says (§3.2): "Primary RQs for this formal paper are RQ3, RQ4, and RQ5. RQ1 and RQ2 are supporting questions."

If RQ1 and RQ2 are not evaluated as primary claims, they should not appear in the RQ list — or the evaluation criteria (§1.4) should explain how supporting RQs are assessed differently. As written, the RQ framework is inconsistent: it sets up five questions but only evaluates three, with the other two reduced to definitional observations.

**Required**: Either elevate RQ1/RQ2 with their own evaluation narrative, or remove them from the RQ list and fold their content into §2 as definitional prerequisites.

### M4. `semanticPullback` / abstract `E` separation lacks formal justification for why `E ≠ graph(proj)` is operationally meaningful

§3.6 motivates abstract `E` by saying it allows "theorem-level reasoning before committing to a concrete extractor." But the paper does not prove any theorem that uses `E ≠ graph(proj)` in an essential way that could not be recovered by specializing `E = graph(proj)`. The `AdequacyCounterexample.lean` shows that when `E = EPlus1` (a specific mismatched relation), one-sided adequacy holds but equality fails — but this is a sanity check, not a proof that the abstraction is necessary.

**Required**: State explicitly what the user of this kernel gets from abstract `E` that they could not get by instantiating immediately. If the answer is "the theorem interface is usable before extractor correctness is proven," state this formally as a theorem about the partial-instantiation pattern.

### M5. Relation to prior work (§7) lacks formal precision on definition-level differences

§7 describes differences from institutions, BX, and Galois connections in prose. For venues like FM or TACAS, reviewers expect the differences to be stated at the definition level: "institution morphisms require X; our kernel does not require X but requires Y instead." The current text says things like "narrower but executable kernel" without specifying what structural property makes it narrower and what is gained.

In particular, §7.5 claims the paper contributes a "partiality-specific guardrail theorem" as a difference from constructive Galois-connection lines. But Darais and Van Horn (ICFP 2016, cited as [11]) work in a setting where partiality is handled via monotone functions on partial orders — the claim that `no_left_adjoint_of_partial` adds something not already implicit in their framework needs more than a prose statement.

**Required**: For at least the two closest lines (institutions and constructive Galois connections), provide a 3–5 row comparison table at the definition level (structures/morphisms/theorems required, structures/morphisms/theorems provided).

---

## 4. Minor Concerns

### m1. §2.3 "pedagogical composite excerpt" notation is misleading

The Lean excerpt in §2.3 is labeled "pedagogical composite across [two files]." For a formal paper, any code excerpt should come from exactly one source location. If the definitions are spread, list both locations separately and do not merge them into a single block. As written, a reader cannot map the excerpt to the actual file structure.

### m2. §3.3 role-separation result framing

`UAndOn_subset_U0On` requires `∃ i, active i` as a hypothesis. This is a standard lattice fact (join dominates meet when the index set is non-empty). Calling this part of a "central role-separation result" overstates its novelty. The genuinely interesting part is the partiality-sensitive behavior. The section should be reordered to foreground that.

### m3. §4.6 theorem-role breakdown arithmetic is approximate

`72 - 22 - 23 = 27` (supporting lemmas). But `theorem_catalog.md` lists `Definitions/Model.lean` with 3 theorems (`subset_refl`, `subset_trans`, `set_ext`). These are standard library-level facts. Their presence as `theorem` declarations in the artifact is fine for mechanization purposes, but counting them among the 27 "supporting lemmas" conflates trivial infrastructure with proof-supporting content. Be explicit about this.

### m4. `UAndOn_empty_eq_univ` vacuous-truth warning (§3.3, §8) should be in §2

The vacuous-truth behavior of `UAndOn` over empty active sets is a semantic gotcha that affects how the kernel should be used. It is introduced in §3.3 and repeated in §8. But it should be disclosed at the level of §2 (model definition), since it is a definitional consequence visible immediately.

### m5. Hash format error in `build_evidence.md`

The expected SHA256 for `paper/lean/lake-manifest.json` is listed as `8c098d788704fb7c279c7004a1f492723bd892acf2500483665ae39e7a00a6e7` (63 hex characters). A SHA256 hash must be 64 hex characters. Either the hash is truncated or there is a transcription error. This must be corrected before submission.

### m6. `CaseStudy/PasswordPolicy.lean` is listed in theorem catalog but not mentioned in §1.5

The RQ-to-theorem traceability matrix (§1.5) does not reference any theorem from `PasswordPolicy.lean`. But §5.2 claims it provides a "mechanized sanity theorem." If it supports any RQ, add it to the matrix. If it does not, explain its role more clearly in §5.2.

---

## 5. Required Revisions Checklist

- [ ] **M1**: Sharpen novelty claim beyond "combination-level assembly." Either identify a theorem with non-trivial formal content, or reframe as a methodology contribution with generalization evidence.
- [ ] **M2**: Provide full Lean source as a frozen artifact, or include in supplementary material with verifiable hash. Extend `reproduce_formal.sh` to also scan for `native_decide` and `decide`.
- [ ] **M3**: Resolve inconsistency in RQ framework. Either evaluate RQ1/RQ2 as primary claims with their own criteria, or remove them from the RQ list.
- [ ] **M4**: Formally state what abstract `E` provides that `E = graph(proj)` does not. Add a theorem or remark that makes this precise.
- [ ] **M5**: Add definition-level comparison tables for institutions and constructive Galois connections (§7.2, §7.5).
- [ ] **m1**: Replace §2.3 composite excerpt with separate per-file excerpts. Label each with its canonical file path.
- [ ] **m5**: Fix SHA256 hash in `build_evidence.md` (63 → 64 hex characters).
- [ ] **m6**: Either add `PasswordPolicy.lean` theorems to the RQ traceability matrix (§1.5) or clarify their role as outside the RQ structure.
- [ ] Reorder §3.3 to foreground partiality-sensitive behavior rather than the standard lattice subset fact.
- [ ] Move the `UAndOn_empty_eq_univ` vacuous-truth disclosure into §2 (model definition section).
