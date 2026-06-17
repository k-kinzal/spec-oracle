## Reviewer #3 Report

**Paper:** UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization

---

## 1. Overall Recommendation

**Minor Revision**

The paper presents a coherent mechanized formal contribution with clear scope, honest non-claims, and verifiable artifact metadata. The core theorem families are well-organized, and the assumption-matrix/counterexample discipline is genuinely valuable. The blocking issues below are solvable without restructuring the paper.

---

## 2. What Is Already Acceptance-Level

**A. Claims/non-claims discipline (§0.1–0.3)**
The explicit separation of claims from non-claims is exemplary. Non-claim #4 (engineering replay ≠ theorem evidence) and non-claim #5 (non-adjointness is a guardrail, not standalone novelty) are exactly the kind of boundary statements FM venues require. This alone puts the paper significantly above average.

**B. Assumption matrix (appendix/assumption_matrix.md)**
Providing a structured fallback-claim column for each theorem is rare and directly useful for reviewers and users of the artifact. The pattern "if assumption fails, use weaker one-sided variant" is machine-auditable through the counterexample examples.

**C. Axiom audit per theorem (§4.3)**
Reporting `#print axioms` results per theorem, with explanation of why `Classical.choice` appears in `preimage_compose` but not `lifted_transfer` (proof-shape asymmetry §4.3 item 10), is honest and technically precise.

**D. Counterexample mechanization (§5.3, §5.4)**
`TransferCounterexample.lean` and `AdequacyCounterexample.lean` are genuine formal value: they show that `hproj` and the sound/complete split are real obligations, not cosmetic hypotheses. This pattern should be highlighted more in the abstract.

**E. Partiality-specificity of RQ3 (§3.3 last paragraph)**
The observation that U0/UAnd separation is not purely order-theoretic but policy-sensitive under partiality is the paper's strongest conceptual contribution. It is stated clearly.

---

## 3. Blocking Issues

### B1. Abstract does not mention counterexamples — mismatch with §5 content

The abstract lists five proof families but never mentions that mechanized counterexamples (TransferCounterexample, AdequacyCounterexample) are part of the contribution. Since §5.3–5.4 and §6 treat these as first-class formal results demonstrating assumption necessity, the abstract undersells the contribution and creates a mismatch a program committee will notice.

**Required fix:** Add one sentence to the abstract stating that assumption-failure counterexamples are mechanized, and that they confirm `hproj` and the sound/complete split are non-redundant hypotheses.

---

### B2. RQ-to-theorem traceability matrix (§1.5) references files that do not appear in §9 reproducibility pointers

The traceability matrix cites `paper/lean/UadfU0/Definitions/Model.lean` and `paper/lean/UadfU0/U0Spec/Construction.lean`. The reproducibility section (§9) lists directories, not files. However, `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean` is referenced in §5.2 and the theorem catalog but **`paper/lean/UadfU0/CaseStudy`** does not appear in the §9 inclusion list. If this directory is absent from the submission package, `checkConsistent_iff_allThree` is unverifiable.

**Required fix:** Either add `paper/lean/UadfU0/CaseStudy` to the §9 artifact list, or add an explicit note that CaseStudy is included under the `paper/lean/UadfU0` directory glob. The current §9 list enumerates subdirectories but omits CaseStudy; the omission should be corrected.

---

### B3. Theorem count arithmetic is inconsistent with the theorem catalog

From `theorem_catalog.md`:
- `Definitions/Model.lean`: 3 theorems (`subset_refl`, `subset_trans`, `set_ext`)
- All other files: sum to 69

3 + 69 = 72. This checks out.

However, the §4.6 role breakdown states:
- Core: 22
- Supporting: 27
- Examples: 23
- Total: 72

The "example-level" count of 23 is defined as: 19 from `Examples/*.lean` + 4 from `CaseStudy/PasswordPolicy.lean`. Verifying from the catalog:
- `ArtifactBundleExample`: 4
- `AdequacyCounterexample`: 4
- `CompositionExample`: 1
- `ContradictoryLayers`: 3
- `TransferChainExample`: 2
- `TransferCounterexample`: 4
- `TransferExample`: 1
- `TwoLayer`: 0
Total Examples: 19 ✓ + CaseStudy 4 = 23 ✓

However: `Definitions/Model.lean` lists `subset_refl`, `subset_trans`, `set_ext` as theorems. These 3 are not in the core-22 list and not in the examples-23 list, so they must be in the supporting-27 count. The supporting count is stated as a remainder (`72 - 22 - 23 = 27`), so the numbers are consistent. **But** the theorem catalog section for `Definitions/Model.lean` labels `set_ext` and `subset_refl/trans` as theorem declarations — these are foundational axiom-like statements for the local SpecSet encoding. The paper should state explicitly in §4.6 whether these 3 are counted as "foundational infrastructure" within the supporting-lemma category, or whether they have some other status. Without this clarification, a reader checking the catalog will wonder why three apparent definitional lemmas appear in the theorem-keyword count at all.

**Required fix:** Add a single sentence to §4.6 clarifying that `subset_refl`, `subset_trans`, `set_ext` from `Definitions/Model.lean` are counted within the supporting-lemma group as foundational infrastructure for the local `SpecSet` encoding (not Mathlib imports).

---

### B4. `reproduce_formal.sh` exit behavior on hash mismatch is brittle for artifact evaluation

The script uses `set -euo pipefail` and exits on hash mismatch with `raise SystemExit(...)` inside a Python heredoc. The `SystemExit` in Python within a shell heredoc will not propagate as a non-zero exit to the shell under all `python3` versions (it depends on how the shell surfaces Python exit codes from `<<'PY'` heredocs). If the hash check silently passes despite a mismatch, artifact integrity is undetected.

**Required fix:** Replace the Python `raise SystemExit(...)` pattern with an explicit `sys.exit(1)` call **and** add a shell-level check after the heredoc:
```bash
python3 - <<'PY' || exit 1
import sys, hashlib, pathlib
...
    if got != want:
        sys.exit(f"hash mismatch: ...")
PY
```
Or restructure as individual `python3 -c` calls where exit codes are unambiguous. The current form may silently pass on some platforms.

---

## 4. Minor Editorial Issues

**E1. §2.3 "Pedagogical composite excerpt" note**
The note says the excerpt spans `Model.lean` and `Construction.lean` but the reader cannot tell which definitions come from which file. For a venue like ITP/CPP where artifact reviewers check this, a per-definition file annotation (even a comment in the code block) would help.

**E2. §3.3 — `UAndOn_empty_eq_univ` described twice**
The theorem is first described in the role-separation bundle (§3.3 third paragraph: "Under empty active set, `UAndOn` collapses to universal predicate") and then again in §5.3 (`contradictoryModel_empty_active_has_spurious_witness`). The duplication is not wrong, but consolidating the operational interpretation once (in §3.3) and forward-referencing from §5.3 would tighten the paper.

**E3. §4.3 item 4 vs. item 5 tension**
Item 4 says "`paper/lean/UadfU0` does not use `open Classical`". Item 5 says "some proofs still depend on core axioms through proof terms." This is technically accurate but will confuse readers unfamiliar with Lean4's implicit classical infrastructure. Adding a single parenthetical — e.g., "Lean4 core inference rules include classical choice; not using `open Classical` means no namespace is opened, but Lean4 kernel-level axioms remain available" — would prevent misreading.

**E4. §7 related work — no citation for BX/TGG (reference #8)**
Reference 8 (Xiong et al.) is the only BX citation. For TACAS/FASE audiences, at least one additional reference to BXSL or QVT-R-based synchronization work would strengthen the positioning claim in §7.4.

**E5. Abstract — "one-sided adequacy decomposition" phrasing**
The abstract uses "one-sided adequacy decomposition (sound/complete split, must/may variants)" — the must/may variants are not "one-sided" in the same sense as sound/complete. The phrasing conflates two independent axes. Suggest: "one-sided adequacy decomposition (sound and complete directions, in both must and may variants)".

**E6. §9 hash check command note**
The prose says "Run this hash check from repository root (not from `paper/lean` after `cd`)." This note is helpful but should also appear as a comment in `reproduce_formal.sh` at the point where the hash check runs, since users who invoke the script directly may not read the prose first.

---

## 5. Final Checklist to Reach Acceptance

- [ ] **B1**: Add one sentence to the abstract explicitly mentioning mechanized counterexamples as a contribution.
- [ ] **B2**: Add `paper/lean/UadfU0/CaseStudy` to the §9 artifact directory list.
- [ ] **B3**: Add one sentence in §4.6 clarifying the role of `subset_refl`, `subset_trans`, `set_ext` within the supporting-lemma count.
- [ ] **B4**: Fix `reproduce_formal.sh` hash-check exit-code propagation (use `sys.exit(1)` and shell-level `|| exit 1`).
- [ ] **E1** (recommended): Annotate per-definition file origin in §2.3 composite excerpt.
- [ ] **E3** (recommended): Clarify `open Classical` vs. kernel-axiom distinction in §4.3.
- [ ] **E5** (recommended): Fix "one-sided adequacy decomposition" phrasing in abstract.
- [ ] **E6** (optional): Mirror the "run from repo root" note as a comment in `reproduce_formal.sh`.
