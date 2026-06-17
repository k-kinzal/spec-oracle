# Mechanization Review: UAD/f U0 Specification Proof

**VERDICT: NG** (Major Revisions Required)

## MAJOR ISSUES

### M1: Incomplete Lean Source Disclosure (Critical)
**Section §7.4, §11 (Appendix A)**

The paper claims 1502 LOC across 9 core Lean files but Appendix A truncates mid-file (`ArtifactBundleExample.lean` ends abruptly at `fu`). Missing files:
- `UadfU0/Definitions/Model.lean` (partial)
- `UadfU0/U0Spec/Construction.lean`
- `UadfU0/U0Spec/Minimality.lean`
- `UadfU0/U0Spec/IdealRoot.lean`
- `UadfU0/InterLayer/*.lean` (5 files)
- `UadfU0/RelatedWork/Galois.lean`
- `UadfU0/Examples/*.lean` (remaining 4 files)

**Impact**: Cannot verify 45+ claimed theorems (§7.4 lists 59 total, only ~10 visible). Build reproducibility unverifiable.

**Required**: Include **all** Lean sources in full, or provide working Git commit hash + repository URL with explicit file list matching §7.4 theorem count.

---

### M2: RQ5-RQ6 Boundary Confusion
**Section §4.3, §6.2**

Paper states:
> "RQ5 (theory):抽象関係 `E` に対する一般結果であり、特定抽出器（regex/LLM等）へ適用するには、その抽出器が soundness/completeness 前提を満たすことの別証明が必要"

Yet §6.2 claims:
> "regex 抽出そのものの soundness/completeness を証明していない。したがって「抽出結果が `A(i)` を正しく表す」ことは未検証"

**Contradiction**: If RQ5 only covers abstract `E`, and regex adequacy is unproven, then §6.2's "detected_contradictory=true" cannot claim to instantiate Theorem 4.3's guarantees. The paper oscillates between "RQ5 solved (abstract)" vs "RQ6 PoC only" without reconciling the gap.

**Required**: 
1. Explicitly state RQ5 contributes **theorem templates** only (no instantiation).
2. Reclassify §6.2 as "抽出パイプライン実行デモ（定理適用範囲外）" in abstract/conclusion.
3. Add §4.3 note: "実抽出器への適用例は本稿未実施（RQ5理論のみ）".

---

### M3: Main Theorem-to-RQ Mapping Incomplete
**Section §4, §7.6**

Table §7.6 lists Lean files but omits **explicit theorem names** for core claims:
- §4.1 transfer: cites `lifted_transfer` but no parameter signature shown.
- §4.5 GLB: cites `UAndOn_greatest_lower_bound_iff` but theorem statement absent.
- §3.5 ideal root claims list 7 theorem names but no `.lean` line numbers or statement bodies.

**Comparison failure**: Reader cannot cross-check §4's prose claims against actual Lean code structure without seeing theorem types.

**Required**: For each RQ1-RQ6 main theorem, include:
```
theorem <name> : <type> := ...
-- File: UadfU0/.../X.lean:L123-L145
```
in §7.6 or Appendix B (separate from full code dump).

---

## MINOR ISSUES

### m1: Build Manifest Verifiability Gap
**Section §7.2**

- `manifest SHA256` listed but no independent verification method (e.g., `sha256sum lake-manifest.json` command).
- `lake build` reproduction instruction lacks error handling guidance (what if version mismatch?).

**Fix**: Add "Verification: `sha256sum paper/lean/lake-manifest.json` should output `8c098d78...`".

---

### m2: PoC Negative Case Underpowered
**Section §6.4**

Regex drift example only tests pattern **absence** (`"inclusive"` removed). Does not test:
- False positive (extracting wrong boundary from unrelated text).
- Unit mismatch (bytes vs characters).
- Implicit default handling (missing lower bound).

**Fix**: Add 1-2 sentences: "負例は抽出失敗（none化）のみ検証。誤抽出（false positive）・単位換算・暗黙値は未テスト（限界§9）。"

---

### m3: `Ω` vs `Ω_art` Notation Overload
**Section §2.5, §6.1.1**

Paper uses `Ω` for both:
1. Abstract root space (挙動宇宙, §2.5).
2. Concrete `ArtifactBundle` type (§6.1.1).

Then states "本稿が要求するのは `Ω` の全列挙ではなく membership 判定" but §6.1.1's `Ω_art` **is** a concrete enumerable type.

**Fix**: Use `Ω_abs` vs `Ω_art` consistently, or add note: "§6実装では `Ω := ArtifactBundle`（具体型）を採用。抽象 `Ω` は構成テンプレート（§2.5）として残す。"

---

### m4: MUS Definition Without Algorithm Claim Clarity
**Section §3.4**

States "MUS抽出アルゴリズムの正当性証明は今後課題" but then defines `MUS(active)` formally. Unclear if:
- Definition is Lean-mechanized (type-level only)?
- Or just LaTeX prose?

**Fix**: Add parenthetical: "（定義のみLean化済、抽出手続きは未実装）" or cite specific `.lean` file if mechanized.

---

## REQUIRED CHANGES (Prioritized)

1. **[Critical]** Complete Appendix A with all 9 Lean files in full (or provide Git URL + commit hash with explicit file manifest).
2. **[Blocker]** Clarify RQ5-RQ6 boundary: Abstract theorem (RQ5) vs regex PoC (RQ6 未適用) in §1, §4.3, §6.2, §10.
3. **[High]** Add theorem statement table (name + type + file:line) for RQ1-RQ6 main theorems in §7.6 or new Appendix B.
4. **[Medium]** Strengthen PoC negative case description (§6.4) to acknowledge untested error modes.
5. **[Low]** Fix `Ω` notation overload (§2.5 vs §6.1.1).
6. **[Low]** Add build verification command (§7.2).
7. **[Low]** Clarify MUS mechanization scope (§3.4).

---

## RISK ASSESSMENT (2-4 sentences)

**Primary risk**: Incomplete Lean source disclosure undermines core mechanization claim. Without verifying `InterLayer/*.lean` + `U0Spec/*.lean` (933 LOC, 62% of claimed proof mass), reviewers cannot confirm RQ1-RQ4 are machine-checked.

**Secondary risk**: RQ5/RQ6 boundary confusion creates ambiguity about whether §6.2's "contradiction detection" instantiates proven theorems or merely demonstrates pipeline execution. Current framing risks overclaiming PoC as validated against Theorem 4.3.

**Mitigation path**: (1) Full Lean disclosure + reproducible build, (2) downgrade §6.2 claims to "technical execution demo (theorem application out-of-scope)", (3) add theorem-statement cross-reference table. If M1-M3 addressed, paper becomes mechanization-acceptable with clear PoC boundaries.
