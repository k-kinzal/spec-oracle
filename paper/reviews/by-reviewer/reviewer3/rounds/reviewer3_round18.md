**VERDICT: NG**

## Detailed Checklist Evaluation

**Q1. Is PoC scope explicitly limited (not claiming full framework validation)?**  
**YES** - The manuscript explicitly limits PoC claims:
- "本節は `RQ6 (practice)`（技術的再実行可能性）を対象とする" (§6.2)
- "本節のスクリプトは、主として `extract_i` の実行可能性を検証する" (§6.2)
- "本結果は contradiction 発生率を推定する統計研究ではなく、抽出から判定までの**パイプライン実行可能性デモ**として解釈する" (§6.2)
- "選定は「3層公開・数値境界制約・URL固定取得可能」という実行要件に基づく convenience sample である" (§6.2)

**Q2. Is mutation detection evidence tied to script output/artifacts?**  
**YES** - Mutation results are properly evidenced:
- `external_validation_results.json` contains mutation detection data with explicit `mutated_intersection_lower/upper` values
- `external_validation_offline.log` shows identical mutation results (3/3 detected)
- Each mutation shows `lower > upper` as expected (PostgreSQL: 64>63, zlib: 10>9, SQLite: 65537>65536)
- Quote: "変異試験（`requirement.lower = upper + 1`）で矛盾検出感度を確認" (§6.2 デモ実行結果)

**Q3. Is regex drift failure evidenced by actual log?**  
**YES** - Drift failure is demonstrated with actual execution log:
- `regex_drift_failure.log` shows concrete `ValueError` when "inclusive" is removed
- Quote: "再現ログは `paper/case-study/real_projects/logs/regex_drift_failure.log` に保存した" (§6.4)
- Log shows pattern `between ([0-9]+) and 65536 inclusive` failing on input `between 512 and 65536 bytes`

**Q4. Are threats explicitly listed (sampling bias, regex brittleness, mutation limits)?**  
**YES** - Multiple threat categories documented:
- Sampling bias: "対象3件は...convenience sample であり、母集団代表ではない" (§6.5 threat 1)
- Regex brittleness: "本PoCは project-specific regex に依存する pattern-based 抽出であり、一般NL理解器の性能を示さない" (§6.5 threat 2)
- Mutation limits: "現在の mutation は `lower > upper` 系の sanity check であり、微小差分（境界包含/排他、単位換算、暗黙デフォルト）への感度を測っていない" (§6.5 threat 4)

**Q5. Is model-PoC connection stated (Omega_art / obs-extract-proj decomposition for PoC)?**  
**YES** - Connection is explicitly stated:
- "PoCにおけるモデル接続（§2.6の具体化）: `Ω_art := Γ_req × Γ_api × Γ_code`（同一時点で取得した3層artifact束）" (§6.2)
- "`obs_i` は `Ω_art` からの成分射影" (§6.2)
- "`extract_i` は現行regex抽出器" (§6.2)
- "`proj_i = Option.bind obs_i extract_i`" (§6.2)

---

## Blocking Issues

### 1. **RQ5/RQ6 boundary violation in scope claim**

The manuscript states:
> "本節は `RQ6 (practice)`（技術的再実行可能性）を対象とする。`RQ5 (theory)` の adequacy（§4.3）で使う抽象関係 `E` について、regex抽出器が意味保存性を満たすことは本節で証明していない。" (§6.2)

However, the **section heading for §6.2** reads:
> "### 6.2 実OSS抽出パイプラインデモ（PostgreSQL / zlib / SQLite）"

This creates **ambiguity** because:
- The heading does not explicitly say "PoC" or "technical reproducibility only"
- Readers may misinterpret this as validating the *theoretical model* on real projects
- The actual scope (RQ6 only, not RQ5 application) is buried in paragraph text

**Fix**: Retitle §6.2 to make PoC status explicit in the heading itself:
```
### 6.2 抽出パイプライン技術的再実行可能性デモ（PoC: PostgreSQL / SQLite / zlib）
```

Add a prominent scope box at the start of §6.2:
```
**PoC範囲明示**: 本節はRQ6（技術的再実行可能性）のみを対象とする。
RQ5（抽出器adequacy）の実証は対象外である。
```

---

### 2. **Mutation evidence gap: no direct link to `run()` implementation**

The mutation results show `lower > upper` detection, but:
- The manuscript states: "スクリプト内部では `check_consistent` が `lower <= upper` を判定し、変異は `requirement.lower = upper + 1` を注入する（`external_validation.py` の `run` 関数）"
- However, **`external_validation.py` does NOT contain a visible mutation injection block** in the provided code

The `run()` function creates mutation results like this:
```python
mutated_requirement = LayerBounds(
    lower=upper + 1,  # <-- mutation happens here
    upper=p.requirement.upper,
    ...
)
```

But this is **inline code**, not a clearly separated "mutation test" block.

**Problem**: A reader inspecting the code may not immediately recognize where/how the mutation is injected, reducing transparency.

**Fix**: Add explicit comments or a helper function to mark mutation injection:
```python
def inject_mutation_lower_exceeds_upper(requirement: LayerBounds, upper: int) -> LayerBounds:
    """Mutate requirement.lower to exceed implementation upper bound (sanity check)."""
    return LayerBounds(
        lower=upper + 1,
        upper=requirement.upper,
        source=requirement.source,
        note="mutation: stale requirement lower bound exceeds implementation/API upper bound",
    )
```

---

### 3. **Edge case log exists but is NOT referenced in main text**

The file `check_consistent_edge_cases.log` exists and demonstrates boundary behaviors:
```
contradiction_min_gt_max {'consistent': False, 'lower': 2048, 'upper': 1024}
boundary_equal {'consistent': True, 'lower': 63, 'upper': 63}
zero_and_negative {'consistent': True, 'lower': -1, 'upper': 9}
missing_bounds {'consistent': False, 'lower': None, 'upper': None}
```

However, **this log is NOT cited anywhere in the manuscript**.

**Problem**: The manuscript mentions:
> "追加の境界挙動ログ: `paper/case-study/real_projects/logs/check_consistent_edge_cases.log`" (§6.4)

But it does NOT explain:
- What these edge cases test
- Whether they are part of the PoC or separate validation
- How they relate to the mutation test

**Fix**: Add a brief explanation in §6.4:
```
境界挙動の補足検証として、`check_consistent_edge_cases.log` に以下を記録した:
- `min > max`: 矛盾検出の正常動作
- `min = max`: 境界一致ケースの許容
- 負値含む区間: 負境界値の扱い（zlib -1など）
- 境界欠損: `None`を含む場合の判定失敗

これらは主PoC（3プロジェクト）の補助的な動作確認であり、網羅的な境界値テストではない。
```

---

## Non-blocking Suggestions

1. **Mutation test description could use a table**: The mutation results are listed in JSON but could be more readable as:
   ```markdown
   | Project | Original [lower, upper] | Mutated [lower, upper] | Detected? |
   |---------|-------------------------|------------------------|-----------|
   | PostgreSQL | [1, 63] | [64, 63] | Yes |
   | zlib | [-1, 9] | [10, 9] | Yes |
   | SQLite | [512, 65536] | [65537, 65536] | Yes |
   ```

2. **Regex drift failure could include original pattern expectation**: The log shows the failure but could be clearer if it showed:
   ```
   Expected pattern: "between X and Y inclusive"
   Actual input: "between X and Y bytes"
   Missing token: "inclusive"
   ```

3. **Extraction pattern table is verbose**: The `extraction_patterns` section in JSON has quadruple-escaped backslashes (`\\\\s+`). This is technically correct for JSON→Python→regex, but readers may find it confusing. Consider adding a note:
   ```
   注: extraction_patterns内のパターンはJSON→Python→regex経由のためエスケープが多層になっている。
   実際の正規表現は例えば `\s+` である。
   ```

---

## Summary

**Blocking reasons for NG verdict**:
1. Section heading §6.2 does not make PoC-only scope explicit (buried in body text)
2. Mutation injection mechanism is not clearly separated/documented in code
3. Edge case log exists but is unreferenced in text

**Fix priority**:
- **High**: Add PoC scope box + heading update for §6.2
- **Medium**: Add mutation helper function or inline comment block
- **Low**: Reference edge case log in §6.4 with brief explanation
