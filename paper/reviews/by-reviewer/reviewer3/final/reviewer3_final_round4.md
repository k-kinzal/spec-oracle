Verdict: NG

## 致命点と最小修正案

### 1. 定義4.1の型不整合（`proj_j = bind(proj_i, g)` の検証不足）

**問題箇所**: §2.2および§4.2の組み合わせで、`proj_j x = Option.bind (proj_i x) g` の型を満たすための条件が本文で明記されていない。

**型検証**:
```
proj_i : Ω → Option β_i
g : β_i → Option β_j
bind : Option β_i → (β_i → Option β_j) → Option β_j
```

本文§2.2は `proj_i : Ω → Option β_i` を定義するが、§4.2の `g` が `M.carrier i → Option (M.carrier j)` である点は Lean コードで確認できる一方、本文では `g` の型宣言が不足している。

**Lean対応確認**: `paper/lean/UadfU0/InterLayer/Composition.lean` L13-15:
```lean
def pullbackVia
    {i j : ι}
    (g : M.carrier i → Option (M.carrier j))
```

**修正案**: §4.2の定理文冒頭に「`g : β_i → Option β_j` を部分写像とし」を追加。

---

### 2. 定理4.3の片側仮定の意味論的曖昧性（sound/complete定義の逆）

**問題箇所**: §4.3で「偽陰性回避は completeness 側」「偽陽性回避は soundness 側」と記述されているが、これは定義4.3の `hSound` / `hComplete` の向きと直感的に逆である可能性がある。

**型検証**:
- `hSound : proj x = some y → E x y` (射影が成功すれば抽出関係も成立)
- `hComplete : E x y → proj x = some y` (抽出関係が成立すれば射影も成功)

**Lean確認**: `paper/lean/UadfU0/InterLayer/Adequacy.lean` L20, L32で型は一致。

**意味論的矛盾**: 本文では「偽陰性（見逃し）回避 = completeness」と書かれているが、`hComplete` は「E が成立すれば proj も成立」を保証するもので、通常の形式検証用語では「proj が E の完全な表現」を意味する。一方、偽陰性回避（見逃し回避）は「実際に満足する点を漏らさない」ことであり、むしろ `hSound` 側（`proj ⊆ E` に相当）が偽陽性回避、`hComplete` 側（`E ⊆ proj` に相当）が偽陰性回避となるべき。

**修正案**: §4.3の運用帰結3段落を以下に差し替え:
```
- 偽陽性（存在しない整合を報告）を避ける側に効くのは soundness 側 (preimage ⊆ semanticPullback) である。
- 偽陰性（見逃し）を避ける側に効くのは completeness 側 (semanticPullback ⊆ preimage) である。
- U∧ の空判定を安全側（「空なら本当に空」）で使うには soundness 側が必要となる。
```

---

### 3. 中核定理4.1の必要性主張の欠落（注意書きの位置ミス）

**問題箇所**: §4.1で「注意: 本定理は仮定1,2の**十分性**を示す。必要性（より弱い仮定では不可能であること）は本稿では証明していない。」と記載されているが、この記述が定理記述の直後にあるため、定理4.1自体の妥当性が疑われる構造になっている。

**Lean確認**: `paper/lean/UadfU0/InterLayer/Transfer.lean` L11-28 で `lifted_transfer` は実装されており、十分性は検証済み。

**修正案**: 注意書きを §4.6（基礎補題）または §9（限界）へ移動し、定理4.1直後では「仮定1,2の下で成立」とのみ記述する。
