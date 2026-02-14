# UAD/fモデルでのU0仕様の証明

## 要旨
本稿は、UAD/fモデルにおける根仕様 `U0` を、各投影宇宙 `Ui` からの逆写像 `f₀ᵢ⁻¹` の和集合として構成する仕様を形式化し、Lean4で証明する。主結果は次の2点である。

1. `U0` の構成同値: `x ∈ U0 ↔ ∃i, x ∈ f₀ᵢ⁻¹(Ui)`
2. `U0` の最小上界性: すべての `f₀ᵢ⁻¹(Ui)` を含む集合 `B` に対して `U0 ⊆ B`、かつこの意味で `U0` は最小

加えて、層間の整合性・矛盾検出に必要な補助定理（`Consistent` と `Contradictory` の双対性）を示す。

## 1. 定義
`α` を仕様要素の型、`ι` を層インデックス型とする。モデル `M` は以下からなる。

- `Ui : ι → Set α`（各層の仕様集合）
- `inv : ι → Set α → Set α`（逆写像 `f₀ᵢ⁻¹` の集合レベル表現）

ここで、

- `lifted(i) := inv i (Ui i)`
- `U0 := { x | ∃ i, x ∈ lifted(i) }`

と定義する。

## 2. 主定理
### 定理1（構成同値）
任意の `x` について
`x ∈ U0 ↔ ∃ i, x ∈ lifted(i)` が成り立つ。

Lean対応: `paper/lean/UadfU0/U0Spec/Construction.lean` の `mem_U0_iff`。

### 定理2（最小上界性）
任意の集合 `B` に対して
`(∀ i, lifted(i) ⊆ B) ↔ (U0 ⊆ B)`。

これは `U0` が `lifted(i)` 族の最小上界であることを意味する。

Lean対応: `paper/lean/UadfU0/U0Spec/Minimality.lean` の `U0_least_upper_bound_iff`。

## 3. 補助定理（層間整合）
2層 `i, j` に対して、

- `Contradictory(i,j) := ∀x, x∈lifted(i) → x∈lifted(j) → False`
- `Consistent(i,j) := ∃x, x∈lifted(i) ∧ x∈lifted(j)`

と置くと、
`Contradictory(i,j) ↔ ¬Consistent(i,j)` が成り立つ。

Lean対応: `paper/lean/UadfU0/InterLayer/Consistency.lean` の `contradictory_iff_not_consistent`。

## 4. 実装と検証
Lean4実装は `paper/lean` に配置し、`lake build` により型検査・証明検証を行う。

主なファイル:

- `paper/lean/UadfU0/Definitions/Model.lean`: UAD/f最小モデル定義
- `paper/lean/UadfU0/U0Spec/Construction.lean`: 構成同値と非空性
- `paper/lean/UadfU0/U0Spec/Minimality.lean`: 最小上界性
- `paper/lean/UadfU0/InterLayer/Consistency.lean`: 整合性/矛盾の補助定理
- `paper/lean/UadfU0/Examples/TwoLayer.lean`: 2層具体例

## 5. 結論
UAD/fモデルにおける `U0 = ⋃ᵢ f₀ᵢ⁻¹(Ui)` をLean4で機械検証し、`U0` の構成同値と最小上界性を示した。これにより、U0を人手で記述せず逆写像合成から構成する仕様原理を形式的に裏付けた。
