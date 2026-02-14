# UAD/fモデルにおける型付きU0構成規則の機械検証

## 0. 位置づけ（結論先出し）
本稿は「UAD/f意味論の完全証明」ではなく、**U0構成規則の形式的コア**を Lean4 で機械検証する原著である。  
査読で問題になりやすい「定義の曖昧さ」「型不整合」「自明性」を避けるため、次を明示した。

1. `U, D, A, f` の型付き定義を本文に完結に記述
2. `f_{0i}^{-1}` をブラックボックス扱いせず、部分射影 `proj_i` から誘導定義
3. 単なる union 展開に留まらない性質（領域整合、層追加単調性、層間伝播、抽出判定の完全性）を証明

## 1. 問題設定と研究課題
多層仕様管理では、層ごとに異なる形式体系（自然言語、API、実装、契約）を使うため、共通の根仕様 `U0` をどう構成するかが曖昧になりやすい。  
特に既存説明では「`f^{-1}` で引き戻す」と述べても、`f` の型・部分性・層ごとの空間差が明示されないことがある。

本稿の研究課題（RQ）は以下。

- `RQ1`: 層ごとに型が異なる場合でも `U0` 構成を一貫して定義できるか。
- `RQ2`: `A_i ⊆ D_i`（許容集合は対象領域に含まれる）を `U0` 側に持ち上げられるか。
- `RQ3`: 層集合の追加・拡張に対して `U0` が単調に拡大することを示せるか。
- `RQ4`: 具体アーティファクト抽出から得る整合判定器を定義し、仕様述語との同値（健全性/完全性）を示せるか。

## 2. UAD/f の型付き定義
### 2.1 空間と層
- ルート空間（root universe）: `Ω`
- 層インデックス集合: `I`
- 各層の搬送型（layer carrier）: `β_i`

### 2.2 U, D, A, f
- `U_i` は本稿では `A_i` と同義に扱う（層仕様集合）
- `D_i ⊆ β_i`: 層 `i` の対象領域（Domain）
- `A_i ⊆ D_i`: 層 `i` の許容集合（Admissible）
- `f_{0i}` は部分写像として  
  \[
  f_{0i} : Ω \rightharpoonup β_i
  \]
  を取り、Lean では
  \[
  proj_i : Ω \to Option(β_i)
  \]
  で実装する（`none` = 未定義）。

### 2.3 誘導逆像（`f_{0i}^{-1}` の実体）
\[
f_{0i}^{-1}(S) := \{x \in Ω \mid \exists y \in β_i,\ proj_i(x)=some(y)\land y\in S\}
\]
（Lean: `preimage`）

### 2.4 U0 構成規則
\[
lifted(i) := f_{0i}^{-1}(A_i), \qquad
U0 := \bigcup_{i \in I} lifted(i)
\]

この定義により、本文の `f_{0i}^{-1}` 表記と Lean 実装（`proj` ベース）が一致する。

## 3. 主結果
### 定理1（誘導逆像の単調性）
\[
S \subseteq T \Rightarrow f_{0i}^{-1}(S) \subseteq f_{0i}^{-1}(T)
\]
Lean: `preimage_monotone`。

### 定理2（誘導逆像の和保存）
\[
f_{0i}^{-1}(S \cup T)=f_{0i}^{-1}(S)\cup f_{0i}^{-1}(T)
\]
Lean: `preimage_union`。

### 定理3（領域整合の持ち上げ）
\[
A_i \subseteq D_i \Rightarrow lifted(i) \subseteq f_{0i}^{-1}(D_i)
\]
Lean: `lifted_subset_preimage_domain`。

### 定理4（U0証人の領域妥当性）
\[
x \in U0 \Rightarrow \exists i,\exists y,\ proj_i(x)=some(y)\land y\in D_i
\]
Lean: `U0_witness_projects_to_some_domain`。

### 定理5（U0 の上限性）
\[
(\forall i,\ lifted(i)\subseteq B)\Leftrightarrow U0\subseteq B
\]
したがって冪集合順序で
\[
U0 = \bigsqcup_{i\in I} lifted(i)
\]
Lean: `U0_least_upper_bound_iff`, `U0_is_supremum`。

### 定理6（層追加に対する単調性）
`J,K : I→Prop` を有効層集合とし `J⊆K` とすると
\[
U0_J \subseteq U0_K
\]
Lean: `U0On_monotone`。

### 定理7（層間伝播定理）
`i,j` 間の関係 `R : β_i → β_j → Prop` が次を満たすとする。

1. `j` 側の任意の投影値 `y_j` に対し、`R` で関係づく `i` 側投影値 `y_i` が存在
2. `R` が `A_j` から `A_i` への許容性保存を満たす

このとき
\[
lifted(j) \subseteq lifted(i)
\]
が成り立つ。  
Lean: `lifted_transfer`（`paper/lean/UadfU0/InterLayer/Transfer.lean`）。

### 定理8（矛盾・整合の双対）
\[
Contradictory(i,j)\Leftrightarrow \neg Consistent(i,j)
\]
Lean: `contradictory_iff_not_consistent`。

### 定理9（抽出判定器の健全性・完全性）
ケーススタディ（パスワード長制約）で、アーティファクト

- 要求: `min_req ≤ n ≤ max_req`
- API: `min_api ≤ n`
- 実装: `n ≤ max_code`

から抽出する決定器
\[
check = \mathbf{decide}\left(\max(min\_req,min\_api)\le \min(max\_req,max\_code)\right)
\]
について
\[
check = true \Leftrightarrow \exists n,\ n \in lifted(req)\cap lifted(api)\cap lifted(code)
\]
が成り立つ。  
Lean: `checkConsistent_iff_allThree`（`paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`）。

## 4. 何が「自明」で何が本稿の増分か
確かに定理1,2,5,8は集合論の古典的事実に近い。  
本稿の増分は以下にある。

1. **型付き層モデル**: `β_i` を明示し、層ごと異型を許す。
2. **`f^{-1}` の具体化**: 抽象記号ではなく `proj_i : Ω → Option β_i` から誘導定義。
3. **`D/A` の接続証明**: `A_i ⊆ D_i` が `U0` 側の証人妥当性に伝播する（定理3,4）。
4. **運用上の性質**: 層追加時の `U0` 単調拡大（定理6）により、差分統合の理論的基礎を与える。
5. **層間意味保存**: 関係 `R` の仮定下で `lifted(j) ⊆ lifted(i)` を導く（定理7）。
6. **実行可能判定と論理仕様の同値**: 具体抽出器の判定式と交差非空性を同値化（定理9）。

## 5. 形式化実装と評価
### 5.1 実装構成
- `paper/lean/UadfU0/Definitions/Model.lean`: 型付き UAD/f 定義
- `paper/lean/UadfU0/U0Spec/Construction.lean`: 構成則と領域整合
- `paper/lean/UadfU0/U0Spec/Minimality.lean`: 上限性
- `paper/lean/UadfU0/InterLayer/Consistency.lean`: 矛盾/整合双対
- `paper/lean/UadfU0/InterLayer/Transfer.lean`: 層間伝播定理
- `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`: 抽出判定器の健全性/完全性
- `paper/lean/UadfU0/Examples/*.lean`: 一致例・矛盾例
- `paper/case-study/password_policy_benchmark.py`: 実証ベンチマーク

### 5.2 形式化規模（本稿時点）
- Leanファイル総行数: 649 LOC（ケーススタディ含む）
- `theorem` 宣言数: 27
- 中核定義: `Layer`, `Model`, `preimage`, `lifted`, `U0`

### 5.3 再現性
```bash
cd paper/lean
~/.elan/bin/lake build
```
- Lean4: `leanprover/lean4:v4.27.0`
- Lake: `5.0.0-src+db93fe1`
- 本稿作成時点で `Build completed successfully` を確認。

### 5.4 実証結果（合成データ）
`paper/case-study/password_policy_benchmark.py` を 5 seed × 200,000 例で実行した。

- 平均矛盾率: **0.214478**
- 平均処理時間: **0.7499 秒 / 200,000件**
- 平均スループット: **267,334 ケース/秒**

結果は `paper/case-study/benchmark_results.json` に保存。

## 6. 関連研究と位置づけ
本稿は既存理論を再発明するものではなく、UAD/f文脈における**最小コアの機械検証**を狙う。

- 抽象解釈・Galois connection（Cousot & Cousot）:
  逆像単調性・順序論は親和的だが、本稿は抽象化関手の完全性ではなく、部分射影由来の `U0` 構成を対象とする。
- Institution 理論（Goguen/Burstall）:
  言語間満足の移送と問題意識を共有するが、本稿は一般 institution 公理化ではなく、`Option` による部分性を明示した具体モデル。
- Refinement/traceability 系:
  層追加単調性（定理6）と層間伝播（定理7）を通じ、運用時の増分統合の基礎を与える。
- 形式手法実装（TLA+, Alloy, Lean）:
  これらを代替するのではなく、層横断の root 統合規則と抽出判定器の同値証明（定理9）に焦点を当てる。

## 7. 限界
本稿は以下を証明しない。

1. `proj_i` が実際の抽出器（AST解析器等）と意味的に同値であること（本稿はパスワード制約DSLまで）
2. UAD/f 全体の健全性・完全性
3. 大規模プロジェクトでの計算量特性（本稿実証は合成データ）

## 8. 今後
1. `proj` の合成則（`f_{0j} = g_{ij} ∘ f_{0i}` 型仮定）を導入し、層間保存定理を拡張する。  
2. 実抽出器（Rust AST / OpenAPI / 契約注釈）に対する意味保存証明を追加する。  
3. 公開アーカイブ（commit hash/DOI）付きで再現パッケージを整備する。

## 9. 結論
UAD/f の `U,D,A,f` を型付きで明示し、`f^{-1}` を部分射影から定義することで、`U0` 構成則の曖昧性を除去した。  
その上で、領域整合・上限性・層追加単調性・矛盾双対を Lean4 で機械検証し、`U0` を単なる記法ではなく、検証可能な統合演算として位置づけた。

---
### 参考文献（簡易）
- P. Cousot and R. Cousot, “Abstract Interpretation,” POPL 1977.  
- J. A. Goguen and R. M. Burstall, “Introducing Institutions,” 1984.  
- L. Lamport, *Specifying Systems* (TLA+), 2002.  
