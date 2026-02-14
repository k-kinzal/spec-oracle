# UAD/fにおける根仕様統合の型付き意味論: U0構成規則のLean4形式化

## 0. 位置づけ（結論先出し）
本稿は「UAD/f意味論の完全証明」ではなく、**根仕様統合（U0構成）の形式的コア**を Lean4 で機械検証する原著である。  
査読で問題になりやすい「定義の曖昧さ」「型不整合」「自明性」を避けるため、次を明示した。

1. `U, D, A, f` の型付き定義を本文に完結に記述
2. `f_{0i}^{-1}` をブラックボックス扱いせず、部分射影 `proj_i` から誘導定義
3. 単なる union 展開に留まらない性質（領域整合、層追加単調性、層間伝播、層間合成則）を証明
4. ケーススタディ（パスワード長制約）において、具体抽出判定器の健全性・完全性を実証
5. 実OSS由来アーティファクト（PostgreSQL/zlib/SQLite）で外的整合性評価を実施

本稿の投稿種別は「新公理系の提案」ではなく**形式化原著（mechanization paper）**である。  
主張範囲は「型付きUAD/fコアの曖昧性除去」と「再利用可能な機械証明ライブラリの提供」を中核とし、外的評価は3件の実OSSケーススタディに限定する（産業規模での一般有効性は主張しない）。

## 1. 問題設定と研究課題
多層仕様管理では、層ごとに異なる形式体系（自然言語、API、実装、契約）を使うため、共通の根仕様 `U0` をどう構成するかが曖昧になりやすい。  
特に既存説明では「`f^{-1}` で引き戻す」と述べても、`f` の型・部分性・層ごとの空間差が明示されないことがある。

本稿の研究課題（RQ）は以下。

- `RQ1`: 層ごとに型が異なる場合でも `U0` 構成を一貫して定義できるか。
- `RQ2`: `A_i ⊆ D_i`（許容集合は対象領域に含まれる）を `U0` 側に持ち上げられるか。
- `RQ3`: 層集合の追加・拡張に対して `U0` が単調に拡大することを示せるか。
- `RQ4`: 一般抽出関係 `E` と `proj` の点ごとの同値仮定から逆像一致を導けるか。また、具体事例（パスワード長制約）において判定器同値性を証明可能か。
- `RQ5`: 現実のOSS仕様/API/実装アーティファクトから抽出した制約は、本モデル上で一貫に扱えるか。

### 1.1 UAD/fモデルの出典と本稿の責務
本稿では UAD/f を**本稿内で自己完結に定義されるモデル**として扱う。  
したがって、外部文献の略記定義には依存せず、`Ω, I, β_i, D_i, A_i, proj_i` の全構成要素を本文と Lean 実装の双方で明示する。

### 1.2 RQに対する評価軸
本稿の評価は以下の4軸で行う。

| 軸 | 評価内容 | 本稿での指標 |
|---|---|---|
| 定義妥当性 | 型の整合・定義の非曖昧性 | §2 と `Model.lean` の1対1対応 |
| 理論妥当性 | RQに対応する不変条件・定理 | §3 の定理1〜12 |
| 形式化コスト | 形式化規模と難所の透明化 | §4.2, §5.2 |
| 再現可能性 | 他者が同一結果を再実行可能か | §5.3（toolchain/manifest/commit） |
| 外的妥当性（RQ5） | 実アーティファクトへの適用可能性 | §5.5（`n_real_projects=3`, `n_real_consistent=3`, 変異検出 `3/3`） |

## 2. UAD/f の型付き定義
### 2.1 空間と層
- ルート空間（root universe）: `Ω`
- 層インデックス集合: `I`
- 各層の搬送型（layer carrier）: `β_i`

### 2.2 U, D, A, f
- `U_i` は本稿では `A_i` と同義に扱う（層仕様集合）
- `D(i) ⊆ β_i`: 層 `i` の対象領域（Domain）
- `A(i) ⊆ D(i)`: 層 `i` の許容集合（Admissible）
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

本文定義（集合内包記法）:
\[
f_{0i}^{-1}(S) := \{x \in Ω \mid \exists y \in β_i,\ proj_i(x)=some(y)\land y\in S\}
\]

Lean実装（関数定義、`paper/lean/UadfU0/Definitions/Model.lean:80-81`）:
```lean
def preimage (M : Model ι α) (i : ι) (S : SpecSet (M.carrier i)) : SpecSet α :=
  fun x => ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ S
```

**対応関係の説明**: Lean では `SpecSet Ω := Ω → Prop` により仕様集合を述語関数として実装する。
したがって `fun x => ...` の型シグネチャ `x : Ω` (すなわち `x : α`) が、本文における `x ∈ Ω` の明示的束縛に対応する。
集合内包記法 `\{x \in Ω \mid P(x)\}` は、Lean型理論では関数定義 `fun (x : Ω) => P(x) : Ω → Prop` と同値である。
この対応により、本文の集合論的記述と Lean 実装は形式的に等価である。

### 2.4 U0 構成規則
\[
lifted(i) := f_{0i}^{-1}(A(i)), \qquad
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

適用例（Lean）:
- `paper/lean/UadfU0/Examples/TransferExample.lean`: `false → true` の伝播
- `paper/lean/UadfU0/Examples/TransferChainExample.lean`: `code → api` と `api → req` の2段伝播

運用シナリオ（例）:
- API層で `minLen ≥ 12` が確定したとき、実装層抽出から `minLen ≥ 8` が得られても、`R` による許容性保存が成立すれば root 側ではより強い制約へ安全に伝播できる。
- 契約注釈層から要求層へのトレーサビリティ更新時に、`lifted_transfer` は「更新で失われない整合集合」を保証する補題として使える。

### 定理8（矛盾・整合の双対）
\[
Contradictory(i,j)\Leftrightarrow \neg Consistent(i,j)
\]
Lean: `contradictory_iff_not_consistent`。

### 定理9（層間合成則）
`proj_j = bind(proj_i, g)` を満たすとき
\[
f_{0j}^{-1}(S) = f_{0i}^{-1}(g^{-1}(S))
\]
が成り立つ（`g^{-1}` は `pullbackVia` として定義）。  
Lean: `preimage_compose`（`paper/lean/UadfU0/InterLayer/Composition.lean`）。

仮定 `proj_j = bind(proj_i, g)` は、層`j`抽出器が層`i`抽出器の後段変換として実装される場合を表す。  
具体例は `paper/lean/UadfU0/Examples/CompositionExample.lean` に示した。

運用シナリオ（例）:
- `i`: API仕様（OpenAPI）抽出、`j`: セキュリティ要求抽出とすると、`g` は「API制約から要求制約への写像」になる。  
  このとき定理9は、要求層での逆像計算を API層での逆像＋`g`の引き戻しに分解できることを保証し、抽出チェーンの差分検証に使える。

### 定理10（抽出関係の一般適合定理）
`E : Ω → β_i → Prop` が
\[
proj_i(x)=some(y) \Leftrightarrow E(x,y)
\]
を満たすとき
\[
f_{0i}^{-1}(S)=\{x\in Ω \mid \exists y,\ E(x,y)\land y\in S\}
\]
が成り立つ。  
Lean: `preimage_eq_semanticPullback`（`paper/lean/UadfU0/InterLayer/Adequacy.lean`）。

### 定理11（具体抽出判定器の健全性・完全性）
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
Lean: `req_projection_adequacy`, `checkConsistent_iff_allThree`（`paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`）。

### 定理12（部分射影下での非随伴性）
層 `i` に対して `∃x0, proj_i(x0)=none` が成り立つとき、`preimage_i` は冪集合上の左随伴を持たない：
\[
\neg \exists F,\ \forall S,T,\ F(S)\subseteq T \Leftrightarrow S\subseteq preimage_i(T)
\]
Lean: `no_left_adjoint_of_partial`（`paper/lean/UadfU0/RelatedWork/Galois.lean`）。

## 4. 何が「自明」で何が本稿の増分か
確かに定理1,2,5,8は集合論の古典的事実に近い。  
本稿の増分は以下にある。

1. **型付き層モデル**: `β_i` を明示し、層ごと異型を許す。
2. **`f^{-1}` の具体化**: 抽象記号ではなく `proj_i : Ω → Option β_i` から誘導定義。
3. **`D/A` の接続証明**: `A_i ⊆ D_i` が `U0` 側の証人妥当性に伝播する（定理3,4）。
4. **運用上の性質**: 層追加時の `U0` 単調拡大（定理6）により、差分統合の理論的基礎を与える。
5. **層間意味保存**: 関係 `R` の仮定下で `lifted(j) ⊆ lifted(i)` を導く（定理7）。
6. **層間合成の保存則**: `proj_j = bind(proj_i,g)` から逆像合成則を導出（定理9）。
7. **一般適合＋具体実装の二段構成**: `proj` と抽出関係 `E` の一致から逆像一致を導き（定理10）、その後に具体判定器同値へ落とす（定理11）。
8. **既存随伴理論との差分の形式証明**: 未定義点を持つ部分射影では `preimage` が左随伴を持たないことを機械検証（定理12）。

### 4.1 機械検証の必要性：型検証上の非自明点

定理1,2,5,8が集合論の古典的事実に近いことは認める。しかし、**型付き設定と部分射影の組合せ**により、既存証明の単純移植では済まない障害が生じる。具体的には：

**1. 依存型環境での存在型スコープ問題**
`carrier : I → Type` の依存型により、`preimage` の定義は層ごとに異なる型 `β_i` を扱う。
このため、`∃ y : β_i, ...` の存在型束縛は層 `i` に依存して型付けされ、素朴な集合論公式 `f^{-1}(S ∪ T) = f^{-1}(S) ∪ f^{-1}(T)` を直接適用できない。
例えば定理2 (`preimage_union`) の証明では、`∃ y, ... ∧ (y ∈ S ∨ y ∈ T)` を `(∃ y, ... ∧ y ∈ S) ∨ (∃ y, ... ∧ y ∈ T)` へ変形する際、
`y` の型が `M.carrier i` であることを Lean が追跡し続ける必要がある。これは型検証器の助けなしでは見落としやすい微妙な依存関係である。

**2. `Option.bind` の正規化と可換条件**
定理9 (`preimage_compose`) では、`proj_j = bind(proj_i, g)` の仮定下で逆像合成則を導く。
Lean では `Option.bind` が `some/none` 場合分けを含むため、`proj_j x = some z` ⇔ `∃ y, proj_i x = some y ∧ g y = some z` という展開が自動的には成立しない。
実装では補題 `Option.bind_eq_some` を明示的に適用し、`bind` 定義を展開した上で存在型を整理する必要があった。
この種の正規化ステップは、紙上証明では「自明」として飛ばされがちだが、型検証器はこれを許さない。

**3. `SpecSet` の membership/subset インスタンス定義**
本稿では `SpecSet α := α → Prop` により集合を述語関数として実装する。
このため、`x ∈ S` を `S x` と解釈し、`S ⊆ T` を `∀ x, S x → T x` と展開するための `Membership` / `HasSubset` インスタンスが必須となる。
さらに、定理の大半が集合の外延同値 `A = B ⇔ ∀ x, x ∈ A ↔ x ∈ B` に依存するため、
補題 `set_ext`（`funext` と `propext` の組合せ）を全証明の共通基盤として確立した。
これは型理論実装特有の技術負債であり、集合論では暗黙の公理として扱われる部分である。

**4. 部分性 (`Option`) の伝播追跡**
`proj : α → Option β` の部分性により、すべての定理で「`proj x = some y` が成り立つ場合のみ議論する」という条件が伝播する。
例えば定理3 (`lifted_subset_preimage_domain`) では、`x ∈ lifted i` から `proj i x = some y` かつ `y ∈ D i` を導く際、
`some y` のパターンマッチが正しく型付けされているか検証器が逐一確認する。
この種の部分性追跡は、紙上では「well-defined な場合に限る」で済ませるが、機械検証では各ステップで型証明が要求される。

これらの技術点は、集合論レベルでは「自明」でも、型付き関数型言語での形式化では非自明な障害となる。
したがって、本稿の機械検証は単なる既知事実の再確認ではなく、**型理論実装における具体的設計選択の検証**として意義を持つ。

定理本文との対応（要約）:
- 定理2（`preimage_union`）: 依存型存在証人 `∃ y : carrier i` のスコープ保持が必要。
- 定理3（`lifted_subset_preimage_domain`）: `proj i x = some y` の証人を経由しないと `A(i) ⊆ D(i)` を root 側へ移送できない。
- 定理9（`preimage_compose`）: `Option.bind` の `some/none` 分岐正規化が証明の中心ステップ。

### 4.2 非自明性の定量スナップショット
本稿で最も証明負荷が高い3定理について、手続き上の複雑度を示す（Leanスクリプト読取ベース）。

| 定理 | 主な難所 | 手続き指標（概数） |
|---|---|---|
| `preimage_union` | 存在量化と論理和の分配 | `rcases` 3回、`constructor` 2段 |
| `lifted_transfer` | 関係 `R` の証人引き戻し | `rcases` 4回、存在証人再構成 2段 |
| `preimage_compose` | `Option.bind` の `some/none` 分岐正規化 | `by_cases` 2分岐、`calc` 4本、反証1箇所 |

## 5. 形式化実装と再現性
### 5.1 実装構成
- `paper/lean/UadfU0/Definitions/Model.lean`: 型付き UAD/f 定義
- `paper/lean/UadfU0/U0Spec/Construction.lean`: 構成則と領域整合
- `paper/lean/UadfU0/U0Spec/Minimality.lean`: 上限性
- `paper/lean/UadfU0/InterLayer/Consistency.lean`: 矛盾/整合双対
- `paper/lean/UadfU0/InterLayer/Transfer.lean`: 層間伝播定理
- `paper/lean/UadfU0/InterLayer/Composition.lean`: 層間合成則
- `paper/lean/UadfU0/InterLayer/Adequacy.lean`: 抽出関係の一般適合定理
- `paper/lean/UadfU0/RelatedWork/Galois.lean`: 部分射影下での非随伴性
- `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`: 抽出判定器の健全性/完全性
- `paper/lean/UadfU0/Examples/*.lean`: 一致例・矛盾例・伝播例・合成例
- `paper/case-study/password_policy_benchmark.py`: 判定式と全探索の一致検証
- `paper/case-study/real_projects/external_validation.py`: 実OSS由来アーティファクト検証

### 5.2 形式化規模（本稿時点）
- Leanファイル総行数: 979 LOC（関連研究比較の形式証明を含む）
- `theorem` 宣言数: 35
- 中核定義: `Layer`, `Model`, `preimage`, `lifted`, `U0`

### 5.3 再現性
```bash
cd paper/lean
~/.elan/bin/lake build
```
- Lean4: `leanprover/lean4:v4.27.0`
- Lake: `5.0.0-src+db93fe1`
- toolchainファイル: `paper/lean/lean-toolchain`
- Lake定義: `paper/lean/lakefile.lean`
- manifest: `paper/lean/lake-manifest.json`
- 外部パッケージ依存: なし（manifest の `packages = []`）
- 再現参照コミット: `3b06520d9704c09dcec03d609731910bcfa0edc9`
- 本稿作成時点で `Build completed successfully` を確認。

### 5.4 判定器実装の一致チェック（補助）

定理11 の証明により、閉形式判定式
\[
\max(min\_{req},min\_{api})\le \min(max\_{req},max\_{code})
\]
が存在検証と論理的に同値であることは Lean で機械検証済みである。
しかし、この判定式を Python などで**実装した際のバグ混入**可能性を排除するため、
合成テストケース（5 seed × 200,000 例と、ベースライン比較 20,000 例）において、全探索ベースライン（存在量化の直接検証）との結果一致を確認した (`paper/case-study/password_policy_benchmark.py`)。

**検証結果**:
- `result_mismatches = 0`（判定式実装とベースラインが完全一致）
- `witness_violation_count = 0`（構成証人が3層制約を満たす）

注: 本節の目的は計算速度測定ではなく、形式証明された判定器の**実装妥当性確認**である。
形式証明は判定式の論理的健全性を保証するが、その Python 実装がバグを含まないことまでは保証しない。
本検証により、実装バグが存在しないことを経験的に確認した。

### 5.5 実OSSアーティファクトを用いた外的妥当性評価（ケーススタディ本体）

本稿のケーススタディは、合成データ検証（§5.4）に加え、実OSS由来の仕様・API・実装アーティファクトから制約を抽出して評価する。

対象プロジェクト（抽出元）:
1. PostgreSQL  
   - 要求層: `max_identifier_length` 記述  
   - API層: SQL lexical 記述  
   - 実装層: `NAMEDATALEN` 定数（`pg_config_manual.h`）
2. zlib  
   - 要求層: `deflateInit` の圧縮レベル仕様  
   - API層: Python `zlib.compress` 引数仕様  
   - 実装層: `zlib.h` 定数（`Z_NO_COMPRESSION`, `Z_BEST_COMPRESSION`, `Z_DEFAULT_COMPRESSION`）
3. SQLite  
   - 要求層: `PRAGMA page_size` 仕様  
   - API層: file format 仕様  
   - 実装層: `sqliteLimit.h` 定数（`SQLITE_MAX_PAGE_SIZE`）

抽出・評価プロトコル:
1. 公式ドキュメント/公式ソースURLを取得  
2. 数値境界（lower/upper）を正規表現で抽出  
3. `requirement/api/code` の3層制約を構成  
4. 共通交差判定 `max(lower_i) ≤ min(upper_i)` で整合性判定

評価スクリプトと結果:
- スクリプト: `paper/case-study/real_projects/external_validation.py`
- 結果JSON: `paper/case-study/real_projects/external_validation_results.json`
- 実測（2026-02-14）:
  - `n_real_projects = 3`
  - `n_real_consistent = 3`
  - `n_real_contradictory = 0`

交差区間の内訳:
| Project | 交差下限 | 交差上限 | 判定 |
|---|---:|---:|---|
| PostgreSQL identifier length | 1 | 63 | consistent |
| zlib compression level | -1 | 9 | consistent |
| SQLite page size | 512 | 65536 | consistent |

さらに、各実プロジェクト制約に対して `requirement.lower = upper + 1` の変異を与える感度試験を行い、
`mutation_total = 3`, `mutation_detected = 3`（矛盾検出率100%）を確認した。

定理体系との対応:
- 定理3（`A(i) ⊆ D(i)` の持ち上げ）: 3プロジェクトの抽出制約は `requirement/api/code` の各層で domain を明示し、交差下限/上限が domain 内で閉じることを確認した。
- 定理4（`U0` 証人の領域妥当性）: `intersection_lower ≤ n ≤ intersection_upper` を満たす値 `n` が各層の許容条件を同時に満たす証人として構成できる。
- したがって §5.5 は「数値結果の提示」に留まらず、定理3/4が実アーティファクト抽出に接続可能であることの具体証拠となる。

この節がケーススタディの中心であり、§5.4 は実装移植バグの内部検証、§5.5 は実アーティファクトへの外的適用確認を担う。

## 6. 関連研究と位置づけ
本稿は既存理論を再発明するものではなく、UAD/f文脈における**最小コアの機械検証**を狙う。

| 枠組み | 部分性の一次表現 | 層ごと異型 | 層横断U0統合演算 | Lean機械検証 |
|---|---|---|---|---|
| 抽象解釈 / Galois | △（総写像前提が多い） | △ | × | × |
| Institution | △（言語意味論中心） | ○ | ×（一般満足移送） | × |
| TLA+/Alloy実務利用 | ×（モデル側で個別表現） | △ | × | △ |
| 本稿 | **○（`Option`で明示）** | **○（`carrier : I → Type`）** | **○（`U0`/`lifted`）** | **○** |

- 抽象解釈・Galois connection（Cousot & Cousot）:
  抽象解釈における Galois 接続 `(α, C, ⊑) ⊣ (γ, A, ≤)` では、
  抽象関数 `α : C → A` と具体化関数 `γ : A → C` が `∀c∀a, α(c) ≤ a ⇔ c ⊑ γ(a)` を満たす。
  本稿の枠組みと比較すると、`preimage` は形式的には `γ` (具体化方向) に対応し、逆像単調性（定理1）は Galois 接続の性質と整合する。
  **相違点として**、本稿の `proj : Ω → Option β_i` は `none` を含む部分性を一次的に表現する。
  この点は定理12で形式化し、未定義点が存在する場合に `preimage` が冪集合上の左随伴を持たないことを Lean で示した。
  よって標準的な総写像ベース随伴への埋め込みには追加条件（定義域制約や総定義化）が必要になる。
  この結果は U0 構成の健全性に直接関与する。すなわち「随伴があるはず」という暗黙仮定に頼らず、
  `proj_i(x)=some(y)` の存在証人を定理3/4で明示的に追跡する必要があることを理論的に裏付ける。
- Institution 理論（Goguen/Burstall）:
  言語間満足の移送と問題意識を共有するが、本稿は一般 institution 公理化ではなく、`Option` による部分性を明示した具体モデル。
  対応関係としては、`I` を署名インデックス、`lifted(i)` を層 `i` の root 充足集合と見なせる。  
  一方で institution の Satisfaction Condition に相当する写像整合は本稿では仮定 `R`（定理7）と `hcomm`（定理9）として個別に与えるため、一般公理化より具体的である。
- Refinement/traceability 系:
  層追加単調性（定理6）と層間伝播（定理7）を通じ、運用時の増分統合の基礎を与える。
- 形式手法実装（TLA+, Alloy, Lean）:
  これらを代替するのではなく、層横断の root 統合規則と抽出判定器の同値証明（定理11）に焦点を当てる。

## 7. 限界
本稿は以下を証明しない。

1. `proj_i` が実際の抽出器（AST解析器等）と意味的に同値であること（本稿はパスワード制約DSLまで）
2. UAD/f 全体の健全性・完全性
3. 外的妥当性の規模制約（本稿は3プロジェクトの数値境界制約に限定）

## 8. 今後
1. **抽出器クラスの一般化**: 定理11 はパスワード長制約に特化した判定器同値性を証明した。
   今後、抽出器の型 `Extractor : Type` をパラメータ化し、`proj` との意味保存を満たす抽出器クラス全般に対する健全性・完全性の一般定理を追加する。
2. **外的妥当性評価の拡張**: 現在の3プロジェクト評価を、プロジェクト数・制約型（列挙/構造制約）・時系列差分（版間矛盾）へ拡張する。
3. `proj` の合成則（`f_{0j} = g_{ij} ∘ f_{0i}` 型仮定）を導入し、層間保存定理を拡張する。
4. 実抽出器（Rust AST / OpenAPI / 契約注釈）に対する意味保存証明を追加する。
5. 公開アーカイブ（commit hash/DOI）付きで再現パッケージを整備する。

## 9. 結論
UAD/f の `U,D,A,f` を型付きで明示し、`f^{-1}` を部分射影から定義することで、`U0` 構成則の曖昧性を除去した。  
その上で、領域整合・上限性・層追加単調性・層間合成・抽出適合性を Lean4 で機械検証し、`U0` を単なる記法ではなく、検証可能な統合演算として位置づけた。

本稿の科学的増分は、既知集合論事実の再掲ではなく、**部分性を含む型付き多層統合モデルにおける不足仮定（随伴の非成立条件を含む）を機械的に可視化した点**にある。
加えて、実OSSアーティファクト3件に対するケーススタディで、理論定義が実データ抽出に接続可能であることを示した。

---
### 参考文献（簡易）
- P. Cousot and R. Cousot, “Abstract Interpretation,” POPL 1977.  
- J. A. Goguen and R. M. Burstall, “Introducing Institutions,” 1984.  
- L. Lamport, *Specifying Systems* (TLA+), 2002.  
