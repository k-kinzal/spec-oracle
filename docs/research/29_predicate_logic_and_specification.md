# 述語論理と仕様記述

## 1. 述語論理とは

述語論理（Predicate Logic）は、命題論理を拡張した論理体系であり、個体の性質や個体間の関係を表現する述語（predicate）と、「すべての」「存在する」といった量化子（quantifier）を導入することで、より豊かな表現力を持つ。

### 1.1 基本概念

- **述語（Predicate）**: 個体の性質を表す述部。例：S(x) = 「xは学生である」、Y(x,y) = 「xはyより若い」
- **量化子（Quantifier）**: 変数の範囲を指定する記号
  - **全称量化子（Universal Quantifier）**: ∀（すべてのxについて）
  - **存在量化子（Existential Quantifier）**: ∃（あるxが存在して）
- **論理演算子**: ¬（否定）、∧（論理積）、∨（論理和）、→（含意）、≡（同値）
- **個体変数**: xやyなど、論理式の対象となる個体を表す変数

### 1.2 形式体系としての特徴

述語論理の形式体系は、以下の要素で構成される：

- **項（Terms）**: 変数、定数、関数の適用
- **論理式（Formulas）**: 原子論理式と論理演算子・量化子による複合論理式
- **推論規則**: 妥当な結論を導出する規則
- **公理**: 体系の基礎となる論理式

## 2. 一階述語論理（First-Order Logic）

### 2.1 定義と特徴

一階述語論理（First-Order Logic, FOL）は、個体に対してのみ量化を許す述語論理である。命題論理を拡張したものであり、個体の性質を述語として扱う。

#### 基本的性質
- **量化の対象**: 個体のみ（述語や関数には量化しない）
- **表現力**: 数学のほぼすべての分野を形式化するのに十分な表現力
- **標準集合論**: 現代の標準的な集合論の公理系ZFCは一階述語論理で形式化されている
- **計算可能性**: 推論手続きが存在し、自動定理証明が可能

### 2.2 量化子による仕様表現

#### 全称量化（Universal Quantification）
- **記法**: ∀x P(x)
- **意味**: 論議領域のすべてのxについてP(x)が真である
- **典型的な文脈**: ∀x (P(x) → Q(x))
  - 「P(x)を満たすすべてのxはQ(x)も満たす」

**仕様記述での例**:
```
∀x (Employee(x) → HasID(x))
「すべての従業員はIDを持つ」

∀x ∀y ((Account(x) ∧ Account(y) ∧ x ≠ y) → ID(x) ≠ ID(y))
「すべての口座は異なるIDを持つ」

∀x (Stack(x) → (Empty(x) ↔ Size(x) = 0))
「すべてのスタックについて、空であることとサイズが0であることは同値」
```

#### 存在量化（Existential Quantification）
- **記法**: ∃x P(x)
- **意味**: 論議領域の少なくとも1つのxについてP(x)が真である
- **典型的な文脈**: ∃x (P(x) ∧ Q(x))
  - 「P(x)を満たすあるxがQ(x)も満たす」

**仕様記述での例**:
```
∃x (Admin(x) ∧ Active(x))
「アクティブな管理者が存在する」

∃!x Root(x)
「ルートノードはただ1つ存在する」（一意存在量化）

∀x (User(x) → ∃y (Session(y) ∧ BelongsTo(y, x)))
「すべてのユーザーは少なくとも1つのセッションを持つ」
```

### 2.3 一階述語論理の重要性

#### 数学的基盤
- 数学のほぼすべての分野を形式化できる十分な表現力
- 集合論、代数、解析などの基礎理論の記述
- 数学的定理の厳密な証明

#### 計算機科学での応用
- **人工知能**: 知識表現と推論
- **データベース**: リレーショナルモデルの理論的基盤（E.F. Coddがリレーショナル論理として適用）
- **形式手法**: プログラム検証、仕様記述
- **自動定理証明**: 定理証明器の理論的基盤

## 3. 高階論理（Higher-Order Logic）

### 3.1 二階論理（Second-Order Logic）

二階論理は、一階述語論理を拡張し、述語や関数に対しても量化を許す論理体系である。

#### 特徴
- **量化の対象**: 個体に加えて、述語（性質）や関数
- **表現力の向上**: 一階論理では表現できない概念を記述可能
- **決定不能性**: 一般的な二階論理は決定不能（decidable ではない）

#### 表現力の例

**数学的帰納法の公理**:
```
∀P ((P(0) ∧ ∀n (P(n) → P(n+1))) → ∀n P(n))
```
これは述語Pに対する量化を含み、一階論理では表現できない。

**完全性の定義**:
実数の完全性（アルキメデス完全順序体の一意性）を二階論理で表現できるが、一階論理では表現不可能。この結果、二階実数論はただ1つのモデル（実数）しか持たない。

### 3.2 三階論理と高階論理

- **三階論理**: 集合に対しても量化する
- **n階論理**: さらに高い階層への量化
- **高階論理**: 一階、二階、三階、...、n階論理の和集合

#### 表現力と決定可能性のトレードオフ

| 論理体系 | 表現力 | 決定可能性 | 完全性 |
|---------|-------|-----------|-------|
| 命題論理 | 最小 | 決定可能（NP完全） | 完全 |
| 一階論理 | 中程度 | 半決定可能 | 完全（Gödelの完全性定理） |
| 二階論理 | 高い | 決定不能 | 不完全（標準意味論） |
| 高階論理 | 最大 | 決定不能 | 不完全 |

### 3.3 HOL（Higher-Order Logic）定理証明

#### HOLシステムの概要

HOLは、高階論理を用いた対話的定理証明システムのファミリーを指す。

**特徴**:
- **単純型付きラムダ計算**: すべての項は変数、定数、適用、抽象化
- **多相性**: Hindley-Milner型検査アルゴリズムによる型多相
- **LCFアプローチ**: 証明された定理の抽象データ型を定義し、推論規則に対応する関数でのみ新しいオブジェクトを作成

#### 応用分野
- **ハードウェア設計と検証**: 回路の正当性検証
- **セキュリティ推論**: セキュリティプロトコルの形式的検証
- **リアルタイムシステム**: タイミング制約を含む証明
- **HDL意味論**: ハードウェア記述言語の形式的意味論
- **コンパイラ検証**: コンパイラの正当性証明
- **プログラム正当性**: プログラムの仕様に対する証明
- **並行性モデリング**: 並行システムの形式的記述
- **プログラム詳細化**: 仕様から実装への段階的詳細化

## 4. 命題論理の限界と述語論理の表現力

### 4.1 命題論理の限界

命題論理（Propositional Logic）は真か偽のいずれかである単純な宣言文（原子命題）しか表現できない。

#### 主な限界

1. **量化の欠如**: 「すべて」や「存在する」といった量化を表現できない
2. **関係の表現不可**: 2つ以上の実体間の関係を適切に記述できない
3. **個体の性質**: 個体とその性質を区別して扱えない
4. **一般化の困難**: 対象の集合やカテゴリに対する量化ができない
5. **粗さ**: オブジェクトの性質を容易に記述するための構造が欠けている

#### 具体例

**表現できない文**:
- 「すべての人間は死すべきものである」
- 「ある素数は偶数である」
- 「xはyより大きい」

これらは個体、述語、量化子を必要とし、命題論理では適切に表現できない。

### 4.2 述語論理による克服

述語論理は、変数、量化子、述語、関数を導入することで、命題論理の限界を克服する。

#### 表現力の向上

**例1**: 一般化の表現
```
命題論理: P1 ∧ P2 ∧ P3 ∧ ... （個別に列挙）
述語論理: ∀x P(x) （一般化された表現）
```

**例2**: 関係の表現
```
命題論理: 表現不可
述語論理: ∀x ∀y (Parent(x, y) → Ancestor(x, y))
```

**例3**: 存在の主張
```
命題論理: 表現不可
述語論理: ∃x (Prime(x) ∧ Even(x))
```

### 4.3 表現力と計算複雑性のトレードオフ

より表現力の高い論理は、より高い計算複雑性を持つ傾向がある：

- **命題論理**: 計算複雑性が低い（NP完全）、推論タスクが効率的
- **一階述語論理**: より高い複雑性だが、実用的な自動推論が可能
- **高階論理**: 最高の表現力だが、一般的に決定不能

## 5. Horn節と論理プログラミング

### 5.1 Horn節の定義

Horn節（Horn Clause）は、数理論理学と論理プログラミングにおいて、特定の規則的な形式を持つ論理式である。

#### 形式的定義
- **論理式**: 選言節（リテラルの選言）
- **制約**: 高々1つの肯定的（否定されていない）リテラルを持つ
- **名称の由来**: 論理学者Alfred Hornが1951年にその重要性を指摘

#### Horn節の種類

1. **確定節（Definite Clause）**: ちょうど1つの肯定的リテラルを持つ
   - 例: `P ← Q ∧ R`（QとRが真ならPが真）

2. **単位節（Unit Clause）**: 否定的リテラルを持たない確定節
   - 例: `P`（Pは真）

3. **事実（Fact）**: 変数を含まない単位節
   - 例: `Human(Socrates)`

4. **ゴール節（Goal Clause）**: 肯定的リテラルを持たない
   - 例: `← Q ∧ R`（QとRが真であることを示せ）

### 5.2 Prologと論理プログラミング

Prolog（PROgrammation en LOGique）は、1972年にAlain ColmerauerとPhilippe Rousselによって発明された論理プログラミング言語である。

#### 基本構造
- **プログラム**: 頭付きHorn節（確定節）の集合で構成されるデータベース
- **クエリ**: ユーザーが供給する頭なしHorn節（ゴール節）
- **実行**: クエリに対する証明の探索

#### Horn節の構文
- **頭部（Head）**: 左辺、0または1つの述語を持つ
- **本体（Body）**: 右辺、述語のリストを持つ

**例**:
```prolog
% 事実
parent(tom, bob).
parent(tom, liz).

% 規則
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

% クエリ
?- ancestor(tom, Who).
```

### 5.3 Horn節の性質と応用

#### 重要な性質

1. **閉包性**: 2つのHorn節の融合項（resolvent）もHorn節である
2. **効率的推論**: ゴール節と確定節の融合項はゴール節
3. **チューリング完全**: Horn節論理は万能チューリングマシンと計算能力が等価

#### 意味論

**宣言的意味論（Model-Theoretic Semantics）**:
- Horn節の集合に対するモデル理論的な意味
- 論理式の真偽値に基づく

**手続き的意味論（Procedural Semantics）**:
- SLD融合（Linear resolution with Selection function for Definite clauses）による定義
- 健全（sound）かつ完全（complete）な推論手続き
- 宣言的意味論と手続き的意味論が一致

#### 応用分野

- **自動定理証明**: 一階融合による自動証明
- **知識表現**: 知識ベースシステム
- **データベースクエリ**: リレーショナルデータベースの結合クエリに類似
- **エキスパートシステム**: ルールベース推論
- **意味Web**: ルール言語（W3C RIF Horn Logic）

## 6. 記述論理（Description Logic）と仕様

### 6.1 記述論理の概要

記述論理（Description Logic, DL）は、知識表現のための形式言語のファミリーであり、命題論理より表現力が高いが、一階述語論理より表現力が低い。

#### 基本的特徴
- **決定可能性**: 一階論理とは異なり、コア推論問題は通常決定可能
- **効率的決定手続き**: 実装された効率的な決定手続きが存在
- **意味的基盤**: 述語論理に基づくが、実用的モデリングと良好な計算特性を持つように言語が形成されている

### 6.2 DLの構成要素

#### 基本概念
- **概念（Concepts）**: クラス、単項述語として解釈
- **役割（Roles）**: プロパティまたは関係、二項関係として解釈
- **個体（Individuals）**: インスタンス

#### 知識ベースの構造

**TBox（Terminological Box）**:
- 用語（概念と役割の定義）を記述
- オントロジーの形で用語体系を表現
- 例: `Parent ⊑ Person`（親は人である）

**ABox（Assertional Box）**:
- オントロジーの用語を使用した個体に関する主張
- 例: `Parent(john)`（johnは親である）

### 6.3 オントロジーとセマンティックWebへの応用

#### OWL（Web Ontology Language）

記述論理は、オントロジーおよびセマンティックWeb、特にWeb Ontology Language（OWL）に論理的形式を提供することで特に重要である。

**発展の歴史**:
- **DAML+OIL DL**: W3C Web Ontology Working Groupへの提出
- **OWL 1.0（2004年）**: W3Cの推奨として完成
- **OWL 2（2009年）**: 記述論理SROIQ(D)に基づく

#### OWL DLの特徴
- **最大の表現力**: 計算完全性と決定可能性を保持しながら最大の表現力をサポート
- **DLサポート**: 名前の「DL」は記述論理の能力をサポートすることを示す

### 6.4 記述論理の応用分野

#### 人工知能
- アプリケーションドメインの関連概念を記述し推論
- 用語的知識の形式化

#### セマンティックWeb
- オントロジー言語の理論的基盤
- 知識の共有と再利用

#### データベース
- 概念的データモデリング
- クエリ最適化

## 7. 仕様における論理式の役割

### 7.1 不変条件（Invariants）

不変条件は、システムのすべての状態で常に真でなければならない性質を記述する。

**一階述語論理での表現**:
```
∀s ∈ SystemStates . Invariant(s)
```

**例**:
```
-- バンキングシステム
∀a ∈ Accounts . balance(a) ≥ 0

-- データ構造
∀t ∈ Trees . (LeftChild(t) ≠ null → Value(LeftChild(t)) < Value(t))
```

### 7.2 事前条件と事後条件（Pre/Post Conditions）

操作の仕様を論理式で記述する。

**形式**:
```
{P} operation {Q}
```
- P: 事前条件（precondition）
- Q: 事後条件（postcondition）

**例**:
```
{balance(account) ≥ amount ∧ amount > 0}
withdraw(account, amount)
{balance(account) = balance@pre(account) - amount}
```

### 7.3 安全性（Safety）と活性（Liveness）

#### 安全性仕様
「悪いことが起こらない」ことを保証。

**例**:
```
∀t ∈ Time . ¬(Resource1InUse(t) ∧ Resource2InUse(t))
「デッドロックが発生しない」
```

#### 活性仕様
「良いことがいつか起こる」ことを保証。時相論理で記述されることが多い。

**例**:
```
∀request . ∃response . Happens(response, request)
「すべてのリクエストは最終的に応答される」
```

## 8. 形式仕様記述言語における述語論理

### 8.1 Z記法（Z Notation）

Z記法は、述語論理と集合論に基づく形式仕様記述言語である。

#### 理論的基盤
- **集合論**: 標準的な集合演算、集合内包記法、直積、冪集合
- **一階述語論理**: 論理演算と量化子を含む
- **型システム**: すべての式に型が付けられ、素朴集合論のパラドックスを回避

#### スキーマ記法

Z記法の特徴は「スキーマボックス」による構造化された仕様記述である。

**例**:
```
BankAccount
----------------
balance: ℕ
accountID: AccountID
----------------
balance ≥ 0
```

#### 操作の仕様

**例**:
```
Withdraw
ΔBankAccount
amount?: ℕ
----------------
amount? > 0
balance ≥ amount?
balance' = balance - amount?
```

### 8.2 VDM（Vienna Development Method）

VDMも述語論理と集合論に基づくが、Zとはいくつかの違いがある。

#### Zとの比較

**類似点**:
- モデルベース仕様記述技法
- 数学記法の大部分を共有
- 集合論と述語論理に基づく

**相違点**:
- **事前条件の明示**: VDMでは事前条件を明示的に分離
  - VDM: `pre-condition` と `post-condition` を分離
  - Z: 述語内で結合
- **読み書きの明示**: VDMでは操作がどのコンポーネントを読み書きするか明示
- **構文の違い**: 記法の詳細が異なる

#### 述語論理の使用

VDMでは、事前条件（before状態のみを含む）と事後条件（after状態も含む）を明示的に分離する：

```
withdraw(amount: ℕ)
ext wr balance: ℕ
pre amount > 0 ∧ balance ≥ amount
post balance = balance~ - amount
```

### 8.3 その他の形式仕様記述言語

#### Alloy
- **リレーショナルロジック**: 一階論理にリレーション代数を組み合わせ
- **制約ベース**: 制約を述語論理で記述
- **自動解析**: SAT/SMTソルバーによる自動検証

#### TLA+
- **時相論理**: 一階論理に時相演算子を追加
- **状態遷移**: 述語論理で状態と遷移を記述
- **不変条件**: 論理式で安全性を指定

## 9. 論理的推論と仕様検証

### 9.1 融合原理（Resolution）

融合原理は、一階述語論理における推論規則であり、完全な反駁による定理証明技法である。

#### 基本原理

**融合規則**:
```
(α ∨ β) ∧ (¬β ∨ γ) ⊢ (α ∨ γ)
```
「αまたはβ」を知っていて、「βでないまたはγ」を知っているなら、「αまたはγ」を結論できる。

#### 自動定理証明への応用

1. **証明する式を否定**: 矛盾を導くことで元の式を証明
2. **節形式に変換**: 連言標準形（CNF）に変換
3. **融合規則の適用**: 空節（矛盾）が導出されるまで繰り返し適用
4. **反駁完全**: 矛盾が導出されれば元の式は真

### 9.2 定理証明器による検証

#### 一階定理証明器
- **Vampire**: 高性能な自動定理証明器
- **E**: 等式推論に特化
- **SPASS**: 多ソート一階論理
- **Prover9**: William McCuneによる古典的な証明器

#### 高階定理証明器
- **Isabelle/HOL**: 対話的定理証明器
- **Coq**: 依存型理論に基づく
- **HOL4**: Standard MLで実装
- **HOL Light**: 小さく信頼できるカーネル

### 9.3 仕様検証の手法

#### モデル検査（Model Checking）
- 有限状態システムに対する自動検証
- 時相論理式で仕様を記述
- 状態空間の網羅的探索

#### 定理証明（Theorem Proving）
- 数学的証明による検証
- 無限状態システムも扱える
- 人間の介入が必要（対話的）

#### SMTソルバー（SAT Modulo Theories）
- 一階論理と理論（算術、配列など）の組み合わせ
- 充足可能性の自動判定
- 制約解決による検証

## 10. まとめ

### 10.1 述語論理の重要性

述語論理は、仕様記述の基盤として極めて重要な役割を果たす：

#### 理論的基盤
- 数学のほぼすべての分野を形式化できる表現力
- 集合論、代数、解析の基礎
- 計算機科学の理論的基盤

#### 実用的応用
- 形式仕様記述言語（Z、VDM、Alloyなど）の基礎
- 自動定理証明の理論的枠組み
- 知識表現と推論の基盤
- データベース理論の基礎

### 10.2 表現力の階層

| 論理体系 | 量化の対象 | 表現力 | 決定可能性 | 主な用途 |
|---------|-----------|-------|-----------|---------|
| 命題論理 | なし | 限定的 | 決定可能 | ハードウェア検証、SAT |
| 一階述語論理 | 個体 | 高い | 半決定可能 | 形式仕様、定理証明 |
| Horn節論理 | 個体（制限付き） | 中程度 | 決定可能 | 論理プログラミング |
| 記述論理 | 個体（制限付き） | 中程度 | 決定可能 | オントロジー、Semantic Web |
| 二階論理 | 個体+述語 | 非常に高い | 決定不能 | 数学的定理、帰納法 |
| 高階論理 | すべて | 最大 | 決定不能 | 対話的定理証明 |

### 10.3 適用場面の選択

#### 一階述語論理を使うべき場面
- 自動定理証明が重要
- 標準的な形式仕様記述
- データベース理論
- 知識表現と推論

#### Horn節を使うべき場面
- 論理プログラミング
- ルールベースシステム
- 効率的な推論が必要
- 知識ベースシステム

#### 記述論理を使うべき場面
- オントロジー工学
- セマンティックWeb
- 決定可能性が重要
- 知識の共有と再利用

#### 高階論理を使うべき場面
- 数学的帰納法が必要
- ソフトウェア・ハードウェアの完全検証
- プログラミング言語の意味論
- 対話的証明が許容できる

### 10.4 現代の発展

#### SMTソルバーの台頭
- 一階論理と理論の組み合わせ
- 効率的な自動推論
- プログラム検証への応用

#### 依存型と証明支援
- 型システムと論理の統合
- プログラムと証明の一体化
- Coq、Agda、Idrisなど

#### AI時代の知識表現
- 記述論理によるオントロジー
- ニューラルシンボリック統合
- 説明可能なAIへの応用

### 10.5 今後の課題

#### スケーラビリティ
- 大規模システムの仕様記述
- 自動推論の効率化
- モジュール化と合成

#### 使いやすさ
- 学習曲線の緩和
- ツールの改善
- エラーメッセージの向上

#### 実用化
- 産業界での普及
- 教育の充実
- ベストプラクティスの確立

述語論理は、形式仕様記述の基盤として不可欠であり、その理解は高品質なシステム開発に欠かせない。適切な論理体系を選択し、その表現力と決定可能性のトレードオフを理解することが、効果的な仕様記述の鍵となる。

## 参考文献・出典

### 述語論理の基礎
- [一階述語論理 - Wikipedia](https://ja.wikipedia.org/wiki/%E4%B8%80%E9%9A%8E%E8%BF%B0%E8%AA%9E%E8%AB%96%E7%90%86)
- [述語論理 - Wikipedia](https://ja.wikipedia.org/wiki/%E8%BF%B0%E8%AA%9E%E8%AB%96%E7%90%86)
- [First-order logic - Wikipedia](https://en.wikipedia.org/wiki/First-order_logic)
- [Predicate Logic | 実用的な数学を](https://www.practmath.com/predicate-logic/)

### 一階論理と仕様
- [First-Order Logic in Artificial Intelligence - GeeksforGeeks](https://www.geeksforgeeks.org/artificial-intelligence/first-order-logic-in-artificial-intelligence/)
- [Syntax and Semantics of First-Order Logic in AI - GeeksforGeeks](https://www.geeksforgeeks.org/artificial-intelligence/syntax-and-semantics-of-first-order-logic-in-ai/)
- [Part I First-order Logic](https://builds.openlogicproject.org/content/first-order-logic/first-order-logic.pdf)

### 高階論理
- [Higher-order logic - Wikipedia](https://en.wikipedia.org/wiki/Higher-order_logic)
- [Second-order and Higher-order Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-higher-order/)
- [HOL (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/HOL_(proof_assistant))
- [HOL Interactive Theorem Prover](https://hol-theorem-prover.org/)
- [The HOL Theorem Prover for Higher Order Logic](https://www.cs.ox.ac.uk/tom.melham/res/hol.html)

### 命題論理と述語論理の比較
- [Limitations of Propositional Logic – Theoretical Insights](https://theoreticalinsights.com/2025/03/17/limitations-of-propositional-logic/)
- [Difference between Propositional and First-Order Logic - GeeksforGeeks](https://www.geeksforgeeks.org/difference-between-propositional-and-first-order-logic-and-how-are-they-used-in-knowledge-representation/)
- [Limitations and extensions of propositional logic | Fiveable](https://fiveable.me/formal-logic-ii/unit-1/limitations-extensions-propositional-logic/study-guide/N11I8T0f7BKb7nAm)

### Horn節と論理プログラミング
- [Horn clause - Wikipedia](https://en.wikipedia.org/wiki/Horn_clause)
- [Horn Clause Logic](https://www-users.york.ac.uk/~sjh1/courses/L334css/complete/complete2/node5.html)
- [Horn Logic - W3C RIF-WG Wiki](https://www.w3.org/2005/rules/wg/wiki/Horn_Logic)
- [Prolog Programming Basics](https://athena.ecs.csus.edu/~mei/logicp/prolog.html)

### 記述論理
- [Description logic - Wikipedia](https://en.wikipedia.org/wiki/Description_logic)
- [Description Logics - Introduction to ontologies and semantic web](https://www.obitko.com/tutorials/ontologies-semantic-web/description-logics.html)
- [Web Ontology Language - Wikipedia](https://en.wikipedia.org/wiki/Web_Ontology_Language)
- [Description Logics - an overview | ScienceDirect](https://www.sciencedirect.com/topics/computer-science/description-logics)

### 論理的推論と定理証明
- [Resolution (logic) - Wikipedia](https://en.wikipedia.org/wiki/Resolution_(logic))
- [Resolution Algorithm in Artificial Intelligence - GeeksforGeeks](https://www.geeksforgeeks.org/artificial-intelligence/resolution-algorithm-in-artificial-intelligence/)
- [Chapter 2 Resolution Theorem Proving](https://lawrencecpaulson.github.io/papers/bachmair-hbar-resolution.pdf)

### Z記法とVDM
- [Z notation - Wikipedia](https://en.wikipedia.org/wiki/Z_notation)
- [Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)
- [Analysis of Three Formal Methods-Z, B and VDM](https://www.ijert.org/research/analysis-of-three-formal-methods-z-b-and-vdm-IJERTV1IS4227.pdf)
- [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)

### 量化子
- [Universal quantification - Wikipedia](https://en.wikipedia.org/wiki/Universal_quantification)
- [Existential quantification - Wikipedia](https://en.wikipedia.org/wiki/Existential_quantification)
- [Quantifier (logic) - Wikipedia](https://en.wikipedia.org/wiki/Quantifier_(logic))
- [Universal and Existential Quantifiers | Fiveable](https://fiveable.me/formal-logic-i/unit-9/universal-existential-quantifiers/study-guide/Hg0xklyxHiSGu3Jq)

### 決定可能性
- [Decidability (logic) - Wikipedia](https://en.wikipedia.org/wiki/Decidability_(logic))
- [Second-order logic - Wikipedia](https://en.wikipedia.org/wiki/Second-order_logic)
