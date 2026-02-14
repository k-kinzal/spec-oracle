# 操作的意味論（Operational Semantics）

## 概要

操作的意味論（Operational Semantics）は、プログラミング言語の形式的意味論を与える主要な手法の一つである。プログラムの意味を、その実行過程における計算ステップのシーケンスとして記述する。操作的意味論は、プログラムが抽象機械上でどのように実行されるかを数学的に厳密に定義することで、プログラムの振る舞いを形式化する。

操作的意味論は、表示的意味論（Denotational Semantics）や公理的意味論（Axiomatic Semantics）と並ぶ、プログラム意味論の三大アプローチの一つである。直感的に理解しやすく、インタープリタの実装と密接に関連するため、プログラミング言語の設計者や実装者にとって実用的な手法となっている。

## 1. 操作的意味論の基本概念

### 1.1 意味論の役割

プログラミング言語の意味論は、プログラムに数学的な意味を与えるための形式的な枠組みである。意味論が必要とされる理由は以下の通り:

- プログラムの振る舞いを厳密に定義する
- 言語仕様の曖昧性を排除する
- プログラムの正当性を形式的に証明する基盤を提供する
- 言語実装（コンパイラ・インタープリタ）の正しさを検証する
- 言語の設計上の選択肢を比較・評価する

### 1.2 操作的意味論の基本思想

操作的意味論は、プログラムの意味を「どのように計算されるか」という観点から定義する。具体的には:

- プログラムの実行を、状態の遷移のシーケンスとしてモデル化する
- 各計算ステップを遷移規則（transition rule）として形式化する
- 抽象機械（abstract machine）または遷移システム（transition system）上でのプログラムの実行を記述する

操作的意味論はインタープリタに対応すると考えることができるが、ここでの「インタープリタ」は実際のコンピュータ実装ではなく、数学的に形式化された抽象的なインタープリタである。

### 1.3 抽象機械との関係

操作的意味論は、しばしば抽象機械を用いて定義される。抽象機械は:

- プログラムの状態（メモリ、レジスタ、スタック等）を抽象的に表現する
- 状態遷移規則によって、各命令の効果を定義する
- 実際のハードウェアから離れた、数学的に扱いやすいレベルで定義される

代表的な抽象機械には、SECD機械、CEK機械、CESK機械などがある。

## 2. 構造的操作的意味論（Structural Operational Semantics: SOS）

### 2.1 SOSの歴史と定義

構造的操作的意味論（SOS）は、Gordon Plotkin（ゴードン・プロトキン）によって1981年に導入された体系的な操作的意味論の手法である。PlotkinのAarhus報告書は、計算機科学において最も引用される技術報告書の一つとなっており、CiteSeerによると1000回以上引用されている。

**SOSの基本原則:**

- **構文指向性（Syntax-directed）**: 意味規則はプログラムの構文構造に従って定義される
- **構造的再帰性**: プログラムの意味は、その構成要素の意味から構造的に（原始再帰的に）定義される
- **形式的推論規則**: 遷移を推論規則の形で記述する

Plotkin自身が述べているように、「規則は構文指向であるべきである。これが「A Structural Approach to Operational Semantics」というタイトルに反映されている。一部の人が考えたような『構造化された（structured）』ではなく、『構造的（structural）』である」。

### 2.2 SOSの形式

SOSでは、プログラムの振る舞いをラベル付き遷移システム（Labelled Transition System: LTS）として定義する。LTSは以下の三つ組である:

```
⟨X, A, →⟩
```

- **X**: 状態（processes）の集合
- **A**: ラベル（actions）の集合
- **→**: 遷移関係（→ ⊆ X × A × X）

遷移関係は、推論規則の形で定義される:

```
前提₁  前提₂  ...  前提ₙ
―――――――――――――――――――――
      結論
```

各規則は、「前提が成り立てば、結論が成り立つ」ことを表現する。

### 2.3 SOSの例：簡単な算術式

算術式の評価を例に取る。構文は以下の通り:

```
e ::= n           (整数)
    | e₁ + e₂     (加算)
    | e₁ × e₂     (乗算)
```

評価関係 `e ⇓ n` は「式eが値nに評価される」ことを意味し、以下の推論規則で定義される:

```
[Num]
―――――
n ⇓ n


e₁ ⇓ n₁    e₂ ⇓ n₂    n = n₁ + n₂
[Add] ――――――――――――――――――――――――――
           e₁ + e₂ ⇓ n


e₁ ⇓ n₁    e₂ ⇓ n₂    n = n₁ × n₂
[Mul] ――――――――――――――――――――――――――
           e₁ × e₂ ⇓ n
```

これらの規則は構文指向的であり、各構文要素（数値、加算、乗算）に対して一つの規則が対応している。

## 3. 大ステップ意味論と小ステップ意味論

操作的意味論には、主に二つのスタイルがある。

### 3.1 大ステップ意味論（Big-Step Semantics / Natural Semantics）

**概要:**

大ステップ意味論は、Gilles Kahnによって「自然意味論（Natural Semantics）」という名前で導入された。Mini-MLという純粋なML方言を記述する際に提示された手法である。

**特徴:**

- プログラムの実行全体の結果を直接的に記述する
- 中間的な計算ステップを省略し、最終結果のみに焦点を当てる
- 評価関係の形式: `e ⇓ v` （式eが値vに評価される）
- 関係意味論（Relational Semantics）や評価意味論（Evaluation Semantics）とも呼ばれる

**メリット:**

- 推論規則がシンプルで、規則の数が少なくて済む
- 効率的なインタープリタの実装と直接的に対応する
- 直感的で理解しやすい（Kahnが「自然」と呼んだ理由）

**デメリット:**

- 非停止（発散）する計算に対して推論木が存在しない
- そのため、非停止性に関する性質を述べたり証明したりすることが困難
- 計算の中間状態についての情報が失われる

**例:**

前述の算術式の評価規則は、大ステップ意味論の例である。

### 3.2 小ステップ意味論（Small-Step Semantics / Structural Operational Semantics）

**概要:**

小ステップ意味論は、計算を一ステップずつ記述する手法である。構造的操作的意味論（SOS）という用語は、しばしば小ステップ意味論と同義で用いられる。

**特徴:**

- 計算の各ステップを明示的に記述する
- 遷移関係の形式: `e → e'` （式eが一ステップで式e'に遷移する）
- 計算の全体は、遷移の列として表現される: `e₀ → e₁ → e₂ → ... → eₙ`

**メリット:**

- 計算の各中間状態を追跡できる
- 非停止性を含むあらゆる計算についての性質を記述・証明できる
- 並行性やインターリービングをモデル化しやすい

**デメリット:**

- 推論規則の数が多くなる傾向がある
- 大ステップに比べて記述が冗長になる場合がある

**例:**

算術式の小ステップ意味論の例:

```
       e₁ → e₁'
[Add-L] ――――――――――――
       e₁ + e₂ → e₁' + e₂


       e₂ → e₂'
[Add-R] ――――――――――――
       n + e₂ → n + e₂'


[Add-C] ――――――――――――――――――
       n₁ + n₂ → n₃    (ここで n₃ = n₁ + n₂)
```

### 3.3 統合的アプローチ

近年の研究では、大ステップと小ステップの利点を統合する手法も提案されている。例えば、「Big-Stop Semantics」は、小ステップ意味論を大ステップの判断の中に組み込む試みである。

## 4. ラベル付き遷移システム（Labelled Transition System: LTS）

### 4.1 LTSの定義

ラベル付き遷移システムは、並行システムや反応的システムの操作的意味論を記述するための標準的なモデルである。

**構成要素:**

```
LTS = ⟨S, Act, T⟩
```

- **S**: 状態の集合
- **Act**: アクション（ラベル）の集合
- **T**: 遷移関係（T ⊆ S × Act × S）

遷移 `(s, α, s') ∈ T` は、しばしば `s →ᵅ s'` と表記される。これは「状態sがアクションαを実行して状態s'に遷移する」ことを意味する。

### 4.2 ラベルの意味

ラベルは、言語や目的に応じて異なる意味を持つ:

- 期待される入力
- 遷移を引き起こすための条件
- 遷移中に実行されるアクション
- 通信チャネルとメッセージ

### 4.3 LTSと並行性

並行プログラムの意味論モデルとして、LTSは広く用いられている。特に:

- プロセス代数（Process Algebra）の意味論
- CCS（Calculus of Communicating Systems）、CSP（Communicating Sequential Processes）、ACP（Algebra of Communicating Processes）などの形式手法

**真の並行性への拡張:**

標準的なLTSはインターリービング意味論に基づいているが、真の並行性（True Concurrency）をモデル化するために、Pomset LTS（PLTS）が提案されている。PLTSでは、遷移が単一のアクションではなく、部分順序付き多重集合（Pomset）のアクションを実行する。

### 4.4 双模倣（Bisimulation）

**定義:**

双模倣は、LTSにおける状態間の等価関係を定義する概念である。二つの状態が双模倣等価であるとは、それらが互いに相手の遷移をシミュレートできることを意味する。

**性質:**

- 反射的（reflexive）
- 対称的（symmetric）
- 推移的（transitive）

したがって、双模倣等価は等価関係である。

**プロセス代数における役割:**

双模倣等価は、CCS、CSP、ACPなどのプロセス代数において合同関係（congruence）となる。これにより、プログラムの等価性を形式的に証明できる。

**ゲーム理論的解釈:**

双模倣は、攻撃者（attacker）と防御者（defender）の間のゲームとして解釈できる。防御者が勝利戦略を持つ場合に限り、二つのシステムは双模倣等価である。

## 5. 抽象機械による操作的意味論

### 5.1 SECD機械

**概要:**

SECD機械は、Peter J. Landinによって1964年に論文「The Mechanical Evaluation of Expressions」で導入された影響力のある抽象機械である。関数型プログラミング言語のコンパイルターゲットとして設計され、ラムダ計算を実用的なプログラミングパラダイムとして解釈する最初の形式的モデルを提供した。

**名前の由来:**

SECDは、機械の内部レジスタの頭文字:

- **S (Stack)**: スタック - 計算の中間結果を保持
- **E (Environment)**: 環境 - 変数の値をバインド
- **C (Control)**: 制御 - 実行すべきコードのリスト
- **D (Dump)**: ダンプ - 関数呼び出しのコールスタック

**評価戦略:**

SECD機械は、適用的順序評価（applicative-order evaluation）を採用している。これは、関数適用の際に引数を完全に評価してから演算子を適用する戦略である。この選択は:

- 早期の適用的言語の意味論と一致
- 評価されていない引数による非停止のリスクを低減
- ベータ簡約ステップの実装を正規順序戦略に比べて簡単にする

**意義:**

SECD機械は、ラムダ計算の操作的意味論の明確で小さな記述を提供する。高階関数と字句スコープを持つ言語の実装モデルとして、後の多くの抽象機械の基礎となった。

### 5.2 CEK機械とCESK機械

**CEK機械:**

CEK機械は、SECD機械の発展形であり、以下の特徴を持つ:

- **C (Control)**: 制御 - 現在評価中の式
- **E (Environment)**: 環境 - 変数のバインディング
- **K (Continuation)**: 継続 - 計算の残りの部分

CEK機械は、SECD機械のダンプ（コールスタック）をより高度な継続（continuation）に置き換え、パラメータを直接環境に配置する。

**CESK機械:**

CESK機械は、CEK機械にストア（Store）を追加したものである:

- **C (Control)**: 制御
- **E (Environment)**: 環境 - 変数をアドレスに対応付ける
- **S (Store)**: ストア - アドレスから値への有限写像（ヒープに相当）
- **K (Continuation)**: 継続

**CESK機械の利点:**

- 環境が変数をストア上のポインタ（アドレス）に対応付ける
- ストアはアドレスから格納可能な値（クロージャや継続を含む）への写像
- 可変状態（mutable state）をCEK機械よりもうまくモデル化できる

**継続の役割:**

CESK機械では、現在の計算は常に何らかの継続の代理として実行されていると仮定される。継続はフレームのスタックであり、各フレームは式の値を待っているコンテキストを表す。継続は式の動的評価コンテキストである。

### 5.3 抽象機械の系統的導出

高レベルの推論規則（big-stepやsmall-step）から、低レベルの抽象機械へと体系的に変換することが可能である。これにより:

- 意味論の正しさを保ちながら、実装に近いモデルを得られる
- 型なしラムダ計算のcall-by-value評価の推論規則をSECDのような抽象機械に変換できる

## 6. 還元意味論（Reduction Semantics）

### 6.1 評価コンテキスト（Evaluation Context）

**歴史:**

還元意味論の重要な概念である評価コンテキストは、Matthias FellesenとRobert Hiebによって1992年に導入された。

**基本概念:**

評価コンテキストは、「どこで次の計算ステップが起きるか」を選択的に指定する概念である。プログラムを以下のように分解する:

```
プログラム = 評価コンテキスト[被約式]
```

ここで、被約式（redex: reducible expression）は、還元可能な式である。

**意味論の定義:**

還元意味論は、以下のステップで定義される:

1. プログラムを評価コンテキストと被約式に**分解（decomposition）**する
2. 被約式を還元規則に従って簡約する
3. 簡約された式をコンテキストに**埋め込む（plugging / recomposition）**

**例（call-by-value lambda calculus）:**

評価コンテキスト:
```
E ::= []                 (穴)
    | E e                (関数位置)
    | v E                (引数位置)
```

還元規則:
```
(λx. e) v → e[x := v]   (ベータ簡約)
```

評価: プログラムeを `E[r]` に分解し、rが `(λx. e') v` の形であれば、`E[e'[x := v]]` に遷移する。

### 6.2 Wright and Felleisen

Wright and Felleisen（1994年）は、コンテキストベースの還元意味論がプログラミング言語の型安全性を表現・証明するための便利な形式であることを実証した。

還元意味論は、SML、Scheme、JavaScriptなど多くの言語のコアをモデル化するために使用されてきた。

### 6.3 コンテキスト感応還元意味論

還元意味論は、コンテキスト感応（context-sensitive）であるため、標準的な項書き換えエンジン（context-insensitive term rewriting engines）では直接実行できないように見える。しかし、書き換え論理（rewriting logic）を意味論の基盤として使用することで、このギャップを埋めることができる。

書き換え論理を用いると、還元ベースの操作的意味論を、標準的なコンテキスト非感応な項書き換えエンジン上で実行できる。

## 7. 項書き換えと書き換え論理

### 7.1 項書き換えシステム（Term Rewriting System: TRS）

項書き換えシステムは、部分項を他の項で置き換える方法を定義する書き換えシステムである。

**構成要素:**

- 項（terms）: 入れ子になった部分式を持つ式
- 書き換え規則（rewrite rules）: `l → r` の形式で、lをrに置き換える

**書き換えの性質:**

- **合流性（confluence）**: 異なる順序で書き換えても同じ結果になる
- **停止性（termination）**: 無限に書き換えが続かない
- **正規形（normal form）**: これ以上書き換えできない項

### 7.2 書き換え論理意味論（Rewriting Logic Semantics: RLS）

**概要:**

書き換え論理は、プログラミング言語の操作的意味論を定義するための計算論理フレームワークとして機能する。Grigore Roșu らによって提唱された。

**対応する意味論スタイル:**

RLSは、以下を含む複数の操作的意味論スタイルに対応できる:

- 大ステップ構造的操作的意味論
- 小ステップ構造的操作的意味論
- モジュラーSOS
- 評価コンテキストを用いた還元意味論
- 継続ベース意味論
- Chemical Abstract Machine

**意義:**

各言語定義スタイルは、RLS理論として忠実に捉えることができ、元の言語定義における計算ステップとRLS理論における計算ステップの間に一対一の対応がある。

## 8. Kフレームワーク

### 8.1 概要

Kフレームワークは、書き換えベースの実行可能意味論フレームワークであり、プログラミング言語、型システム、形式解析ツールを構成（configurations）と規則（rules）を用いて定義できる。

**開発者:** Runtime Verification社とイリノイ大学のFormal Systems Laboratory（FSL）

### 8.2 実行可能仕様としての役割

Kフレームワークは、プログラミング言語の形式的意味論を直感的かつモジュラーな方法で定義できる。定義が完了すると、Kは以下のツール群を提供する:

- **実行可能モデル**: 言語のインタープリタとして機能
- **プログラム検証器**: 正当性を検証するツール

### 8.3 検証機能

Kフレームワークは、到達可能性論理（reachability logic）を用いて、言語に依存しない検証フレームワークを提供する:

- 操作的意味論を入力として受け取る（信頼された意味論）
- プログラム検証器を追加の労力なしに自動生成する
- 操作的意味論とプログラムの正当性仕様の両方を、到達可能性規則として扱う
- 健全（sound）かつ相対的に完全（relatively complete）な到達可能性論理証明システムを使用

### 8.4 適用事例

Kフレームワークは、以下の言語の形式意味論に適用されている:

- C、Java、JavaScript、Rust
- スマートコントラクト言語（Solidity、Michelson等）
- ドメイン固有言語

## 9. 操作的意味論と仕様の関係

### 9.1 実行可能仕様（Executable Specification）

操作的意味論は、実行可能仕様と密接な関係がある。

**実行可能仕様の特徴:**

- 仕様そのものがインタープリタとして機能する
- 仕様を実行してシステムの振る舞いを観察できる
- 仕様と実装のギャップを縮める

**LOTOSの例:**

LOTOS（Language Of Temporal Ordering Specification）は、分散システムのための実行可能仕様言語である。LOTOS操作的意味論とその実行可能性に関する議論があり、プロトタイプのLOTOSインタープリタが開発された。このインタープリタは、ユーザーが仕様の実行を対話的に指示できるシステムである。

### 9.2 操作的意味論とインタープリタの対応

操作的意味論は、インタープリタの実装に対応すると考えられる:

- 大ステップ意味論 → 再帰的評価関数
- 小ステップ意味論 → ステップ実行可能なインタープリタ
- 抽象機械 → スタックベースまたはレジスタベースのVM

この対応により、意味論定義から実装を導出したり、実装の正しさを意味論と照らして検証したりできる。

### 9.3 検証への応用

操作的意味論は、以下の検証タスクに使用される:

- **型安全性の証明**: 進行（progress）と保存（preservation）の性質
- **プログラム等価性**: 双模倣等価やコンテキスト等価性
- **不変条件の検証**: 実行のすべてのステップで成り立つ性質
- **モデル検査**: 状態空間探索による性質の検証

## 10. 意味論の比較：操作的 vs 表示的 vs 公理的

### 10.1 三つの意味論アプローチ

プログラム意味論には三つの主要なアプローチがある:

| アプローチ | 焦点 | 記述方法 |
|----------|------|---------|
| **操作的意味論** | プログラムの振る舞い | 計算ステップのシーケンス |
| **表示的意味論** | プログラムが表すもの | 数学的対象への写像 |
| **公理的意味論** | プログラムが満たす性質 | 形式論理における公理と推論規則 |

### 10.2 操作的意味論 vs 表示的意味論

**基本的な違い:**

- **操作的**: 「どのように計算されるか」を記述
- **表示的**: 「何を意味するか」を記述

**算術式の例:**

- **操作的**: 式 `2 + 3` を評価するステップを記述（`2 + 3 → 5`）
- **表示的**: 式 `2 + 3` に数学的対象（整数5）を割り当てる（`⟦2 + 3⟧ = 5`）

**比較:**

| 観点 | 操作的意味論 | 表示的意味論 |
|------|-------------|-------------|
| 直感性 | 実行に近く直感的 | より抽象的・数学的 |
| インタープリタ対応 | 直接対応する | 間接的 |
| 合成性 | 必ずしも保証されない | 合成性が重要な特性 |
| 複雑性 | 厳密に定義すると複雑 | 数学的困難（再帰、定義域理論） |
| 非停止性 | 扱いが難しい（big-stepの場合） | ボトム（⊥）で表現 |

**接続の重要性:**

表示的意味論が抽象的・数学的である場合、操作的意味論とのつながりを確立することが重要である。これにより、抽象的な意味論が実装可能であることが保証される。

### 10.3 操作的意味論 vs 公理的意味論

**公理的意味論（Axiomatic Semantics）:**

- Hoare論理に基づく
- プログラムの正当性証明を目的とする
- Hoareトリプル `{P} C {Q}` を用いる

**比較:**

| 観点 | 操作的意味論 | 公理的意味論 |
|------|-------------|-------------|
| 目的 | プログラムの実行を記述 | プログラムの正当性を証明 |
| 記述対象 | 計算の過程 | 事前条件と事後条件の関係 |
| 利用 | 言語設計、実装 | 形式検証、プログラム証明 |

**相補性:**

操作的意味論と公理的意味論は相補的である。操作的意味論がプログラムの実行を定義し、公理的意味論がその上でプログラムの性質を証明する。

## 11. 操作的意味論の利点

### 11.1 直感的で理解しやすい

操作的意味論は、プログラムの実行過程を直接的に記述するため、プログラマにとって理解しやすい。特に:

- インタープリタやデバッガの動作と直接対応
- ステップ実行による動作の追跡が可能

### 11.2 実装との密接な関係

操作的意味論は、言語実装（インタープリタやVM）の青写真として機能する:

- 抽象機械からVMの実装を導出できる
- 意味論定義から正しい実装を体系的に生成できる

### 11.3 実行可能性

多くの操作的意味論は、そのまま実行可能である:

- Kフレームワークなどのツールにより、意味論定義から直接インタープリタを生成
- プロトタイピングや言語設計の検証が容易

### 11.4 非決定性と並行性のモデル化

小ステップ操作的意味論とLTSは、非決定性や並行性を自然にモデル化できる:

- 複数の遷移可能性を明示的に表現
- インターリービング意味論や真の並行性の記述

### 11.5 検証への適用

操作的意味論は、以下の検証技術の基盤となる:

- モデル検査
- 型安全性の証明
- 双模倣等価性の証明
- ランタイム検証

## 12. 操作的意味論の限界と課題

### 12.1 精密さと繊細さ

操作的意味論は具体的であるがゆえに、以下の問題がある:

- 少しの規則変更でプログラムの意味が大きく変わる可能性
- 記述が詳細すぎて、本質的でない詳細に引きずられる

### 12.2 形式的な記述の複雑性

非形式的に使う場合は良いが（言語マニュアル等）、形式的に厳密に定義すると極めて複雑になる。

### 12.3 合成性の欠如

操作的意味論は、必ずしも合成性（compositionality）を保証しない:

- プログラム全体の意味が、部分の意味から自明に構成されない場合がある
- これは表示的意味論の重要な特性である

### 12.4 複雑なシステムへの適用の困難さ

集合と関数の枠組みでプログラムの意味を記述するのは、以下の場合に困難:

- 無限実行や部分性には構造を導入して対応できるが、
- 並列プログラムやリアクティブシステムでは辛い
- 時間の概念が陽に絡むと、表示的記述が困難

### 12.5 大ステップ意味論の限界

大ステップ意味論では:

- 非停止する計算に対する推論木が存在しない
- そのため、発散する計算についての性質を述べることが困難

小ステップ意味論はこの問題を解決するが、記述が冗長になる。

### 12.6 状態空間爆発

モデル検査や探索的検証を行う際、状態空間が指数的に増大する「状態爆発問題」が発生しやすい。

## 13. 操作的意味論の最新動向

### 13.1 モジュラーSOS（MSOS）

Peter Mosses によって提案されたモジュラーSOSは、意味論定義のモジュール性を向上させる手法である。

**特徴:**

- 言語拡張時に既存の規則を変更せずに新しい規則を追加できる
- 大規模な言語の意味論を管理しやすくする

### 13.2 真の並行性への拡張

Pomset LTSなど、真の並行性（True Concurrency）をサポートする操作的意味論の研究が進んでいる（2026年の論文も参照）。

### 13.3 K Framework と Reachability Logic

KフレームワークとReachability Logicの統合により、操作的意味論から自動的にプログラム検証器を生成する技術が進展している。

### 13.4 Big-Stop Semantics

2025年の研究では、大ステップの判断の中に小ステップ意味論を組み込む「Big-Stop Semantics」が提案されている。これにより、両方の利点を統合する試みが続けられている。

### 13.5 型システムとの統合

操作的意味論を基盤とした、より表現力の高い型システム（依存型、洗練型等）の研究が進んでいる。

## 14. 実践における操作的意味論

### 14.1 プログラミング言語の標準化

多くの言語仕様では、非形式的な操作的意味論が使用される:

- Python、Ruby、JavaScriptなどの言語リファレンス
- 実装の振る舞いを記述するための「リファレンス実装」

### 14.2 形式検証プロジェクト

以下のプロジェクトでは、形式的な操作的意味論が使用されている:

- **CompCert**: 検証済みCコンパイラ（C言語のCompcert C意味論）
- **seL4**: 検証済みマイクロカーネル
- **CakeML**: 検証済みMLコンパイラ

### 14.3 スマートコントラクトの検証

Ethereum、Cardano、Tezosなどのブロックチェーンプラットフォームでは、スマートコントラクト言語の操作的意味論が定義され、形式検証に使用されている（Kフレームワークを用いたSolidityやMichelsonの意味論など）。

### 14.4 教育

操作的意味論は、プログラミング言語理論の教育において中心的な役割を果たす:

- 「Software Foundations」「Programming Language Foundations」などの教科書
- Coq、Agda、Isabelleなどの定理証明器を用いた演習

## 15. まとめ

操作的意味論は、プログラミング言語の意味を形式的に定義するための強力かつ直感的な手法である。Gordon Plotkinによって体系化された構造的操作的意味論（SOS）は、プログラミング言語理論の基礎となっている。

**主要な特徴:**

- **構文指向性**: プログラムの構造に従った規則定義
- **実行との対応**: インタープリタや抽象機械との直接的な関係
- **柔軟性**: 大ステップ、小ステップ、還元意味論など多様なスタイル
- **実行可能性**: Kフレームワークなどにより、意味論から直接ツールを生成可能

**主要な応用:**

- プログラミング言語の設計と実装
- 型安全性や他の性質の形式的証明
- プログラム検証とモデル検査
- 並行システムとプロセス代数の意味論

**課題と限界:**

- 形式的記述の複雑性
- 合成性の欠如
- 大ステップ意味論における非停止性の扱い
- 状態爆発問題

**今後の展望:**

- モジュラーSOSによる大規模言語への対応
- 真の並行性のモデル化
- 到達可能性論理による検証の自動化
- 型システムとの統合による強力な静的検証

操作的意味論は、仕様と実装の橋渡しとして、プログラミング言語の設計・実装・検証において不可欠な役割を果たし続けている。

## 参考文献・情報源

### 構造的操作的意味論（SOS）
- [A Structural Approach to Operational Semantics - Gordon D. Plotkin](https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf)
- [The Origins of Structural Operational Semantics - Gordon D. Plotkin](https://homepages.inf.ed.ac.uk/gdp/publications/Origins_SOS.pdf)
- [Structural Operational Semantics | PLS Lab](https://www.pls-lab.org/Structural_Operational_Semantics)
- [Modular Structural Operational Semantics - Peter D. Mosses](https://courses.grainger.illinois.edu/cs522/sp2016/ModularStructuralOperationalSemantics.pdf)

### 操作的意味論の概要
- [Operational semantics - Wikipedia](https://en.wikipedia.org/wiki/Operational_semantics)
- [操作的意味論 - Wikipedia](https://ja.wikipedia.org/wiki/%E6%93%8D%E4%BD%9C%E7%9A%84%E6%84%8F%E5%91%B3%E8%AB%96)
- [プログラム意味論 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%A0%E6%84%8F%E5%91%B3%E8%AB%96)
- [Operational Semantics - cs.lmu.edu](https://cs.lmu.edu/~ray/notes/opsem/)

### 大ステップと小ステップ意味論
- [Integrated Operational Semantics: Small-Step, Big-Step and Multi-step | Springer](https://link.springer.com/chapter/10.1007/978-3-642-30885-7_2)
- [Big-Stop Semantics Small-Step Semantics in a Big-Step Judgment](https://www.cs.cmu.edu/~runmingl/paper/stop.pdf)
- [Natural Semantics | Semantic Scholar](https://www.semanticscholar.org/paper/Natural-Semantics-Kahn/3630dfdf9e95a8ba07288a3a4ff336a293c5bd54)
- [Smallstep: Small-step Operational Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)

### ラベル付き遷移システム（LTS）
- [Labelled Transition System - ScienceDirect Topics](https://www.sciencedirect.com/topics/mathematics/labelled-transition-system)
- [Transition system - Wikipedia](https://en.wikipedia.org/wiki/Transition_system)
- [Structural Operational Semantics for True Concurrency](https://arxiv.org/abs/2601.17322)
- [transition system in nLab](https://ncatlab.org/nlab/show/transition+system)

### 双模倣（Bisimulation）
- [Bisimulation - Wikipedia](https://en.wikipedia.org/wiki/Bisimulation)
- [Process Algebra, CCS, and Bisimulation Decidability | Request PDF](https://www.researchgate.net/publication/2736686_Process_Algebra_CCS_and_Bisimulation_Decidability)
- [Process Algebra - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/process-algebra)

### 抽象機械
- [SECD machine - Wikipedia](https://en.wikipedia.org/wiki/SECD_machine)
- [CEK Machine - Wikipedia](https://en.wikipedia.org/wiki/CEK_Machine)
- [Writing an interpreter, CESK-style - Matt Might](https://matt.might.net/articles/cesk-machines/)
- [Abstracting Abstract Machines](https://arxiv.org/pdf/1007.4446)
- [From operational semantics to abstract machines | ACM](https://dl.acm.org/doi/10.1145/91556.91680)

### 還元意味論（Reduction Semantics）
- [Reduction (or Contextual) Semantics - CPSC 509](https://www.cs.ubc.ca/~rxg/cpsc509-spring-2022/05-reduction.pdf)
- [A Semantics for Context-Sensitive Reduction Semantics](https://users.cs.northwestern.edu/~robby/plug/aplas2011-kmjf.pdf)
- [An operational semantics for Scheme - Robby Findler](https://users.cs.northwestern.edu/~robby/pubs/papers/jfp2008-mf.pdf)

### 項書き換えと書き換え論理
- [A Rewriting Logic Approach to Operational Semantics - Extended Abstract](https://www.researchgate.net/publication/222660544_A_Rewriting_Logic_Approach_to_Operational_Semantics_Extended_Abstract)
- [Rewriting - Wikipedia](https://en.wikipedia.org/wiki/Rewriting)
- [Term Rewriting Systems - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/term-rewriting-systems)

### Kフレームワーク
- [K Framework - An Overview | Runtime Verification](https://runtimeverification.com/blog/k-framework-an-overview)
- [K: A Semantic Framework for Programming Languages](https://fsl.cs.illinois.edu/publications/rosu-2017-marktoberdorf.pdf)
- [K | Runtime Verification Inc](https://kframework.org/)
- [Semantics-based program verifiers for all languages | ACM SIGPLAN](https://dl.acm.org/doi/10.1145/3022671.2984027)

### 意味論の比較
- [Operational and Denotational Semantics - HackMD](https://hackmd.io/@alexhkurz/Hkf6BTL6P)
- [Denotational semantics - Wikipedia](https://en.wikipedia.org/wiki/Denotational_semantics)
- [Concepts of Programming Languages Lecture 6 - Semantics](https://faculty.ksu.edu.sa/sites/default/files/06-semantics.pdf)
- [semantics - cs.lmu.edu](https://cs.lmu.edu/~ray/notes/semantics/)
- [表示的意味論 - Wikipedia](https://ja.wikipedia.org/wiki/%E8%A1%A8%E7%A4%BA%E7%9A%84%E6%84%8F%E5%91%B3%E8%AB%96)

### 実行可能仕様
- [Executable Specification - ScienceDirect Topics](https://www.sciencedirect.com/topics/engineering/executable-specification)
- [An interpreter for LOTOS - Wiley](https://onlinelibrary.wiley.com/doi/abs/10.1002/spe.4380180406)

### 形式手法と限界
- [形式手法入門： 利点・期待と欠点・限界](https://formal.mri.co.jp/outline/fm-introduction-2.html)
- [形式手法 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E6%89%8B%E6%B3%95)
- [操作的意味論と、不純な表示的意味論 - 檜山正幸のキマイラ飼育記](https://m-hiyama.hatenablog.com/entry/20120118/1326852526)
