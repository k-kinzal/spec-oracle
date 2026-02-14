# 非決定性の形式的理論

## 概要

非決定性（nondeterminism）は、形式仕様と形式手法において中核的な役割を果たす概念である。プログラミング言語における非決定性とは異なり、形式仕様における非決定性は抽象化の強力な手段として機能する。本文書では、非決定性の形式的定義、意図的な非決定性と未規定の違い、選択の意味論、非決定性オートマトン、プロセス代数における扱いなど、非決定性の理論的側面を包括的に調査する。

## 1. 非決定性の基本概念

### 1.1 形式仕様における非決定性の意味

形式仕様における非決定性は、「正しい振る舞いを拡張する方法が複数存在すること」を意味する。これには、システム外部からの異なる潜在的な入力も含まれる。重要なのは、これが実装の詳細を抽象化する手段であるという点である。

形式仕様言語において、非決定性は抽象化の手段として機能する。例えば、TLA+のような仕様記述言語では、`AttemptLogin == \/ Login \/ RejectLogin`のように、実装の詳細を抽象化しながら高レベルの振る舞いに焦点を当てることができる。

### 1.2 プログラミングにおける非決定性との違い

形式仕様における非決定性とプログラミングにおける非決定性には重要な違いがある：

- **形式仕様**: 正しい振る舞いを複数の経路に沿って拡張できることを意味する
- **プログラム**: コードがどの経路を取るか分からないことを意味する

この違いは本質的である。仕様における非決定性は「可能性の記述」であり、実装における非決定性は「不確実な実行」である。

### 1.3 非決定性の役割

非決定性のモデリングは形式仕様の中核的な部分であり、並行性（concurrency）は非決定性の最も劇的な源泉の一つである。抽象化としての非決定性を習得することは、優れた仕様を書く上で鍵となる。

## 2. 非決定性と未規定の区別

### 2.1 根本的な違い

非決定性と未規定（underspecification）は、しばしば混同されるが、異なる概念である：

**未規定（Underspecification）**:
- 仕様記述者が複数の代替的な振る舞いを許可し、その選択を実装者に委ねること
- 有効な実装は、少なくとも1つの代替案を実装すればよいが、必ずしもすべてを実装する必要はない
- 実装者が任意の方法で解決できる選択肢を残すこと

**固有の非決定性（Inherent/Intentional Nondeterminism）**:
- 有効な実装がすべての代替案を反映する必要があること
- システムの振る舞いにおいて実際にすべての可能な代替案が存在しなければならない
- 実装は実際に異なる時点で異なる選択を行う能力を持つ必要がある

### 2.2 なぜこの区別が重要か

ほとんどの形式主義は非決定性と未規定を区別しない。しかし、WalickiとMeldalは代数的仕様において類似の区別を行い、その主な動機は、未規定が時として過剰仕様（overspecification）につながる可能性があり、そのような場合には明示的な非決定性を使用する方が良いとしている。

### 2.3 実践的な意味

この区別は、仕様の詳細化（refinement）プロセスにおいて重要である：

- 未規定の場合: 実装者は1つの選択肢を選び、それを一貫して使用できる
- 固有の非決定性の場合: 実装は異なる状況で異なる選択を行う機構を持たなければならない

例えば、「x' ∈ {1,2,3}」という仕様が未規定であれば、実装は常に`x := 1`とすることができる。しかし、これが固有の非決定性であれば、実装は実際に1, 2, 3のいずれかを（異なる実行で）返す能力を持たなければならない。

## 3. 非決定性の分類

### 3.1 5種類の非決定性

非決定性には少なくとも5つの主要な種類が存在する：

1. **抽象化としての非決定性（Abstraction Nondeterminism）**: 実装の詳細を隠蔽するための仕様レベルの非決定性
2. **並行性の非決定性（Concurrency Nondeterminism）**: 並行プロセスの実行順序の不確定性
3. **選択的非決定性（Choice Nondeterminism）**: 明示的な選択演算子による非決定性
4. **バックトラッキング非決定性（Backtracking Nondeterminism）**: 制約充足のための探索空間
5. **確率的非決定性（Probabilistic Nondeterminism）**: 確率分布に基づく選択

### 3.2 天使的・悪魔的・エラティック非決定性

意味論的には、非決定性は3つの重要な種類に分類される：

**天使的非決定性（Angelic Nondeterminism）**:
- 可能な限り失敗を避ける選択の性質
- 成功可能な選択肢が存在する場合、必ず成功する経路を選ぶ
- 詳細化計算（refinement calculus）において仕様を簡潔にする
- 正規表現の形式的基礎となる

**悪魔的非決定性（Demonic Nondeterminism）**:
- 最悪のケースを考慮する選択の性質
- すべての可能な選択が成功する場合にのみ成功とみなす
- 安全性検証において重要

**エラティック非決定性（Erratic Nondeterminism）**:
- 天使的でも悪魔的でもない、完全に任意の選択
- 実装の自由度を最大化

### 3.3 形式的モデリング

天使的および悪魔的非決定性は、単調述語変換子（monotonic predicate transformers）のモデルと同型な二項多重関係（binary multirelations）のモデルで表現できる。

Hoare論理の命題的変種を使用して、天使的および悪魔的非決定性の両方を示すプログラムについて推論することができる。これは、原子的アクションの意味が公理的に指定される非解釈設定（uninterpreted setting）で機能する。

## 4. 非決定性オートマトン

### 4.1 非決定性有限オートマトン（NFA）の定義

非決定性有限オートマトン（Nondeterministic Finite Automaton, NFA）は、有限オートマトンの一種であり、ある状態と入力があったとき、次の遷移先が一意に決定しないことがある。

形式的には、NFAは五つ組 (Σ, Q, δ, q₀, F) として定義される：

- Σ: 文字を表す有限集合（アルファベット）
- Q: 状態を表す有限集合
- δ: Q × (Σ ∪ {ε}) → 2^Q で定義される遷移関数
- q₀: 初期状態
- F: 受理状態の集合

### 4.2 NFAの特性

NFAの次の状態は現在の入力イベントのみで決定されるのではなく、その後の任意個数の入力イベント（文字列）にも影響される。

主な特性：
- 次の状態が一意に決定しないこと
- 入力文字がなくても自由に他の状態へ遷移できるε遷移が可能

### 4.3 DFAとの等価性

任意のNFAには、それと同じ言語を受容する決定性有限オートマトン（DFA）が存在する。非決定性有限オートマトンをより単純な決定性有限オートマトンでシミュレーションするには「サブセット構成（subset construction）」というテクニックを使う。

これは重要な理論的結果であり、NFAとDFAが認識する言語のクラスが一致することを示している。しかし、NFAは時としてDFAよりも指数的に簡潔な表現を可能にする。

## 5. プロセス代数における非決定性

### 5.1 プロセス代数の概要

プロセス代数（Process Algebra）またはプロセス計算（Process Calculus）は、並行システムを形式的にモデリングする多様な関連アプローチのファミリーである。独立したエージェントやプロセス間の相互作用、通信、同期を高レベルで記述するツールを提供する。

主要な例：
- **CSP（Communicating Sequential Processes）**: Hoareによって開発
- **CCS（Calculus of Communicating Systems）**: Milnerによって開発
- **ACP（Algebra of Communicating Processes）**
- **LOTOS**
- **π計算（Pi-Calculus）**

### 5.2 CSPにおける非決定性

CSPは非決定性を扱うために2つの異なる選択演算子を提供する：

**外部選択（External Choice, □演算子）**:
- 環境によって選択を解決できる決定的選択
- 環境が初期イベントを通信することで、どちらかのプロセスを選択
- `P □ Q` は環境が最初のイベントを提供することで選択される

**内部選択（Internal Choice, ⊓演算子）**:
- 環境の影響を受けない非決定的選択
- プロセスの将来の進化が2つのコンポーネントプロセス間の選択として定義される
- 環境は選択を解決できない
- `P ⊓ Q` はシステム内部で非決定的に選択される

### 5.3 意味論による区別

両方のプロセスのトレース（traces）は同じである可能性があるが、2番目のプロセスは内部的に異なるオプションに切り替えることができ、最初のケースでは1つのイベントを拒否し、2番目のケースでは別のイベントを拒否する可能性がある。

安定失敗意味論（stable failures semantics）は2つのプロセスを区別する。2番目のプロセスは、τ遷移（内部遷移）によって到達可能な2つの安定状態（τ遷移のない状態）を持ち、それぞれが異なるイベントを拒否する。

### 5.4 CCSにおける非決定性

CCSも非決定性を意味論モデルに含む。並行プログラミングにおいて、非決定性の制御は非常に重要であり、誤った状況に陥らないようにすることが課題となる。

CCSとCSPの両方は、非決定性の影響をそれらの意味論モデルに含んでいる。

## 6. 選択演算子と形式意味論

### 6.1 非決定的選択演算子

非決定的プログラミング言語は、プログラムの特定のポイント（選択点と呼ばれる）でプログラムフローのさまざまな代替案を指定できる言語である。「Choose」は非決定的演算子の典型的な名前である。

### 6.2 意味論的アプローチ

非決定的プログラミング言語の異なる意味論モデルが、抽象型によるプログラミング言語の代数的仕様の形式的枠組みで定義、分析、比較されている。4つの抽象型が与えられている：

1. **選択的（エラティック）非決定性**: Choice ("erratic") nondeterminism
2. **バックトラック（悪魔的）非決定性**: Backtrack ("demonic") nondeterminism
3. **無制限（天使的）非決定性**: Unbounded ("angelic") nondeterminism
4. **緩い非決定性**: Loose nondeterminism

### 6.3 TLA+における非決定性

TLA+では、非決定性を表現するための複数の機構がある：

**CHOOSE演算子**:
- Hilbertのε演算子を実装
- 一般的な構文: `CHOOSE x \in set: P(x)`
- 集合から値を取り出す必要があるときに有用
- 例: `ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds`

**PlusCalにおける非決定性**:
- `with x \in set`: setから非決定的に値を選択
- `either branch1 or branch2`: 非決定的に分岐を選択

具体例（コンセンサス仕様より）:
```
with (v \in Value) { chosen := {v} }
```

### 6.4 バックトラッキング非決定性

一つの選択方法は、バックトラッキングシステム（AmbやPrologの単一化など）に具現化されており、一部の代替案が「失敗」する可能性があり、プログラムはバックトラックして他の代替案を試みる。

**Amb演算子**:
- "ambiguous"の略
- 自動的理論における非決定性と密接に関連
- 可変数の式（または値）を取り、将来の計算で制約を満たす正しいものを生成し、失敗を回避

**Prologのバックトラッキング**:
- Prologは異なる述語の真理値を検索するためにバックトラッキングを使用
- バックトラックプログラムは、現在の部分解を法的な選択で段階的に拡張して解を構築
- カット演算子（!）でバックトラッキングを制御可能

## 7. パワードメイン理論

### 7.1 パワードメインの概要

パワードメイン（Power Domain）は、表示的意味論（denotational semantics）およびドメイン理論における非決定的および並行計算のドメインである。パワードメイン構成は、再帰と非決定性を組み合わせたプログラムに意味論を与える方法である。

パワードメインは、Plotkinによって非決定的または並行プログラムに意味論を与えるために1976年に導入された。

### 7.2 3つの標準的パワードメイン

3つの主要なパワードメインがあり、それぞれ異なる非決定性の考え方に対応する：

**Hoareパワードメイン（下パワードメイン）**:
- ドメインDの非空Scott閉部分集合の束
- 天使的非決定性のモデルとして使用される
- 近似に基づいて集合を順序付け
- 下パワードメインは非決定性に天使的意味論を与える

**Smythパワードメイン（上パワードメイン）**:
- 悪魔的非決定性のモデリングに有用
- 上パワードメインでは、発散可能な任意のプログラムは意味論 ↑{⊥} = D を持つ
- これは悪魔的意味論である
- 3つのパワードメイン構成の中で最も普及しているのがSmythパワードメイン

**Plotkinパワードメイン（凸パワードメイン）**:
- 集合上のEgli-Milner順序を使用
- HoareパワードメインとSmythパワードメインの交差
- エラティック非決定性のモデル化に使用

### 7.3 パワードメインと集合の問題

非決定的プログラムは複数の結果を持つ可能性があるため、意味論の自然な選択は状態の非空集合にマッピングする関数となる: C[[c]] : Σ → (℘(Σ⊥) − ∅)（℘(S)はSのべき集合）

しかし、べき集合と完全部分順序（CPO）は相性が悪く、やや複雑な構成、すなわちドメインDの有限生成部分集合を含む構成が必要となる。

### 7.4 その他のパワードメイン

確率的パワードメイン（probabilistic powerdomains）など、他の有用なパワードメイン構成も存在し、可能な結果の集合を確率にマッピングする。

## 8. テスト理論と非決定性

### 8.1 MayテストとMustテスト

プロセス代数において、テスト等価性は非決定性の異なる側面を捉える：

**Mayテスト等価性（May-testing equivalence）**:
- 安全性特性（safety properties）を正確に捉える
- プロセスが特定の振る舞いを示す可能性があるかを検証
- 少なくとも1つの実行で成功すれば、テストに合格

**Mustテスト等価性（Must-testing equivalence）**:
- 生存性特性（liveness properties）を正確に捉える
- プロセスがすべての実行で特定の振る舞いを示すかを検証
- すべての可能な実行で成功しなければならない

### 8.2 テストと詳細化

標準的な（must）テスト前順序の理論は、クライアント詳細化前順序とピア詳細化前順序の両方に拡張できる。テストフレームワークは、単純なサーバー・クライアント関係を超えて、ピア・ツー・ピアのテストシナリオを含むように進化している。

### 8.3 相互テスト

直感的に、プロセスpがそのピアqを満たすというのは、それらが並列に実行されるときに両方が満たされることが保証される場合である。ある意味で、両方のピアがそのパートナーをテストする。

### 8.4 報酬テストと条件付き生存性

報酬テスト（reward testing）は、結果として得られる意味的等価性も条件付き生存性特性を捉えることを示している。これは古典的なmayテストとmustテストフレームワークの拡張である。

## 9. 詳細化と非決定性の削減

### 9.1 詳細化の概念

詳細化（Refinement）とは、形式手法において、抽象的な形式仕様記述から具体的な実行プログラムへと検証可能な変換を行うことである。

このプロセスにおいて、非決定性は重要な役割を果たす。操作の詳細化は、システムの操作の仕様を実装可能なプログラムに変換することであり、この過程で：

- 事前条件は弱められる（より多くの状況で適用可能になる）
- 事後条件は強められる（より具体的な結果を保証する）

### 9.2 非決定性の削減プロセス

詳細化によって仕様に内在する非決定性を段階的に削減し、最終的に完全に決定的な実装へと変換する。

具体例：
1. 初期仕様: `x' ∈ {1,2,3}` （3つの可能な結果）
2. 第一詳細化: `x' ∈ {1,2}` （2つの可能な結果）
3. 第二詳細化: `x' ∈ {1}` （1つの結果）
4. 最終実装: `x := 1` （決定的）

### 9.3 詳細化と未規定の関係

未規定の場合、詳細化は単に仕様が許可する代替案の1つを選択することである。固有の非決定性の場合、詳細化はより複雑であり、実装は実際に複数の代替案を維持する機構を持たなければならない。

## 10. 非決定性の実用的応用

### 10.1 並行システムのモデリング

並行システムは、デッドロック、スターベーション、通信、非決定的振る舞いなどの問題を含む。数学的理論に基づく形式手法を使用することで、これらのシステムへの信頼を高めることができる。

非決定性は並行システムにおいて不可避であり、以下の要因から生じる：
- プロセスのインターリービング
- メッセージ到着順序の不確定性
- リソース競合
- 外部環境の予測不可能性

### 10.2 仕様記述言語における非決定性

主要な形式仕様言語における非決定性の扱い：

**Z言語とVDM**:
- モデル指向の形式手法
- 集合論に基づく仕様記述
- 非決定性を許容集合として表現

**Alloy**:
- 軽量形式手法
- 関係論理に基づく
- 制約ソルバーを用いた非決定的仕様の探索

**B Method**:
- 詳細化を中核とする形式手法
- 非決定性を段階的に削減

**TLA+**:
- 時相論理に基づく
- 並行システムの非決定性を明示的にモデル化

### 10.3 検証における役割

非決定性は、モデル検査において重要な役割を果たす：

- **状態空間探索**: すべての非決定的選択を探索
- **反例生成**: 非決定的選択の特定の組み合わせで失敗するケースを発見
- **公平性仮定**: 無限に繰り返される非決定的選択における公平性の考慮

## 11. 高度なトピック

### 11.1 非決定性と量子計算

量子コンピュータと非決定性の関係には誤解が多い：

**量子コンピュータと非決定性チューリングマシン**:
- 量子コンピュータが非決定性チューリングマシン（NTM）であるという主張は誤り
- 多項式時間の量子コンピュータの能力は多項式時間のNTMよりも低いと考えられている
- 計算複雑性クラスの関係: P ⊆ BPP ⊆ BQP ⊆ PSPACE

**量子重ね合わせと非決定性**:
- 量子ビット（qubit）は|0⟩と|1⟩の線形結合（重ね合わせ）の状態を取れる
- 量子系における非決定性は、並列合成から生じる
- 量子ネットワークプロトコルにおける非決定性は、並行実行とリソース割り当てから発生

**形式仕様の観点**:
- 量子ネットワークプロトコルのための形式仕様言語（例: PBKAT）が開発されている
- 確率的および非決定的振る舞いの両方を扱える

### 11.2 非決定性マトリクス（Nmatrices）

非決定性マトリクス（Nmatrices）は、オートマトン理論における非決定的計算のアイデアを論理体系の真理値評価に適用したものである。

複雑な式の真理値は、いくつかの非空なオプションの集合から非決定的に選択される。これにより、通常の真理値表では表現できない論理体系を形式化できる。

### 11.3 確率的非決定性

確率と非決定性の組み合わせは、現実のシステムのモデリングにおいて重要である：

**確率的パワードメイン**:
- 可能な結果の集合を確率にマッピング
- マルコフ決定過程（MDP）との関連

**確率的プロセス代数**:
- 非決定性と確率の両方を扱う
- 例: PEPA（Performance Evaluation Process Algebra）

**意味論的課題**:
- 確率と非決定性の相互作用の形式化
- 確率的選択と非決定的選択の順序依存性

### 11.4 公平性と非決定性

無限に続く非決定的選択において、公平性（fairness）は重要な概念である：

**弱公平性（Weak Fairness）**:
- 常に有効な操作は最終的に実行される

**強公平性（Strong Fairness）**:
- 無限に頻繁に有効な操作は無限に頻繁に実行される

公平性仮定は、非決定的並行システムの生存性特性の検証に不可欠である。

## 12. まとめと考察

### 12.1 非決定性の本質

形式仕様における非決定性は、単に「決まっていない」ことではなく、「複数の正しい可能性を許容する」という積極的な意味を持つ。これは抽象化の強力な手段であり、以下を可能にする：

1. **実装の自由度の提供**: 仕様は「何を」達成すべきかを述べ、「どのように」は実装者に委ねる
2. **段階的詳細化**: 抽象レベルから具体的実装へと段階的に移行
3. **並行性のモデリング**: 実行順序の不確定性を自然に表現
4. **環境との相互作用**: 外部からの予測不可能な入力を考慮

### 12.2 非決定性と未規定の明確な区別

「A or Bという仕様は未規定か？こんなに厳密に決まっているのに」という疑問に対する答え：

- 仕様「A or B」は非常に厳密に決まっている - AまたはBのいずれかが正しいと明確に述べている
- しかし、これが未規定か固有の非決定性かは、仕様の意図による：
  - **未規定の場合**: 実装はAかBのいずれか一方を選び、常にそれを使用すればよい
  - **固有の非決定性の場合**: 実装は実際にAとBの両方を異なる時点で実行できなければならない

非決定性は「仕様を決めていない」のとは別の話である。非決定性は、仕様が厳密に「複数の可能性のすべてが正しい」と決めているのである。

### 12.3 理論的重要性

非決定性の形式的理論は、以下の基盤を提供する：

1. **プロセス代数**: CSP、CCS、π計算などにおける選択演算子の意味論
2. **表示的意味論**: パワードメイン理論による非決定性の数学的モデル
3. **操作的意味論**: 非決定的遷移システムの振る舞い
4. **公理的意味論**: Hoare論理における非決定性の推論規則

### 12.4 実用的影響

非決定性の理解は、以下の実践に不可欠である：

1. **仕様記述**: 適切な抽象レベルの選択
2. **検証**: モデル検査における状態空間探索
3. **詳細化**: 仕様から実装への段階的変換
4. **並行システム設計**: デッドロックやスターベーションの回避

### 12.5 今後の展望

非決定性の理論は以下の方向で発展し続けている：

1. **量子計算**: 量子重ね合わせと非決定性の形式的関係
2. **機械学習**: ニューラルネットワークの振る舞いの非決定的仕様
3. **分散システム**: 大規模分散システムにおける非決定性の制御
4. **自律システム**: 環境との相互作用における適応的非決定性

非決定性は形式手法の中核概念であり続け、複雑なシステムの設計、仕様記述、検証において重要な役割を果たしている。

## 参考文献

### 主要文献

1. [Nondeterminism in Formal Specification](https://buttondown.com/hillelwayne/archive/nondeterminism-in-formal-specification/) - Hillel Wayne
2. [Five Kinds of Nondeterminism](https://buttondown.com/hillelwayne/archive/five-kinds-of-nondeterminism/) - Hillel Wayne
3. [Nondeterminism vs. Underspecification](https://www.researchgate.net/publication/221595066_Nondeterminism_vs_Underspecification)
4. [Underspecification, Inherent Nondeterminism and Probability in Sequence Diagrams](https://link.springer.com/chapter/10.1007/11768869_12)
5. [Communicating sequential processes](https://en.wikipedia.org/wiki/Communicating_sequential_processes) - Wikipedia
6. [Process calculus](https://en.wikipedia.org/wiki/Process_calculus) - Wikipedia

### プロセス代数と選択

7. [A gentle introduction to Process Algebras](https://www.pst.ifi.lmu.de/Lehre/fruhere-semester/sose-2013/formale-spezifikation-und-verifikation/intro-to-pa.pdf) - Rocco De Nicola
8. [Trace and Stable Failures Semantics for CSP-Agda](https://arxiv.org/pdf/1709.04714)
9. [External and Internal Choice with Event Groups in Event-B](https://eprints.soton.ac.uk/341169/1/twochoice.pdf)

### 天使的・悪魔的非決定性

10. [Angelic Processes](https://arxiv.org/abs/1505.04726)
11. [Programming with angelic nondeterminism](https://dl.acm.org/doi/10.1145/1706299.1706339)
12. [Modelling angelic and demonic nondeterminism with multirelations](https://www.researchgate.net/publication/222620288_Modelling_angelic_and_demonic_nondeterminism_with_multirelations)
13. [Synthesis of Strategies and the Hoare Logic of Angelic Nondeterminism](https://link.springer.com/chapter/10.1007/978-3-662-46678-0_2)

### パワードメイン理論

14. [CS 6110 Lecture 36 Monads, Nondeterminism and Powerdomains](https://www.cs.cornell.edu/courses/cs6110/2025sp/lectures/powerdomains.pdf)
15. [Power domains](https://en.wikipedia.org/wiki/Power_domains) - Wikipedia
16. [Powerdomains](https://www.pls-lab.org/Powerdomains) - PLS Lab
17. [A Denotational Semantics for Nondeterminism in Probabilistic Programs](https://www.cs.cmu.edu/~janh/papers/WangHR18.pdf)

### TLA+と仕様言語

18. [Nondeterminism — Learn TLA+](https://www.learntla.com/core/nondeterminism.html)
19. [A primer on formal verification and TLA+](https://jack-vanlightly.com/blog/2023/10/10/a-primer-on-formal-verification-and-tla)
20. [Formal specs as sets of behaviors](https://surfingcomplexity.blog/2025/07/26/formal-specs-as-sets-of-behaviors/)

### バックトラッキングとAmb

21. [Nondeterministic programming](https://en.wikipedia.org/wiki/Nondeterministic_programming) - Wikipedia
22. [Prolog - Backtracking](https://www.tutorialspoint.com/prolog/prolog_backtracking.htm)
23. [Amb - Rosetta Code](https://rosettacode.org/wiki/Amb)
24. [On Lisp --- 非決定性](https://www.asahi-net.or.jp/~kc7k-nd/onlispjhtml/nondeterminism.html)

### オートマトン理論

25. [非決定性有限オートマトン](https://ja.wikipedia.org/wiki/%E9%9D%9E%E6%B1%BA%E5%AE%9A%E6%80%A7%E6%9C%89%E9%99%90%E3%82%AA%E3%83%BC%E3%83%88%E3%83%9E%E3%83%88%E3%83%B3) - Wikipedia
26. [決定性有限オートマトンと非決定性有限オートマトンの等価性](https://comfreak.net/automaton7/)
27. [非決定性有限オートマトン(NFA)を例を用いて分かりやすく解説](https://www.krrk0.com/nondeterministic-finite-automaton/)

### テスト理論

28. [MUTUALLY TESTING PROCESSES](https://lmcs.episciences.org/776/pdf)
29. [Fair Testing Revisited: A Process-Algebraic Characterisation of Conflicts](https://link.springer.com/content/pdf/10.1007/978-3-540-30476-0_14.pdf)
30. [Reward Testing Equivalences for Processes](https://link.springer.com/chapter/10.1007/978-3-030-21485-2_5)

### 詳細化

31. [詳細化](https://ja.wikipedia.org/wiki/%E8%A9%B3%E7%B4%B0%E5%8C%96) - Wikipedia
32. [Mutation Testing in the Refinement Calculus](https://dl.acm.org/doi/pdf/10.1007/s00165-003-0011-8)

### 形式仕様言語

33. [Think IT - Z言語とVDM-SLの違いとその効果](https://thinkit.co.jp/free/article/0711/6/4/)
34. [形式手法のまとめ #VDM++](https://qiita.com/kannkyo/items/f9ab4407594f56b2fa79)
35. [Abstract State Machines, Alloy, B, TLA, VDM, and Z: 6th International Conference, ABZ 2018](https://link.springer.com/content/pdf/10.1007/978-3-319-91271-4.pdf)

### 量子計算

36. [A Language for Quantifying Quantum Network Behavior](https://rand.cs.uchicago.edu/files/PBKAT.pdf)
37. [Quantum superposition](https://en.wikipedia.org/wiki/Quantum_superposition) - Wikipedia
38. [量子コンピュータ](https://ja.wikipedia.org/wiki/%E9%87%8F%E5%AD%90%E3%82%B3%E3%83%B3%E3%83%94%E3%83%A5%E3%83%BC%E3%82%BF) - Wikipedia
39. [非決定性チューリングマシン](https://ja.wikipedia.org/wiki/%E9%9D%9E%E6%B1%BA%E5%AE%9A%E6%80%A7%E3%83%81%E3%83%A5%E3%83%BC%E3%83%AA%E3%83%B3%E3%82%B0%E3%83%9E%E3%82%B7%E3%83%B3) - Wikipedia

### その他

40. [Non-Deterministic Semantics for Logical Systems](https://link.springer.com/chapter/10.1007/978-94-007-0479-4_4)
41. [Semantics of nondeterminism, concurrency, and communication](https://www.academia.edu/88989695/Semantics_of_nondeterminism_concurrency_and_communication)
42. [プロセス計算](https://ja.wikipedia.org/wiki/%E3%83%97%E3%83%AD%E3%82%BB%E3%82%B9%E8%A8%88%E7%AE%97) - Wikipedia

---

**調査者**: researcher-12
**作成日**: 2026-02-14
**文字数**: 約17,000字
