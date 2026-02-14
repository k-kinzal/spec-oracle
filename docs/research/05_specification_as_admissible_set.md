# 仕様を「許容集合（admissible set）」として捉える理論的枠組み

## 調査概要

本調査では、仕様を「許容される振る舞いの集合」として定義し、その集合の広さが仕様の緩さに対応するという理論的枠組みについて、形式手法とプロセス代数の学術的根拠を調査した。

## 1. 基本概念：仕様＝振る舞いの集合

### 1.1 根本的な視点転換

Hochsteinは、形式仕様に関する根本的な洞察を示している：

> **「プログラムは命令のリスト、形式仕様は振る舞いの集合である」**

この区別は形式手法を理解する上で極めて重要である。仕様は実行可能な手順ではなく、正当な振る舞いすべてを含む（多くの場合無限の）集合として機能する。

参考: [Formal specs as sets of behaviors – Surfing Complexity](https://surfingcomplexity.blog/2025/07/26/formal-specs-as-sets-of-behaviors/)

### 1.2 振る舞い（behavior）の定義

- **振る舞い**とは、メソッド呼び出しとその戻り値の列（sequence）である
- **仕様**とは、すべての妥当な振る舞いを含む無限集合である
- **正しさ**とは、ある振る舞いがその仕様集合に属することを意味する

仕様は、すべての妥当な振る舞いを明示的に列挙するのではなく、TLA+のInit/Next パターンのような生成的アプローチを用いて、初期状態から連続的な遷移によって妥当な振る舞いがどのように拡張されるかを記述する。

### 1.3 許容集合の広さと仕様の緩さ

この枠組みにおいて：

- **許容集合が広い** = 仕様が緩い = 細部を決めていない = 非決定性が高い
- **許容集合が狭い** = 仕様が厳密 = 実装の自由度が少ない

仕様の精密化（refinement）は、この許容集合を狭めていくプロセスとして理解できる。

## 2. トレース意味論（Trace Semantics）

### 2.1 トレースとしての振る舞い

プロセス代数において、トレース（trace）とはアクション（action）の列であり、システムが表現する振る舞いを表す。トレースの集合は、振る舞いの選択として解釈される可能な振る舞いの集合として理解できる。

参考: [Failure Trace Semantics for a Process Algebra with Time-outs](https://arxiv.org/html/2002.10814)

### 2.2 実装と仕様の関係

トレース構造は、実装と仕様の両方を表現する：

> **実装が仕様を満たす ⟺ 実装の可能なトレースの集合 ⊆ 仕様の可能なトレースの集合**

これは、許容集合モデルの数学的基盤である。実装は仕様よりも小さい（または等しい）振る舞いの集合を持たなければならない。

参考: [Process Algebra - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/process-algebra)

### 2.3 トレース意味論の限界

しかし、単純なトレース等価性には重要な限界がある：

- トレース等価性では `a.(b + c)` と `(a.b) + (a.c)` を区別できない
- 並行システムの意味論では、これらは本質的に異なる振る舞いである
- セキュリティやプライバシーなど、複数のトレースを関連付ける「ハイパープロパティ」は表現できない

参考: [Behavioral Equivalences Rocco De Nicola](http://staff.um.edu.mt/afra1/seminar/de-nic-beh-eq.pdf)

## 3. プロセス代数における仕様の集合論的定義

### 3.1 意味論の階層

プロセス代数は、2レベルの意味論を通じて数学的推論をサポートする：

1. **操作的意味論（Operational Semantics）**: 構造的操作規則により振る舞いを形式化
2. **振る舞い等価性（Behavioral Equivalences）**: 等価性を導入

最も研究されている3つのアプローチは：
- **双模倣（bisimulation）**
- **テスティング（testing）**
- **トレース（trace）**

参考: [Ready-trace semantics for concrete process algebra](https://dl.acm.org/doi/10.1093/comjnl/30.6.498)

### 3.2 振る舞い等価性の階層

振る舞い等価性には階層があり、それぞれ異なる粒度でシステムを区別する：

- **双模倣等価性（Bisimulation equivalence）**: 最も細かい等価性
- **トレース等価性（Trace equivalence）**: 最も粗い等価性

双模倣等価性は、トレースベースの等価性よりも細かくシステムを区別する。2つのプロセスが双模倣であれば、すべての等価性において等価である。

参考: [An Introduction to Bisimulation and Coinduction](https://homes.cs.washington.edu/~djg/msr_russia2012/sangiorgi.pdf)

## 4. リファインメント理論（Refinement Theory）

### 4.1 仕様の精密化と集合の包含

形式手法において、プログラム・リファインメント（program refinement）とは、抽象的な（高レベルの）形式仕様を、具体的な（低レベルの）実行可能プログラムへと検証可能な形で変換することである。

段階的リファインメント（stepwise refinement）により、このプロセスを段階的に行うことができる。

参考: [Refinement (computing) - Wikipedia](https://en.wikipedia.org/wiki/Refinement_(computing))

### 4.2 非決定性の削減と集合の縮小

リファインメントは、仕様における非決定性を削減し、典型的には完全に決定的な実装へと導く。例えば：

```
x ∈ {1,2,3}  →  x ∈ {1,2}  →  x ∈ {1}  →  x := 1
```

これは、集合の包含を用いて仕様を段階的に制約していく過程を示している。各リファインメントステップで、許容集合が狭くなっていく。

参考: [Refinement (computing) - Wikipedia](https://en.wikipedia.org/wiki/Refinement_(computing))

### 4.3 リファインメント代数

リファインメントとリファインメント代数は、形式仕様（通常は抽象的）をより具体的な表現へと変換するために使用される。最終的な目標は実装されたシステムである場合もあるが、リファインメントは異なる抽象レベルでのシステムの仕様を考察する際にも等しく有用である。

これにより、同じシステムの2つの表現が等価（または整合的）と見なせるかどうかを理解できる。

参考: [A Survey on Refinement in Formal Methods](https://www.researchgate.net/publication/336154810_A_Survey_on_Refinement_in_Formal_Methods_and_Software_Engineering)

## 5. CSPのFailures-Divergences Model

### 5.1 モデルの構成要素

CSP（Communicating Sequential Processes）のfailures-divergences意味論では、プロセスは3つ組 (A, F, D) でモデル化される：

- **A**: アルファベット（可能なイベントの集合）
- **F**: 失敗（failures）の集合
- **D**: 発散（divergences）の集合

参考: [Structural refinement in Object-Z / CSP](https://staff.itee.uq.edu.au/smith/papers/ifm2000-2.pdf)

### 5.2 Failuresの意味

プロセスのfailuresとは、対 (t, X) であり：
- **t**: プロセスが実行可能な有限のイベント列
- **X**: プロセスがtを実行した後に拒否可能なイベントの集合

Failure (s, X) ∈ F(P) は、プロセスPがsを実行した後にX内のどのイベントも拒否することを意味する。

### 5.3 Divergencesの意味

D(P) は発散集合である。発散 s ∈ D(P) は、Pがsを実行した後にカオス状態に入る実行トレースである。

### 5.4 リファインメント関係

CSPにおけるリファインメント関係は、集合の包含として定義される：

プロセスQがプロセスPをリファインする ⟺
- traces(Q) ⊆ traces(P)
- failures(Q) ⊆ failures(P)
- divergences(Q) ⊆ divergences(P)
- infinites(Q) ⊆ infinites(P)

これは、**リファインメント＝許容集合の縮小**という原則を明確に示している。

参考: [A Corrected Failure-Divergence Model for CSP](https://usr.lmf.cnrs.fr/~wolff/papers/conf/CSP.pdf)

### 5.5 CSPの意味論モデル

CSPには3つの主要な表示的意味論モデルがある：

1. **トレースモデル（Traces model）**: プロセスの意味を、観測可能なイベント列の集合として定義
2. **安定失敗モデル（Stable failures model）**: トレースに加えて、拒否集合を考慮
3. **失敗・発散モデル（Failures/divergences model）**: 最も精密なモデル

参考: [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)

## 6. デノテーショナル意味論における仕様

### 6.1 意味論的領域（Semantic Domains）

デノテーショナル意味論は、プログラミング言語の意味を形式化するアプローチであり、言語の式の意味を記述する数学的対象（表示、denotation）を構築する。

意味論的領域（semantic domains）は、デノテーショナル意味論で使用される値の集合である。

参考: [Denotational semantics - Wikipedia](https://en.wikipedia.org/wiki/Denotational_semantics)

### 6.2 集合論と領域理論

デノテーショナル意味論では、集合よりも**領域（domains）**が使用される。領域は通常、**完備半順序（complete partial orders, cpos）**であり、値の集合と特定の条件を満たす関係から構成される。

重要な要件は、デノテーショナル意味論がプログラミング言語の**合成性（compositionality）**を尊重することである。つまり、サブ項から構成される項の意味は、対応してこれらのサブ項の意味から構築される。

参考: [Denotational Semantics](https://people.cs.ksu.edu/~schmidt/text/DenSem-full-book.pdf)

### 6.3 仕様としての性質

性質（properties）自体も振る舞いの集合である。仕様が性質を満たすのは、仕様のすべての振る舞いがその性質の集合に含まれる場合である。

重要な点として、性質は仕様の外部の振る舞いを許可することができる。これは性質チェックを無効にするものではない。

参考: [Formal specs as sets of behaviors](https://surfingcomplexity.blog/2025/07/26/formal-specs-as-sets-of-behaviors/)

## 7. Abrial（B-Method）のリファインメント概念

### 7.1 B-Methodの概要

B-Methodは、Jean-Raymond Abrialによって1990年代初頭に導入され、以下を含む：

- **B言語**: 仕様記述言語
- **リファインメント手法**: 抽象化レベルの管理
- **証明手法**: リファインメントの満足性の検証

参考: [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)

### 7.2 集合論とリファインメント

B-Methodの特徴は以下の通り：

- **集合論によるモデリング**: システムを集合論で表現
- **リファインメントによる抽象化レベルの表現**: 異なる抽象化レベルでシステムを表現
- **数学的証明による整合性検証**: リファインメントレベル間の整合性を証明

参考: [Refinement and Reachability in Event_B](https://inria.hal.science/inria-00001245)

### 7.3 Abstract MachineとRefinement

最初の最も抽象的なバージョンは**Abstract Machine**と呼ばれ、設計の目標を指定する。次にリファインメントステップで、仕様を明確化するために詳細を追加したり、目標を達成する方法を定義するデータ構造やアルゴリズムの詳細を追加して、Abstract Machineをより具体的にする。

新しいバージョン（**Refinement**と呼ばれる）は、整合性があり、Abstract Machineのすべての性質を含むことを証明する必要がある。

参考: [The B-Method | SpringerLink](https://link.springer.com/chapter/10.1007/978-0-85729-277-3_19)

### 7.4 Correctness-by-Construction

B-Methodは、**正しさによる構築（correctness-by-construction）**パラダイムを体現している。システムは、高度に抽象的な数学的仕様から始まり、段階的に実行可能なコードへとリファインされる。安全性や機能的正しさなどの重要な性質が、各ステップで形式的証明により保持されることが保証される。

参考: [B-Method | Grokipedia](https://grokipedia.com/page/B-Method)

## 8. モデル指向仕様とプロパティ指向仕様

### 8.1 モデルベース仕様（Model-Based Specification）

モデルベース仕様は、システムの仕様をシステム状態モデルとして表現する形式仕様へのアプローチである。状態モデルは、集合や関数などの十分に理解された数学的実体を用いて構築される。

最も広く使用されているモデルベース仕様の表記法は、**VDM**と**Z**である。

参考: [Model-based specification - Wikipedia](https://en.wikipedia.org/wiki/Model-based_specification)

### 8.2 ZとVDMの特徴

- **Z**: 順次指向（sequential-oriented）、プロパティ指向（property-oriented）
- **VDM**: プロセス指向（process-oriented）、モデル指向（model-oriented）

両言語は類似した数学的基盤を使用し、モデルベース仕様技法を使用し、数学的表記法の大部分を共有している。

参考: [Comparison of Formal Specification Languages](https://www.iosrjournals.org/iosr-jce/papers/Vol11-issue5/G01153739.pdf)

### 8.3 状態ベースアプローチ

システムの操作は、システムモデルの状態にどのように影響するかを定義することで仕様化される。この状態ベースの視点は、両言語にとって基本的である。

VDMでは、各操作の事前条件を操作仕様の独立した構成要素として明示的に含める必要があるが、Zでは、操作を指定する単一の述語に暗黙的に含まれる。

参考: [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)

### 8.4 プロパティ指向仕様

プロパティ指向仕様は、抽象的なスタイルで与えられた形式仕様であり、システムの振る舞いは性質の集合によって定義される。これらの性質は、関数とソートを関連付ける公理によって与えられる。

参考: [Property-Oriented Specification | IGI Global](https://www.igi-global.com/dictionary/property-oriented-specification/60951)

## 9. 抽象解釈（Abstract Interpretation）

### 9.1 健全性（Soundness）

抽象解釈は、プログラムの意味論を健全に近似する理論であり、順序集合（特に束）上の単調関数に基づいている。

抽象意味関数が**健全（sound）**であるとは、具体的意味論を正しく近似することを意味する：

任意のプログラムPに対して、α([[P]]) ≤_A [[P]]♯

抽象解釈による静的解析は、一般的に「健全」に設計される。つまり、成立しない性質を確立すると主張してはならない。

参考: [Abstract interpretation - Wikipedia](https://en.wikipedia.org/wiki/Abstract_interpretation)

### 9.2 完全性（Completeness）

完全性は、理想的ではあるが稀な、抽象解釈の特徴である。抽象計算で蓄積される情報の損失がないという直感を形式化する。完全な抽象解釈は、最適と理解できる。

完全性は、抽象解釈器がすべての可能な入力に対して偽陽性（false alarms）を報告しないことを意味するが、非常に精密な解析が必要であるため、極めて稀である。

参考: [Completeness in Abstract Interpretation](https://www.math.unipd.it/~ranzato/papers/amast97.pdf)

### 9.3 束理論の基盤

具体的意味論領域は**完備束（complete lattice）**であると仮定される。具体領域と抽象領域は通常、完備束である。これにより、具体的意味論と抽象意味論の定義で使用される結合（join）と交差（meet）の基本的な束演算の存在が保証される。

**ガロア接続（Galois connection）**は、α : C → A と γ : A → C の関数の対が形成され、すべての c ∈ C, a ∈ A に対して、α(c) ≤_A a ⟺ c ≤ γ(a) が成立する。

参考: [Abstract Interpretation Frameworks](https://faculty.sist.shanghaitech.edu.cn/faculty/songfu/cav/AIF.pdf)

## 10. 非決定性（Nondeterminism）と仕様の緩さ

### 10.1 仕様における非決定性の役割

仕様を書く際、非決定性を利用して「ここに、この振る舞いを妥当に拡張できるすべての異なる方法がある」と表現し、すべての可能な正しい振る舞いを生成する。

設計者は、非決定性を利用して複数の正しいシステム仕様を許可し、それによってシステムが動作する環境の振る舞いに関する仮定を緩和できる。

参考: [Nondeterminism in Formal Specification](https://buttondown.com/hillelwayne/archive/nondeterminism-in-formal-specification/)

### 10.2 非決定性の種類

形式手法における非決定性には複数の種類がある：

1. **Choice（erratic）nondeterminism**: 選択的非決定性
2. **Backtrack（demonic）nondeterminism**: 悪魔的非決定性
3. **Unbounded（angelic）nondeterminism**: 天使的非決定性
4. **Loose nondeterminism**: 緩い非決定性

参考: [Five Kinds of Nondeterminism](https://buttondown.com/hillelwayne/archive/five-kinds-of-nondeterminism/)

### 10.3 天使的・悪魔的非決定性

プログラムは、天使（angel）と悪魔（demon）という2つのエージェント間の契約と見なすことができる：

- **天使的非決定性（Angelic nondeterminism）**: 選択が天使（この場合はマシン）によって行われ、天使は我々に有利な最良の結果を選択すると仮定される
- **悪魔的非決定性（Demonic nondeterminism）**: 選択が悪魔（外部ユーザー）によって行われる

参考: [Programming with angelic nondeterminism](https://dl.acm.org/doi/10.1145/1706299.1706339)

### 10.4 抽象化としての非決定性

仕様言語における非決定性は、プログラミング言語とは異なる使い方をされる。ランダム性や並行性から生じるのではなく、**抽象化の手段**として機能する。

例えば、パスワード検証のすべての詳細をモデル化する代わりに、非決定性を使用して、正しさがどのように決定されるかを指定せずに、ログインの成功または拒否のいずれかを表現できる。

参考: [Nondeterminism in Formal Specification](https://buttondown.com/hillelwayne/archive/nondeterminism-in-formal-specification/)

### 10.5 仕様の緩さ（Specification Looseness）

非決定性を使用して許容可能な振る舞いを拡張すると、仕様は「緩い（loose）」状態になる：

- **緩い仕様**: 多くの異なる実装を許可する（許容集合が広い）
- **厳密な仕様**: 実装の選択肢が少ない（許容集合が狭い）

より高い設計レベルでは、実装の詳細を気にしない場合があり、特定の条件が発生した場合に何が起こるかだけをモデル化し、非決定性を使用してこの抽象化を処理する。

参考: [Formal Methods](https://users.ece.cmu.edu/~koopman/des_s99/formal_methods/)

## 11. このモデルの限界と批判

### 11.1 トレース意味論の表現力の限界

トレース意味論には、重要な表現力の限界がある：

#### 11.1.1 オプションと必須の区別

単純なトレース集合意味論は、オプションの振る舞いと必須の振る舞いを区別する表現力を持たない。これは、仕様におけるこれらの異質な混合がサポートされないことを意味する。

参考: [Triggered Message Sequence Charts](https://www.researchgate.net/publication/3189679_Triggered_Message_Sequence_Charts)

#### 11.1.2 ハイパープロパティの表現不可能性

従来のLTL（線形時相論理）は、個々の実行のトレース性質のみを表現できる。セキュリティ、プライバシー、特定の一貫性要件は「ハイパープロパティ」であり、複数のトレースを関連付ける。これらはトレースのクラスとして表現できない。

参考: [Misconceptions in Finite-Trace and Infinite-Trace Linear Temporal Logic](https://link.springer.com/chapter/10.1007/978-3-031-71162-6_30)

#### 11.1.3 タイミング制約の表現困難

LTLは以下の制約を表現できない：

- 固定数でのモジュロカウント
- タイミング境界の適切な表現（例：すべてのリクエストが一定時間内に応答を受け取る必要がある場合）

Metric Temporal Logic（MTL）も、構文的または意味論的な制限がある（例：有界な未来様相のみを許可、整数時間の仮定）。

参考: [On the Expressiveness and Monitoring of Metric Temporal Logic](https://lmcs.episciences.org/5447/pdf)

### 11.2 非決定性の扱いにくさ

Waynは、仕様における非決定性に関する2つの主要な課題を指摘している：

#### 11.2.1 能力vs扱いやすさ

> 「非決定性は非常に能力が高いため、あまり扱いやすくない」

これにより、条件付き性質の表現が困難になる。例えば、特定の非決定的な結果が発生しない場合に何が起こるかを表現することが難しい。

#### 11.2.2 実装ギャップ

抽象化としての非決定性は、仕様と実際のコード間の距離を生み出し、実装が仕様と一致することを検証することが困難になる。

参考: [Nondeterminism in Formal Specification](https://buttondown.com/hillelwayne/archive/nondeterminism-in-formal-specification/)

### 11.3 CTL（Computation Tree Logic）の限界

CTLは、時相性質仕様言語としていくつかの根本的な制限がある：

- 言語が直感的でなく、使用が困難
- 合成的推論に適していない
- 半形式検証と根本的に非互換

参考: [Branching vs. Linear Time: Semantical Perspective](https://www.cs.rice.edu/~vardi/papers/atva0711.pdf)

### 11.4 過小仕様（Underspecification）の問題

過小仕様とは、仕様の様々な要素が不完全または不十分に正確であることを意味する。

形式手法のコンテキストでは、過小仕様と固有の非決定性は、演算子（altは過小仕様用、xaltは固有の非決定性用）によって構文的に、そして相互作用義務の集合によって意味論的にサポートされる。

トレースの集合として定義された仕様は、システム振る舞いのすべてのニュアンス、特に必須の振る舞いと単に許容される振る舞いの区別を完全に表現できないという限界がある。

参考: [Underspecification - Wikipedia](https://en.wikipedia.org/wiki/Underspecification)

### 11.5 形式手法における厳密性と表現力のトレードオフ

厳密性の必要性とすべての振る舞いをモデル化する能力との間には、顕著なトレードオフがある。これは、形式的精度を維持しながら仕様の緩さを表現するという課題に関連している。

参考: [Formal Methods](https://users.ece.cmu.edu/~koopman/des_s99/formal_methods/)

## 12. 学術的根拠のまとめ

### 12.1 仕様＝許容集合モデルの理論的基盤

仕様を「許容される振る舞いの集合」として捉えるモデルは、以下の複数の理論的基盤により裏付けられている：

1. **トレース意味論**: 実装⊆仕様という包含関係
2. **プロセス代数**: 振る舞い等価性の階層
3. **CSPのfailures-divergences model**: リファインメント＝集合の包含
4. **リファインメント理論**: 非決定性の削減＝許容集合の縮小
5. **デノテーショナル意味論**: 意味論的領域としての振る舞い集合
6. **B-Method**: 集合論に基づくリファインメント
7. **抽象解釈**: 具体領域と抽象領域の束構造

### 12.2 許容集合の広さと仕様の緩さの対応

以下のように対応する：

| 許容集合の特性 | 仕様の特性 | 非決定性 | 実装の自由度 |
|----------------|------------|----------|--------------|
| 広い | 緩い | 高い | 大きい |
| 狭い | 厳密 | 低い | 小さい |

リファインメントは、許容集合を段階的に狭めていくプロセスである。

### 12.3 このモデルの利点

- **数学的厳密性**: 集合論による明確な定義
- **合成性**: 部分仕様の組み合わせが可能
- **検証可能性**: 包含関係の検証により実装の正しさを証明
- **抽象化**: 非決定性により実装詳細を隠蔽

### 12.4 このモデルの限界

- **表現力の制約**: トレースだけでは表現できない性質（ハイパープロパティなど）
- **非決定性の扱いにくさ**: 高い能力と引き換えに扱いが困難
- **オプションと必須の区別困難**: 単純なトレース集合では区別不可能
- **実装ギャップ**: 抽象的な仕様と具体的なコード間の距離

## 13. 結論

仕様を「許容される振る舞いの集合」として捉え、その集合の広さが仕様の緩さに対応するというモデルは、形式手法とプロセス代数の分野において確固たる理論的基盤を持つ。

トレース意味論、リファインメント理論、CSPのfailures-divergences model、B-Methodなど、複数の形式体系がこのモデルを支持している。リファインメントは集合の包含として、非決定性は許容集合の広さとして、厳密に定義される。

しかし、このモデルには限界もある。単純なトレース集合では、ハイパープロパティやオプション/必須の区別などを表現できない。非決定性は強力だが扱いにくく、抽象仕様と具体実装の間にギャップを生じさせる。

現代の形式手法は、これらの限界を克服するために、より表現力の高い時相論理、天使的・悪魔的非決定性の区別、ゲーム意味論などを導入している。

仕様＝許容集合モデルは、形式仕様の本質を捉える有用な抽象化であるが、実際の仕様記述では、このモデルの限界を理解し、適切な拡張を用いることが重要である。

## 参考文献

### トレース意味論・プロセス代数
- [Process Algebra - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/process-algebra)
- [Failure Trace Semantics for a Process Algebra with Time-outs](https://arxiv.org/html/2002.10814)
- [Ready-trace semantics for concrete process algebra](https://dl.acm.org/doi/10.1093/comjnl/30.6.498)
- [Behavioral Equivalences Rocco De Nicola](http://staff.um.edu.mt/afra1/seminar/de-nic-beh-eq.pdf)
- [An Introduction to Bisimulation and Coinduction](https://homes.cs.washington.edu/~djg/msr_russia2012/sangiorgi.pdf)

### リファインメント理論
- [Refinement (computing) - Wikipedia](https://en.wikipedia.org/wiki/Refinement_(computing))
- [A Survey on Refinement in Formal Methods](https://www.researchgate.net/publication/336154810_A_Survey_on_Refinement_in_Formal_Methods_and_Software_Engineering)
- [Formal methods - Wikipedia](https://en.wikipedia.org/wiki/Formal_methods)

### CSP
- [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)
- [Structural refinement in Object-Z / CSP](https://staff.itee.uq.edu.au/smith/papers/ifm2000-2.pdf)
- [A Corrected Failure-Divergence Model for CSP](https://usr.lmf.cnrs.fr/~wolff/papers/conf/CSP.pdf)
- [Communicating Sequential Processes, by C. A. R. Hoare](http://www.usingcsp.com/)

### デノテーショナル意味論
- [Denotational semantics - Wikipedia](https://en.wikipedia.org/wiki/Denotational_semantics)
- [Denotational Semantics](https://people.cs.ksu.edu/~schmidt/text/DenSem-full-book.pdf)

### B-Method
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [The B-Method | SpringerLink](https://link.springer.com/chapter/10.1007/978-0-85729-277-3_19)
- [Refinement and Reachability in Event_B](https://inria.hal.science/inria-00001245)
- [B-Method | Grokipedia](https://grokipedia.com/page/B-Method)

### モデル指向仕様
- [Model-based specification - Wikipedia](https://en.wikipedia.org/wiki/Model-based_specification)
- [Comparison of Formal Specification Languages](https://www.iosrjournals.org/iosr-jce/papers/Vol11-issue5/G01153739.pdf)
- [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)
- [Property-Oriented Specification | IGI Global](https://www.igi-global.com/dictionary/property-oriented-specification/60951)

### 抽象解釈
- [Abstract interpretation - Wikipedia](https://en.wikipedia.org/wiki/Abstract_interpretation)
- [Completeness in Abstract Interpretation](https://www.math.unipd.it/~ranzato/papers/amast97.pdf)
- [Abstract Interpretation Frameworks](https://faculty.sist.shanghaitech.edu.cn/faculty/songfu/cav/AIF.pdf)

### 非決定性
- [Formal specs as sets of behaviors – Surfing Complexity](https://surfingcomplexity.blog/2025/07/26/formal-specs-as-sets-of-behaviors/)
- [Nondeterminism in Formal Specification](https://buttondown.com/hillelwayne/archive/nondeterminism-in-formal-specification/)
- [Five Kinds of Nondeterminism](https://buttondown.com/hillelwayne/archive/five-kinds-of-nondeterminism/)
- [Programming with angelic nondeterminism](https://dl.acm.org/doi/10.1145/1706299.1706339)
- [Formal Methods](https://users.ece.cmu.edu/~koopman/des_s99/formal_methods/)

### 限界と批判
- [Triggered Message Sequence Charts](https://www.researchgate.net/publication/3189679_Triggered_Message_Sequence_Charts)
- [On the Expressiveness and Monitoring of Metric Temporal Logic](https://lmcs.episciences.org/5447/pdf)
- [Misconceptions in Finite-Trace and Infinite-Trace Linear Temporal Logic](https://link.springer.com/chapter/10.1007/978-3-031-71162-6_30)
- [Branching vs. Linear Time: Semantical Perspective](https://www.cs.rice.edu/~vardi/papers/atva0711.pdf)
- [Underspecification - Wikipedia](https://en.wikipedia.org/wiki/Underspecification)
