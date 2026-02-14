# プロセス代数と並行システムの仕様

## 1. はじめに

プロセス代数（Process Algebra）は、並行システムにおけるプロセス間の相互作用、通信、同期を形式的にモデル化するための数学的枠組みの総称である。1970年代後半から1980年代にかけて、Robin MilnerのCCS（Calculus of Communicating Systems）やTony HoareのCSP（Communicating Sequential Processes）などが登場し、並行計算理論の基礎が確立された。

プロセス代数は、独立したエージェントやプロセスの集まりが、メッセージ通信やチャネルを通じて相互作用する様子を高レベルで記述するツールを提供する。これにより、並行システムの仕様を明確に表現し、デッドロックやライブロックなどの性質を形式的に検証することが可能になる。

## 2. 主要なプロセス代数

### 2.1 CSP（Communicating Sequential Processes）

CSPは、Tony Hoareにより1978年に発表された並行システムの形式言語である。CSPは、チャネルを通じたメッセージパッシングに基づくプロセス代数の一員であり、並行システムにおける相互作用のパターンを記述する。

**歴史的発展**：
- 1978年の原論文では、CSPは本質的に並行プログラミング言語として提示された
- 当初のバージョンは数学的に定義された意味論を持たず、無限非決定性を表現できなかった
- 1984年にBrookes、Hoare、Roscoeによる理論版が発表され、1985年にHoareの著書『Communicating Sequential Processes』が出版された
- 2006年時点で、この著書はコンピュータサイエンス分野で3番目に引用された文献となっている

**主な特徴**：
- 固定数の順序プロセスの並列合成としてプログラムを記述
- プロセス間の厳密な同期メッセージパッシング
- 動的な振る舞いのモデリングに有効
- Z、B、VDMなどの仕様記述言語との統合（CSP-Z、CSP-OZ、TCOS、B+CSPなど）

**意味論モデル**：
- **トレース意味論（Traces）**：プロセスが実行可能な通信の系列を記録
- **失敗意味論（Failures）**：トレースに加え、プロセスが拒否可能なイベント集合を記録
- **発散意味論（Divergences）**：ライブロックや無限内部動作を捉える

**産業応用**：
- T9000 Transputer の仕様と検証
- セキュアなeコマースシステムの設計
- ハードウェア、OS、ミドルウェア、プログラミング言語、アプリケーションなど幅広い分野への適用

### 2.2 CCS（Calculus of Communicating Systems）

CCSは、Robin Milnerにより1973年から1980年にかけて開発されたプロセス計算である。プロセス計算の研究はMilnerのCCSに関する先駆的研究から本格的に始まった。

**中核概念**：
- 2つの参加者間の不可分な通信としてアクションをモデル化
- 並列合成、アクション間の選択、スコープ制限を記述する原始演算子
- ラベル付き遷移システム（Labelled Transition System）として言語の式を解釈
- ビシミュレーション（Bisimulation）を意味的等価性として使用

**主な用途**：
- デッドロックやライブロックなどシステム特性の定性的正当性の評価
- 通信システムの仕様記述と性質の検証

**CSPとの関係**：
- CSPとCCSは多くの共通目標を持ち、開発過程で相互に影響を与え合った
- 両者とも並行システムのモデリング、仕様記述、検証の実用ツールとして産業界に大きな影響を与えた

### 2.3 ACP（Algebra of Communicating Processes）

ACPは、Jan BergstraとJan Willem Klopにより1982年に開発された、並行システムについて推論するための代数的アプローチである。これは、無防御再帰方程式の解を調査する試みの一環として初期開発された。

**主要演算子**：
- **マージ演算子（Merge）**：2つのプロセスの並列合成を表現し、個々のアクションはインターリーブされる
- **左マージ演算子（Left-merge）**：マージと類似の意味論を持つが、常に左側プロセスから初期ステップを選択する
- 基本プロセス代数、並行性、通信を提供する演算子群

**インターリーブ意味論**：
ACPでは、並列プロセスは任意の方法でインターリーブされると考えられる。ビシミュレーションはインターリーブ意味論と呼ばれ、プロセス内の演算子をACPの公理を用いた推論により除去できる。

### 2.4 π計算（Pi-Calculus）

π計算は、Robin Milner、Joachim Parrow、David Walkerにより1980年代後半に開発され、CCSをチャネル名の移動性で拡張したプロセス計算である。

**主な特徴**：
- チャネル名自体をチャネル経由で通信可能
- 計算中にネットワーク構成が変化する並行計算を記述可能
- プロセスの動的生成と削除が可能で、動的システムのモデリングに適している
- **チャネル移動性（Channel Mobility）**：チャネル名をメッセージとして送受信可能

**表現力と応用**：
- π計算は万能な計算モデルである
- Milnerの論文「Functions as Processes」でλ計算の2つのエンコーディングが提示された
- 理論研究の枠を超え、Business Process Modeling Language（BPML）やMicrosoftのXLANGの理論的基盤となっている

### 2.5 LOTOS（Language of Temporal Ordering Specification）

LOTOSは、イベントの時間的順序付けに基づく形式仕様言語であり、ISO/OSIモデルにおける通信プロトコル仕様記述に使用される。

**構造と構成要素**：
- **データと操作の記述部分**：抽象データ型に基づく（ACT ONE抽象データ型形式主義）
- **並行プロセスの記述部分**：プロセス計算に基づく（MilnerのCCSの拡張版）

**標準化と発展**：
- 1988年に作業が完了し、1989年にISO 8807として公開
- 1993年から2001年にかけてLOTOS標準の改訂版が定義され、2001年にE-LOTOSとして公開

**用途**：
- OSIアーキテクチャおよび一般的な分散システムの形式記述のために開発
- 明確に定義された操作的意味論を持ち、正しいLOTOS仕様をラベル付き遷移システムに一意にマッピング
- 初期抽象仕様から実装に近い形式へのステップワイズ精密化が可能

## 3. 並行性の意味論

### 3.1 インターリーブ意味論

インターリーブ意味論は、真の並行意味論（true-concurrency semantics）の対極にある伝統的な並行システムモデリングアプローチである。この意味論では、2つのイベントが厳密に同時に発生することはなく、並列プロセスは任意のレートで各アクションの実行を交互に行うことで進行する。

**特徴**：
- 最も単純な並列合成演算子
- 2つの並列プロセスが任意のレートでアクションの実行を交互に行うことをモデル化
- CSP、CCS、ACPなどの主要なプロセス代数で採用

### 3.2 真の並行性と部分順序意味論

真の並行性（True Concurrency）は、イベントが実際に同時に発生する可能性を認める並行モデルである。部分順序意味論は、真の並行性を捉えるために使用される。

**意義と応用**：
- **セキュリティ解析**：分散システムの振る舞いを分散計算モデル（ペトリネットなど）で記述し、真の並行行動意味論で観察する必要がある
- すべての可能な情報フローを捉えるため、観測意味論は非常に具体的である必要がある
- 発生したイベントの部分順序だけでなく、分散状態の構造も観察する（fully-concurrent bisimilarity、team equivalence、state-sensitive fully-concurrent bisimilarity、structure-preserving bisimilarityなど）

**インターリーブ意味論との比較**：
- 行動等価性は、インターリーブから真の並行性へ、線形時間から分岐時間へと分散される
- 真の並行意味論は主にアルゴリズム目的で使用される
- 決定可能性問題はPSPACE完全であり、インターリーブ意味論を計算しない手続きが存在する

**ペトリネット**：
並行性を真に表現できるモデルとして、ペトリネット（1962年にCarl Adam Petriが発表）がある。ペトリネットにおいて、2つの動作がそれぞれ実行可能ならば独立して実行可能であり、「独立」とは一方の動作の実行が他方の動作の実行可能性に影響を与えないことを意味する。

## 4. 等価性と検証の概念

### 4.1 ビシミュレーション（Bisimulation）

ビシミュレーションは、2つのプロセスが観察下で区別不可能な相互作用系列を示す場合を捉える正準的等価性である。

**種類**：
- **強ビシミュレーション（Strong Bisimulation）**：CCSにおける正準的等価性
- **弱ビシミュレーション（Weak Bisimulation）**：観察等価性とも呼ばれ、対応する原子アクションの前後に任意の無音ステップ（τ遷移）系列を許可する

**特性**：
- ビシミュレーション等価性は最も細かい等価性
- トレース等価性は最も粗い等価性
- パーティション精密化アルゴリズムにより決定可能

### 4.2 トレース等価性

トレース等価性は、2つのプロセスが同じトレース集合（可能な通信系列）を持つ場合に成立する等価性である。

**用途**：
- 安全性性質（Safety Properties）の証明に使用される
- プロセスQがプロセスPのトレース精密化である場合、Qが実行可能なすべての通信系列はPでも可能である

### 4.3 観測等価性とテスト等価性

**観測等価性（Observational Equivalence）**：
- 2つのプログラムがすべての可能な文脈で同じ振る舞いを示すかどうかで定義
- 特別な観測不可能アクションτを抽象化する
- 弱ビシミュレーション等価性と一致する

**テスト等価性（Testing Equivalence）**：
- トレース、拒否、コピー、グローバルテストなどの形式を含む
- 観測等価性と一致することが示されている

### 4.4 失敗・発散モデル

**失敗（Failure）**：
- 失敗は対(s, X)であり、sはプロセスのトレース、Xはプロセスがその時点で拒否可能なイベント集合
- Xは拒否（refusal）と呼ばれる

**発散（Divergence）**：
- 失敗・発散モデルは、ライブロックや無限内部アクションを捉えるために発散概念を追加
- 安全性、活性、組み合わせ性質の証明、システム間の精密化と等価関係の確立に使用される

### 4.5 デッドロックフリー性

**CSPにおける拒否テスト**：
- プロセスがトレース後に特定のイベントを拒否できることを検証
- 並行設計におけるデッドロックフリー性などの性質を保証

**型システムとプロセス計算**：
- プロセス計算は、プログラミング言語における検証技術、特に行動等価性を活用してデッドロックフリー性を保証する型システムに影響を与える

## 5. プロセス代数の合成と並列演算子

### 5.1 並列合成演算子

並列合成は、複数の計算プロセスまたはコンポーネントを組み合わせ、システム内で並行動作させる方法である。通常、演算子「||」で表現される。

**種類**：
- **アルファベット化並列合成（Alphabetised Parallel Composition, M1 || M2）**：両モジュールに現れるアクションのみで同期
- **非同期並列合成（Asynchronous Parallel Composition, M1 ||| M2）**：同期なしで完全にインターリーブ
- **制限付き並列合成（Restricted Parallel Composition, M1 |[a,b,...]| M2）**：指定された集合のアクションのみで同期

### 5.2 基本演算子

プロセス代数は、基本的なアクションと以下の演算子に基づく：
- **+（代替合成または選択）**：Choice
- **·（順次合成または積）**：Sequential Composition
- **||（並列合成またはマージ）**：Parallel Composition

### 5.3 同期とインタフェース

**並列合成と同期**：
- 並列合成により、計算は同時かつ独立に進行可能
- 同期と情報フローによる相互作用も許可される

**接続部（インタフェース）の問題**：
- マルチエージェントモデルでは、システムを並行動作する複数の部品（エージェント）に分割し、通信により結合
- プロセス代数は並行動作するエージェントの動作解析のための数学的枠組を提供
- ブロードキャスト通信方式など、エージェント間の接続様式が重要

## 6. 検証ツールとモデル検査

### 6.1 FDR（Failures-Divergences Refinement）

FDRは、CSPで表現された形式モデルを検査するために設計された精密化検査ソフトウェアツールである。

**発展**：
- FDR、FDR2、FDR3、FDR4へと進化
- FDR3は並列精密化検査器

**精密化モデル**：
- **トレース精密化（Traces Refinement）**：安全性性質の証明に使用
- **失敗・発散精密化（Failures-Divergences Refinement）**：安全性、活性、組み合わせ性質の証明、精密化と等価関係の確立に使用

**精密化検査アルゴリズム**：
- 実装で即座に可能なイベントは、仕様でも可能でなければならない
- すべてのトレースと拒否が仕様に含まれることを確認

### 6.2 並行システムのCSPによる検証技術

**日本におけるアプローチ**：
- 並行システムのCSPによるモデル化技術
- モデル検査器FDRによる検証技術
- JCSPによる実装技術

## 7. プロセス代数の実用応用

### 7.1 並行システムの解析

**プロセス生成機能を持つ並行システム**：
- アクティブデータベースシステムのように、子プロセスを生成してプロセス木を構築
- 親プロセスと子プロセス間でマルチウェイ局所通信が可能な並行システムの解析

### 7.2 ブロードキャストシステム

マルチエージェントモデルにおいて、ブロードキャスト的な通信方式が有効であり、プロセス代数はエージェントの動作解析のための数学的枠組として活用される。

### 7.3 ビジネスプロセスモデリング

ビジネスプロセスモデルのために提案されている記法や言語は、ペトリネット、オートマトン、プロセス代数といった技術に基礎を置いている。

**BPELの形式化**：
- プロセス代数CCSによるBPEL（Business Process Execution Language）の形式化

### 7.4 暗号プロトコル検証

暗号セキュリティ定義の多くは、観測等価性プロパティとして自然に定式化できる。Tamarinなどのツールは、可変状態、無制限セッション、等式理論を持つプロトコルの観測等価性を証明するために拡張されている。

## 8. まとめと考察

プロセス代数は、並行システムの仕様記述と検証のための強力な理論的基盤を提供する。CSP、CCS、ACP、π計算、LOTOSなど、様々なプロセス代数が開発され、それぞれ異なる特徴と応用領域を持つ。

**主要な貢献**：
- **形式的意味論**：並行システムの振る舞いを厳密に定義
- **等価性概念**：ビシミュレーション、トレース等価性、観測等価性などによるプロセス間の関係を明確化
- **検証技術**：FDRなどのツールによるモデル検査と精密化検査
- **産業応用**：ハードウェア、通信プロトコル、セキュリティシステム、ビジネスプロセスなど幅広い分野での実用化

**並行システム仕様の課題**：
- **並行性の意味論**：インターリーブ意味論と真の並行性（部分順序意味論）の選択
- **合成問題**：並列する宇宙（プロセス）の結合や接続部（インタフェース）の仕様化
- **状態空間爆発**：並行システムの状態空間は指数的に増大し、検証が困難になる
- **表現力と決定可能性のトレードオフ**：より表現力の高いモデルは検証が困難になる

**仕様の階層性との関係**：
- プロセス代数における精密化（refinement）概念は、抽象仕様から具体実装への段階的変換を支援
- 異なる抽象レベルでの仕様記述が可能で、「多層宇宙」的な仕様構造を構築できる
- 局所的仕様（個々のプロセス）と大域的性質（システム全体のデッドロックフリー性など）の関係が重要

プロセス代数は、並行システムという複雑な対象を扱うための数学的言語として、今後も発展を続けるであろう。特に、分散システム、モバイル計算、セキュリティプロトコルなどの現代的課題に対して、プロセス代数の理論と技術は不可欠な役割を果たしている。

## 参考文献

- [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)
- [Process calculus - Wikipedia](https://en.wikipedia.org/wiki/Process_calculus)
- [The Pi Calculus | The n-Category Café](https://golem.ph.utexas.edu/category/2009/08/the_pi_calculus.html)
- [CSP: a practical process algebra (PDF)](https://www.cs.ox.ac.uk/files/12724/cspfdrstory.pdf)
- [A gentle introduction to Process Algebras (PDF)](https://www.pst.ifi.lmu.de/Lehre/fruhere-semester/sose-2013/formale-spezifikation-und-verifikation/intro-to-pa.pdf)
- [Concurrency: 2025-2026 - Oxford](https://www.cs.ox.ac.uk/teaching/courses/2025-2026/concurrency/)
- [プロセス計算 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%97%E3%83%AD%E3%82%BB%E3%82%B9%E8%A8%88%E7%AE%97)
- [並行システムの検証と実装 (AIST)](https://staff.aist.go.jp/y-isobe/topse/vic/preface-text.pdf)
- [CSP-Consortium CSPとは](http://www.csp-consortium.org/csp/)
- [ペトリネット理論 (PDF)](http://www.jaist.ac.jp/is/labs/hira-lab/old_home_page/Petrinet.pdf)
- [Algebra of communicating processes - Wikipedia](https://en.wikipedia.org/wiki/Algebra_of_communicating_processes)
- [Algebra of Communicating Processes (PDF)](https://ir.cwi.nl/pub/1778/1778D.pdf)
- [Non Interleaving Process Algebra (PDF)](https://www.researchgate.net/profile/Jos-Baeten/publication/220701017_Non_Interleaving_Process_Algebra/links/604a120da6fdcc4d3e561fde/Non-Interleaving-Process-Algebra.pdf)
- [A Calculus of Mobile Processes (PDF)](https://www.cis.upenn.edu/~stevez/cis670/pdfs/pi-calculus.pdf)
- [The π-calculus: A Theory of Mobile Processes](https://www.khoury.northeastern.edu/home/riccardo/papers/sangiorgi-pi-calc.pdf)
- [π-calculus - Wikipedia](https://en.wikipedia.org/wiki/%CE%A0-calculus)
- [Language of Temporal Ordering Specification - Wikipedia](https://en.wikipedia.org/wiki/Language_Of_Temporal_Ordering_Specification)
- [E-LOTOS: Enhanced Language Of Temporal Ordering Specification](https://link.springer.com/chapter/10.1007/978-1-4471-0701-9_10)
- [Basic process algebra with deadlocking states](https://www.sciencedirect.com/science/article/pii/S0304397500002905)
- [Process Algebra: Specification and Verification in Bisimulation Semantics (PDF)](https://files01.core.ac.uk/download/pdf/301634525.pdf)
- [Interleaving vs True Concurrency: Some Instructive Security Examples](https://link.springer.com/chapter/10.1007/978-3-030-51831-8_7)
- [Partial order semantics versus interleaving semantics for CSP-like languages](https://link.springer.com/chapter/10.1007/3-540-13345-3_37)
- [FDR (software) - Wikipedia](https://en.wikipedia.org/wiki/FDR_(software))
- [FDR2 User Manual: CSP Refinement](https://www.cs.ox.ac.uk/projects/concurrency-tools/fdr-2.94-html-manual/fdr2manual_5.html)
- [FDR3 — A Modern Refinement Checker for CSP (PDF)](https://www.cs.ox.ac.uk/files/6001/Document.pdf)
- [Refinement Checking — FDR 4.2.7 documentation](https://cocotec.io/fdr/manual/implementation/refinement_checking.html)
- [PRISM Manual | The PRISM Language / Process Algebra Operators](https://www.prismmodelchecker.org/manual/ThePRISMLanguage/ProcessAlgebraOperators)
- [Parallel Composition - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/parallel-composition)
- [Observational Equivalence - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/observational-equivalence)
- [Observation equivalence as a testing equivalence](https://www.sciencedirect.com/science/article/pii/030439758790065X)
- [Calculus of communicating systems - Wikipedia](https://en.wikipedia.org/wiki/Calculus_of_communicating_systems)
- [A Calculus of Communicating Systems](https://link.springer.com/book/10.1007/3-540-10235-3)
- [Communicating Sequential Processes (Hoare, 1978) (PDF)](https://www.cs.cmu.edu/~crary/819-f09/Hoare78.pdf)
- [Communicating Sequential Processes (Hoare's book) (PDF)](http://www.usingcsp.com/cspbook.pdf)
- [プロセス代数によるプロセス生成機能をもつ並行システムの解析](https://cir.nii.ac.jp/crid/1570009752155042816)
- [プロセス代数とその応用(1) 形式仕様とプロセス代数](http://jglobal.jst.go.jp/public/20090422/200902013396181394)
