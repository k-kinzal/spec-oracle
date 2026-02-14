# 制約プログラミングと仕様記述

## 概要

制約プログラミング(Constraint Programming, CP)は、問題を変数、定義域、制約の三つ組として宣言的に記述し、制約ソルバーが解を自動探索するプログラミングパラダイムである。仕様記述の観点から見ると、制約プログラミングは「何を満たすべきか」を記述し「どう解くか」をソルバーに委ねる純粋に宣言的なアプローチであり、仕様記述の理想形の一つとして位置づけられる。本文書では、制約プログラミングと仕様記述の深い関係、理論的基盤、実用ツール、産業応用について調査する。

## 1. 制約充足問題(CSP)の形式的定義

### 1.1 CSPの基本構成要素

[制約充足問題](https://en.wikipedia.org/wiki/Constraint_satisfaction_problem)は形式的に以下の三つ組として定義される：

- **変数(Variables)**: X = {X₁, X₂, ..., Xₙ}
- **定義域(Domains)**: D = {D₁, D₂, ..., Dₙ}、各Dᵢは変数Xᵢが取り得る値の集合
- **制約(Constraints)**: C = {C₁, C₂, ..., Cₘ}、各制約は変数の部分集合上の許容可能な値の組み合わせを定義する関係

CSPの目的は、すべての制約を同時に満たすように、各変数にその定義域から値を割り当てることができるかを決定することである。完全割当て(complete assignment)がすべての制約を満たすとき、それは解(solution)と呼ばれる。

### 1.2 制約の分類

[制約の種類](https://www.geeksforgeeks.org/artificial-intelligence/constraint-satisfaction-problems-csp-in-artificial-intelligence/)には以下のような分類がある：

- **単項制約(Unary Constraints)**: 単一の変数に関する制約
- **二項制約(Binary Constraints)**: 2つの変数間の関係を定義する制約。二項CSPは各制約が高々2つの変数に関係する問題
- **非二項制約(Non-Binary Constraints)**: 3つ以上の変数に関係する制約
- **ハード制約(Hard Constraints)**: 厳密に満たされなければならない制約
- **ソフト制約(Soft Constraints)**: 違反可能だがコストが発生する制約。現実世界の応用でよく用いられる

### 1.3 制約最適化問題(COP)

[制約最適化問題](https://en.wikipedia.org/wiki/Constrained_optimization)はCSPを一般化したもので、制約充足に加えて最適化すべき目的関数を持つ。最小化(最大化)COPの最適解は、目的関数の値を最小化(最大化)する解である。目的関数は最小化すべきコスト関数やエネルギー関数、または最大化すべき報酬関数や効用関数となる。

## 2. 制約プログラミングの宣言的性質と仕様記述

### 2.1 宣言的仕様としての制約

[制約プログラミングの本質](https://www.constraint.org/ja/intro/)は、問題の要素を変数として定義し、それらの変数間に存在する制約条件を宣言的に記述することである。この宣言的記述には以下の特徴がある：

- **処理の方向が固定されない**: 「XからYを計算する」のではなく「XとYの関係」を記述する
- **特定の解き方を前提としない**: 解くべき問題の記述に専念できる
- **コードが簡潔で分かりやすい**: 問題の本質が明確に表現される
- **問題の変更に柔軟に対応**: 制約の追加・削除が容易

仕様記述の観点から見ると、制約プログラミングは**仕様と実装の区別が極めて明確**である。制約の集合が仕様であり、制約ソルバーによる探索が実装である。

### 2.2 制約仕様の表現力と曖昧性の排除

[モデルベースソフトウェア工学における制約言語](https://link.springer.com/article/10.1007/s10270-020-00796-4)の研究によると、制約仕様は以下の利点を持つ：

- **曖昧性の排除**: 制約は透明な意味論を持ち、特定ツールの実行意味論の知識なしに理解可能
- **簡潔性**: 制約は変換規則や実行可能な変換よりも簡潔に記述できる
- **ドメイン知識の統合**: 一階述語論理を用いた大域制約としてドメイン固有の知識を組み込める

Object Constraint Language(OCL)のようなモデルベース制約言語は、表現力のギャップを埋め、曖昧性を排除するために用いられる。2025年9月の論文[「From OCL to JSX: declarative constraint modeling in modern SaaS tools」](https://arxiv.org/abs/2509.17629)では、宣言的制約モデリングの現代的なアプローチが提案されている。

### 2.3 制約仕様の構成性

[制約ベースの可変性モデリング](https://link.springer.com/article/10.1007/s10009-012-0254-x)は、ソリューション空間の可変性を管理するための柔軟で宣言的なアプローチである。制約は仕様の構成的合成を可能にし、局所的な関係を表現しながら、システム全体の整合性を保証する。

## 3. 制約論理プログラミング(CLP)

### 3.1 CLPの理論的基盤

[制約論理プログラミング](https://en.wikipedia.org/wiki/Constraint_logic_programming)(Constraint Logic Programming, CLP)は、JaffarとLassezによって1987年に導入され、Prolog IIの項等式と不等式が制約の特定形式であるという観察を一般化したものである。

CLPはホーン節論理プログラミングと制約解決を組み合わせる。ホーン節を拡張し、制約述語として宣言された述語が節の本体にリテラルとして現れることを許す。制約述語はプログラム中の事実と規則によって定義されるのではなく、ドメイン固有のモデル理論的構造または理論によって事前定義される。

### 3.2 SWI-Prologにおける制約論理プログラミング

[SWI-Prolog](https://www.swi-prolog.org/pldoc/man?section=clp)のCLPライブラリは、以下のドメインをサポートする：

- **CLP(FD)**: 有限領域上の制約論理プログラミング。整数上のCLPとして最も重要かつ典型的なインスタンス
- **CLP(R)**: 実数上の制約論理プログラミング
- **CLP(Q)**: 有理数上の制約論理プログラミング
- **CLP(B)**: ブール値上の制約論理プログラミング

制約を使用することで、Prologの手続き的側面や制限から解放され、プログラムがより宣言的になる。論理変数の概念を拡張し、変数が特定の値ではなく定義域を持つことを可能にし、プログラマが指定した規則に従うように変数を制約できる。

### 3.3 CLPの宣言的意味論

[Prologと宣言的プログラミング](https://en.wikipedia.org/wiki/Declarative_programming)において、Prologは第一に宣言的プログラミング言語として意図されており、プログラムは関係を定義する事実と規則の集合である。CLPはこの宣言性をさらに強化し、制約として数学的関係を直接表現する。

## 4. 制約伝播と整合性

### 4.1 弧整合性(Arc Consistency)

[弧整合性](https://www.sciencedirect.com/topics/computer-science/arc-consistency)は、最も古く最もよく知られた制約伝播の方法である。変数の対(X, Y)が弧整合であるとは、Xの定義域の各値xに対して、XとY間のすべての二項制約を満たすようなYの定義域の値yが存在することを意味する。

### 4.2 弧整合性アルゴリズムの歴史

[Mackworthの貢献](https://ics.uci.edu/~dechter/courses/ics-276/spring-19/reading/chapter3-constraints.pdf)は制約伝播理論の基盤を築いた：

- **AC-1、AC-2、AC-3**: Mackworthは二項ネットワークの局所整合性を特徴づける3つの性質(ノード整合性、弧整合性、パス整合性)を区別し、弧整合性を強制するアルゴリズムを導入した
- **AC-3の優位性**: AC-3はAC-2を一般化・簡潔化し、修正すべき弧のキューを維持する。定義域が縮小されたとき、関連する弧のみがキューに再追加される。この効率的な伝播により、AC-3は実用上最も広く使用される弧整合性アルゴリズムとなっている

### 4.3 制約伝播の形式的性質

[制約伝播](https://www.geeksforgeeks.org/artificial-intelligence/constraint-propagation-in-ai/)は、問題を変えずに解を変えない変換によって、すべての局所整合性条件を強制できる。制約伝播は以下の方法で動作する：

- 変数の定義域を縮小する
- 制約を強化する
- 新しい制約を生成する

ハイパー弧整合性(hyper-arc consistency)または一般化弧整合性(generalized arc consistency)は、制約を満たすように単一の変数の拡張可能性を要求する。変数がハイパー弧整合であるとは、変数のすべての値が、制約が満たされるように制約の他の変数へ拡張可能であることを意味する。

## 5. 大域制約(Global Constraints)

### 5.1 大域制約の定義と意義

[大域制約](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf)は、固定されていない数の変数間の関係を捉える制約である。大域制約により、複数の単純な制約の集合を置き換える単一の制約を任意数の変数に対して表現でき、典型的には一般化弧整合性を強制する伝播アルゴリズムを提供する。

大域制約の使用は、以下の利点をもたらす：

- **探索空間の効率的な刈り込み**: 不整合な解を除去し、計算複雑度と時間を削減
- **より強力な伝播**: 二項制約の集合として表現するよりも効果的

### 5.2 AllDifferent制約

[AllDifferent制約](https://sofdem.github.io/gccat/gccat/Calldifferent.html)は、おそらく最もよく知られ、最も影響力があり、最も研究されている大域制約である。変数の集合がすべて異なる値を取ることを強制する。

二項不等式制約の集合として表現することもできるが、そのような表現は不整合な解の刈り込みにおいて効果が低い。専用の伝播アルゴリズムは、変数間の相互作用をより深く理解し、より効率的な定義域縮小を可能にする。

### 5.3 Cumulative制約

[Cumulative制約](https://sofdem.github.io/gccat/gccat/Ccumulative.html)は、各時点において、重なり合うタスクの累積資源消費が指定された容量を超えないことを強制する。各タスクは開始時刻、継続時間、資源消費を持ち、これらはすべて定義域変数である。

Cumulative制約の専用伝播アルゴリズムは、開始時刻や他の変数の定義域を縮小することを目的とし、多数の二項制約を定義してそれらに対して弧整合性や境界整合性を適用するよりも効率的である。

### 5.4 大域制約カタログ

[Global Constraint Catalog](http://sofdem.github.io/gccat/)は、制約プログラミングにおける大域制約の包括的なリポジトリであり、数百の大域制約の形式的定義、意味論、伝播アルゴリズムを提供している。

## 6. 制約プログラミング言語とツール

### 6.1 MiniZinc

[MiniZinc](https://www.minizinc.org/)は、制約プログラミングのための高レベル、ソルバー非依存のモデリング言語である。MiniZincモデルは、制約プログラミング、混合整数計画法、SATベースソルバーなど、広範なバックエンドを用いて解くことができ、研究と実用応用の両方に理想的なツールである。

#### 2025年の動向

2025年の[MiniZinc Challenge](https://www.minizinc.org/challenge/2025/results/)では、各ソルバーが100のMiniZincモデルインスタンスで実行され、問題の解決、解のスピード、解の質に対してポイントが授与された。最新リリースはバージョン2.9.5(2026年1月23日リリース)である。

[ICAPS 2025](https://icaps25.icaps-conference.org/program/tutorials/minizinc/)では、MiniZincを用いた計画とスケジューリングのための制約モデリングのチュートリアルが開催された。

### 6.2 Picat

[Picat](https://picat-lang.org/)は、汎用応用を目的としたシンプルでありながら強力な、論理ベースのマルチパラダイムプログラミング言語である。Picatは現在、制約充足・最適化問題を解くために4つのモジュール(cp、sat、mip、smt)を提供しており、あるソルバーから別のソルバーへシームレスに切り替えることが可能である。

#### 2025年の成果

Picatは[XCSP'25でメインCSP部門1位](https://www.minizinc.org/challenge/2025/)、MiniZinc'25でフリーサーチ部門2位を獲得した。

### 6.3 主要な制約ソルバー

[制約プログラミングツールの現状](https://developers.google.com/optimization/cp)：

- **Google OR-Tools**: Googleによるオペレーションズリサーチ/制約プログラミングシステム。オープンソースで幅広い最適化問題に対応
- **Choco Solver**: Javaで書かれた制約プログラミングシステム。フリーのオープンソースライブラリ
- **Gecode**: C++による制約プログラミングシステム。オープンソースツールキット

これらのツールは、スケジューリング、計画、資源割当、構成問題など多岐にわたる分野で応用されている。

## 7. 制約プログラミングと他の形式手法の関係

### 7.1 CSP検証とモデル検査

[CSP(Communicating Sequential Processes)のモデル検査](https://link.springer.com/chapter/10.1007/978-3-540-88479-8_22)は、並行システムの形式検証における主流手法である。モデル検査は、システムの有限状態モデルが与えられた仕様を満たすかを検証する方法であり、安全性要求(システムクラッシュを表す状態の回避)と活性要求(ライブロックの回避)を含む。

#### FDRとPATツール

- **FDR(Failures-Divergences Refinement)**: CSPの事実上の解析器として数十年前に導入され、洗練化検査を自動化する
- **PAT(Process Analysis Toolkit)**: CSPを用いて指定されたイベントベースの構成的システムモデル、共有変数、非同期メッセージ送受信を解析するように設計されている。自動洗練化検査、イベント拡張LTLのモデル検査などをサポート

#### セキュリティプロトコル検証

CSPは複雑なメッセージ交換を含むシステムのモデリングと解析に適しており、通信・セキュリティプロトコルの検証にも応用されてきた。著名な例として、LoweによるCSPとFDR洗練化チェッカーを用いたNeedham-Schroeder公開鍵認証プロトコルにおける未知の攻撃の発見と、その攻撃に耐える修正プロトコルの開発がある。

### 7.2 制約プログラミングとオペレーションズリサーチの統合

[制約プログラミングとオペレーションズリサーチの統合](https://johnhooker.tepper.cmu.edu/CPandOR.pdf)は、組合せ最適化問題の解決において強力なアプローチである。両者は共通の主双対解法アプローチに依拠しており、以下の4つの主要戦略による統合の基盤を提供する：

1. **単一ソルバー内での密な相互連携**: CPの伝播とORの緩和を単一ソルバー内で緊密に組み合わせる
2. **CPの定義域フィルタリングへのOR技法の適用**: ORの手法をCP伝播に応用する
3. **問題の分解**: 問題をCPで解く部分とORで解く部分に分解し、CPベースの列生成や論理ベースのBenders分解を用いる
4. **緩和決定ダイアグラムの利用**: CP伝播のために開発された緩和決定ダイアグラムをORの動的計画法モデルの解決に活用する

## 8. 制約プログラミングの産業応用

### 8.1 スケジューリング問題

[産業テストラボラトリーのスケジューリング](https://link.springer.com/article/10.1007/s10951-024-00821-0)において、制約プログラミングは現実的なインスタンスに対して良好な結果を達成し、同じモデル上でMIPソルバーを上回る性能を示した。資格を持つ人員が専門機器を用いて、期限やその他の制約を尊重しながら大量のテストを実行する複雑な現実世界のスケジューリング問題に対して、CP技術が成功裏に適用できることを実証している。

研究によると、制約プログラミング技術は大規模プロジェクトスケジューリング問題を解くための精密で柔軟、効率的かつ拡張可能なスケジューリングシステムの実装を可能にする。

### 8.2 造船業

[造船業における制約プログラミングモデル](https://www.mdpi.com/2077-1312/11/8/1517)は、組立と限定されたバッファ容量を伴うフレキシブルジョブショップスケジューリング問題を解決するために開発された。この問題は、サブブロックから最終船舶建造までのブロックの製造と組立を含み、ブロックのサイズによる限定されたバッファ容量を考慮している。

### 8.3 その他の応用分野

[制約プログラミングの実用応用](https://link.springer.com/article/10.1007/BF00143881)は以下を含む：

- **回路検証**: 回路の正当性検証
- **リアルタイム制御システム検証**: リアルタイムシステムの性質検証
- **銀行計画の意思決定支援システム**: 中期銀行計画における意思決定支援
- **乗務員スケジューリング**: 航空会社や鉄道の乗務員配置問題

制約プログラミングは、複雑な現実世界の産業問題、特にスケジューリングと資源最適化のシナリオにおいて実用的なアプローチを提供する。

### 8.4 日本における応用例

[日本の制約プログラミング応用](https://tamura70.gitlab.io/lect/pdf/jk.pdf)には以下がある：

- **Jリーグの日程調整**: スポーツリーグのスケジューリング最適化
- **人員配置計画**: 人的資源の最適配分
- **輸送計画**: 物流の最適化
- **パッキング問題**: 空間・資源の効率的利用
- **時間割作成**: 教育機関のスケジューリング

これらの応用は、制約プログラミングが問題の本質に焦点を当てた直感的な記述を可能にし、複雑な組合せ問題の実用的解決に貢献していることを示している。

## 9. CSPの解法アルゴリズム

### 9.1 バックトラッキング法

[バックトラッキング法](https://ja.wikipedia.org/wiki/%E5%88%B6%E7%B4%84%E5%85%85%E8%B6%B3%E5%95%8F%E9%A1%8C)は、CSPの代表的な解法である。制約違反が起こらないようにある順序に従って変数への値の割当てを順次行っていく方法で、木探索とも呼ばれる。

変数に値を割当てる際、すべての制約を満たす値が存在しなければ、一つ前の変数に戻ってその値を取消し、他の値を試みる(バックトラック)という操作を繰り返す。

### 9.2 改良されたバックトラッキング技法

[CSPアルゴリズムの改良技法](https://ocw.hokudai.ac.jp/wp-content/uploads/2016/01/IntelligentInformationProcessing-2005-Note-07.pdf)：

- **バックジャンピング(Backjumping)**: 複数の値が制約矛盾を起こす場合、一つ前の変数に戻るのではなく、より前の変数まで戻ってその値を変更する
- **バックマーキング(Backmarking)**: 過去の探索情報を記録して無駄な再計算を避ける
- **バックチェッキング(Backchecking)**: 割当て時に過去の変数との整合性をチェックする

### 9.3 メタヒューリスティクス

[タブー探索アプローチ](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1015-13.pdf)など、メタヒューリスティクスもCSPに適用される。タブーリストを用いて局所最適解からの脱出を図り、大規模問題の近似解を効率的に求める。

### 9.4 SATソルバーへの還元

近年、高速化した[SATソルバー](https://tamura70.gitlab.io/lect-logic/pdf/AI-SAT-3.pdf)を活用してCSPなど他の問題をSAT(充足可能性問題)へ還元して解くことがよく行われている。SAT符号化により、CSPを命題論理の充足可能性問題として定式化し、高度に最適化されたSATソルバーの性能を活用できる。

## 10. 制約プログラミングの理論的基盤と仕様記述への含意

### 10.1 宣言的仕様の数学的基盤

制約プログラミングは、以下の数学的・論理学的基盤に立脚している：

- **述語論理**: 制約は一階述語論理の式として表現される
- **関係論理**: 制約は変数間の関係を定義する
- **充足可能性理論**: 制約の集合が充足可能かを判定する理論
- **グラフ理論**: 制約ネットワークはグラフとして表現され、弧整合性などの概念はグラフ理論的性質と対応する

### 10.2 仕様記述における制約の位置づけ

制約プログラミングの視点から見た仕様記述の特徴：

1. **完全な宣言性**: 「何を満たすべきか」のみを記述し、「どう達成するか」は記述しない
2. **実行可能性**: 制約仕様は直接ソルバーにより実行可能である
3. **検証可能性**: 解候補が制約を満たすかは機械的に検証可能である
4. **反証可能性**: 制約を満たさない例があれば、仕様違反が明確に示される

これらは、Karl Popperの反証主義における「良い仕様」の条件と一致する。制約プログラミングは、科学的方法論と整合的な仕様記述パラダイムといえる。

### 10.3 制約プログラミングの限界と課題

一方で、制約プログラミングには以下の限界も存在する：

- **計算複雑性**: 多くのCSPはNP完全であり、最悪の場合は指数時間を要する
- **スケーラビリティ**: 変数数・定義域サイズが増大すると解が困難になる
- **表現力の制約**: すべての仕様が自然に制約として表現できるわけではない
- **ソフト制約の扱い**: ハード制約と異なり、ソフト制約の最適化は多目的最適化問題となり複雑度が増す

しかし、これらの限界は原理的なものではなく、アルゴリズム改良・ハードウェア性能向上・ハイブリッドアプローチにより継続的に改善されている。

## 11. 制約プログラミングと仕様記述の未来

### 11.1 AI時代における制約プログラミング

2025年以降、大規模言語モデル(LLM)との統合により、制約プログラミングは新たな段階に入りつつある：

- **自然言語からの制約生成**: LLMが自然言語の問題記述から制約を自動生成
- **制約の説明生成**: ソルバーの結果をLLMが自然言語で説明
- **対話的制約精緻化**: ユーザーとの対話を通じて制約仕様を反復的に改善

### 11.2 ハイブリッドアプローチの発展

[制約プログラミングとオペレーションズリサーチの統合](https://link.springer.com/article/10.1007/s10601-017-9280-3)は今後も深化し、以下の方向性が期待される：

- **マルチパラダイム最適化**: CP、MIP、SAT、メタヒューリスティクスの自動的な組み合わせ
- **学習ベース制約伝播**: 機械学習により伝播戦略を最適化
- **量子制約解決**: 量子アニーリングやQAOAなど量子計算の活用

### 11.3 仕様記述手法としての制約プログラミングの意義

制約プログラミングは、仕様記述における以下の本質的問題に対する一つの解を示している：

- **仕様と実装の分離**: 制約は純粋な仕様であり、ソルバーは汎用的な実装である
- **形式性と可読性の両立**: 数学的に厳密でありながら、直感的に理解可能
- **実行可能性**: 仕様から直接解を導出できる
- **段階的精緻化**: 制約の追加により仕様を段階的に精密化できる

これらの特性により、制約プログラミングは「理想的な仕様記述」の一形態として、今後も重要な役割を果たし続けるだろう。

## まとめ

制約プログラミングは、変数、定義域、制約の三つ組による宣言的問題記述と、制約ソルバーによる自動的解探索を特徴とするパラダイムである。仕様記述の観点から見ると、制約プログラミングは「何を満たすべきか」を記述し「どう解くか」をシステムに委ねる純粋に宣言的なアプローチであり、仕様と実装の理想的な分離を体現している。

理論的基盤として、制約充足問題(CSP)と制約最適化問題(COP)の形式的定義、制約伝播と弧整合性の理論、大域制約による効率的モデリングがある。MiniZinc、Picat、Choco、Gecode、OR-Toolsなどの実用ツールが2025年現在も活発に開発され、工業スケジューリング、造船業、テストラボラトリー計画など多様な産業応用で成果を上げている。

制約論理プログラミング(CLP)は論理プログラミングと制約解決を統合し、SWI-PrologのCLP(FD)などを通じて実用化されている。CSP検証とモデル検査の関係、制約プログラミングとオペレーションズリサーチの統合など、他の形式手法との連携も深まっている。

AI時代において、LLMによる自然言語からの制約生成、ハイブリッド最適化手法、量子計算の活用など、制約プログラミングはさらなる進化を遂げつつある。仕様記述手法としての制約プログラミングは、形式性と可読性の両立、実行可能性、段階的精緻化という特性により、ソフトウェア工学における「理想的な仕様記述」の一形態として、今後も中心的な役割を果たし続けるだろう。

## 参考文献・情報源

### 理論的基盤
- [Constraint Programming - Wikipedia](https://en.wikipedia.org/wiki/Constraint_programming)
- [Constraint Satisfaction Problem - Wikipedia](https://en.wikipedia.org/wiki/Constraint_satisfaction_problem)
- [Constraint Satisfaction Problems (CSP) in Artificial Intelligence - GeeksforGeeks](https://www.geeksforgeeks.org/artificial-intelligence/constraint-satisfaction-problems-csp-in-artificial-intelligence/)
- [Constrained Optimization - Wikipedia](https://en.wikipedia.org/wiki/Constrained_optimization)
- [制約プログラミング - Wikipedia](https://ja.wikipedia.org/wiki/%E5%88%B6%E7%B4%84%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%9F%E3%83%B3%E3%82%B0)
- [制約充足問題 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%88%B6%E7%B4%84%E5%85%85%E8%B6%B3%E5%95%8F%E9%A1%8C)
- [制約プログラミングって何? - Constraint.org](https://www.constraint.org/ja/intro/)

### 制約論理プログラミング
- [Constraint Logic Programming - Wikipedia](https://en.wikipedia.org/wiki/Constraint_logic_programming)
- [SWI-Prolog -- Constraint Logic Programming](https://www.swi-prolog.org/pldoc/man?section=clp)
- [Prolog/Constraint Logic Programming - Wikibooks](https://en.wikibooks.org/wiki/Prolog/Constraint_Logic_Programming)
- [制約論理プログラミング - Wikipedia](https://ja.wikipedia.org/wiki/%E5%88%B6%E7%B4%84%E8%AB%96%E7%90%86%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%9F%E3%83%B3%E3%82%B0)
- [制約論理プログラミング超入門](https://www.nct9.ne.jp/m_hiroi/prolog/clp01.html)

### 制約伝播と整合性
- [Chapter 3 Consistency-enforcing algorithms: constraint propagation](https://ics.uci.edu/~dechter/courses/ics-276/spring-19/reading/chapter3-constraints.pdf)
- [Arc Consistency - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/arc-consistency)
- [Constraint Propagation in AI - GeeksforGeeks](https://www.geeksforgeeks.org/artificial-intelligence/constraint-propagation-in-ai/)
- [Local Consistency - Wikipedia](https://en.wikipedia.org/wiki/Local_consistency)

### 大域制約
- [Chapter 7 Global Constraints - Willem-Jan van Hoeve and Irit Katriel](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf)
- [Global Constraint Catalog](http://sofdem.github.io/gccat/)
- [Global Constraint Catalog: Calldifferent](https://sofdem.github.io/gccat/gccat/Calldifferent.html)
- [Global Constraint Catalog: Ccumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html)

### 言語とツール
- [MiniZinc](https://www.minizinc.org/)
- [MiniZinc Challenge 2025](https://www.minizinc.org/challenge/2025/)
- [ICAPS 2025 - MiniZinc Tutorial](https://icaps25.icaps-conference.org/program/tutorials/minizinc/)
- [Picat](https://picat-lang.org/)
- [Google OR-Tools - Constraint Optimization](https://developers.google.com/optimization/cp)
- [Choco-solver](https://choco-solver.org/)

### 仕様記述と制約
- [Imperative versus declarative constraint specification languages - Springer](https://link.springer.com/article/10.1007/s10270-020-00796-4)
- [Constraint-based specification of model transformations - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0164121212002543)
- [From OCL to JSX: declarative constraint modeling (arXiv 2509.17629)](https://arxiv.org/abs/2509.17629)
- [A constraint-based variability modeling framework - Springer](https://link.springer.com/article/10.1007/s10009-012-0254-x)

### CSP検証とモデル検査
- [Model Checking CSP Revisited - Springer](https://link.springer.com/chapter/10.1007/978-3-540-88479-8_22)
- [Model Checking - Wikipedia](https://en.wikipedia.org/wiki/Model_checking)
- [Communicating Sequential Processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)

### 統合とハイブリッドアプローチ
- [Operations Research Methods in Constraint Programming - John Hooker](https://johnhooker.tepper.cmu.edu/chapter15.pdf)
- [Constraint Programming and Operations Research - John Hooker](https://johnhooker.tepper.cmu.edu/CPandOR.pdf)
- [Constraint programming and operations research - Springer](https://link.springer.com/article/10.1007/s10601-017-9280-3)

### 産業応用
- [Investigating constraint programming for real world industrial test laboratory scheduling - Springer](https://link.springer.com/article/10.1007/s10951-024-00821-0)
- [A Constrained Programming Model for the Shipbuilding Industry - MDPI](https://www.mdpi.com/2077-1312/11/8/1517)
- [Practical applications of constraint programming - Springer](https://link.springer.com/article/10.1007/BF00143881)
- [Building Industrial Applications with Constraint Programming - Springer](https://link.springer.com/chapter/10.1007/3-540-45406-3_6)

### 日本語資料
- [CSP制約充足アルゴリズム - 田村直之(神戸大学)](https://tamura70.gitlab.io/lect/pdf/jk.pdf)
- [制約充足問題 - 北海道大学OCW](https://ocw.hokudai.ac.jp/wp-content/uploads/2016/01/IntelligentInformationProcessing-2005-Note-07.pdf)
- [数学的な問題をそのまま解く〜制約・論理プログラミングの考え方 - Qiita](https://qiita.com/jkr_2255/items/572d3b107f09d33acc8e)

### 国際会議
- [CP 2025 (31st International Conference on Principles and Practice of Constraint Programming)](https://cp2025.a4cp.org/)
- [CPAIOR Conference Series](https://cpaior.org/)
