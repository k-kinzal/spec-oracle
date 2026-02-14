# ランタイム検証（Runtime Verification）

## 1. はじめに

ランタイム検証（Runtime Verification、RV）は、形式手法の一分野であり、実行トレースの動的解析を形式仕様に対して行う技術である。プログラムが実行されている間に監視され、関心のある性質に対してチェックされる。性質は形式的記法（LTL、正規表現など）で指定される。

「ランタイム検証」という用語は、2001年に形式検証とテストの境界に位置する問題に対処することを目的としたワークショップの名称として正式に導入された。ランタイム検証は、形式手法とアドホックなテストの間のギャップを埋めることを試みている。

ランタイム検証の主要な有用性は、実行時に問題や異常を発見する能力にあり、システムが実行される際の振る舞いについて貴重な洞察を提供する。形式検証手法（モデル検査や定理証明）の補完として、またテストやデバッグのようなより実用的な手法に対してより厳密なアプローチとして使用される。

## 2. ランタイム検証の基本概念

### 2.1 定義と特徴

**ランタイム検証とは**：
実行トレース（execution traces）が形式仕様（formal specifications）に対して動的に解析される形式手法の分野である。プログラムは実行中に監視され、関心のある性質に対してチェックされる。

**主要な特徴**：
- **動的解析**：システムの実際の実行を観察
- **形式仕様**：性質は形式的記法で記述される
- **実用性**：モデル検査よりもスケーラブル
- **補完的役割**：テストと形式検証の中間に位置

### 2.2 主要な活動

ランタイム検証の取り組みにおける2つの主要な活動：

1. **仕様からモニタを生成するプロセス**：
   - 形式仕様（LTL式、オートマトンなど）から実行可能なモニタを自動生成
   - モニタ合成（monitor synthesis）技術

2. **生成されたモニタに対してトレースを評価するアルゴリズム**：
   - トレースの効率的な処理
   - 性質違反の検出と報告

**その他の活動**：
- トレースを生成するためのシステムの計装（instrumentation）
- 解析対象システムとモニタ間の通信

### 2.3 仕様形式主義

ランタイム検証の仕様は、通常、トレース述語形式主義（trace predicate formalisms）で表現される：

- **有限状態機械（Finite-State Machines）**
- **正規表現（Regular Expressions）**
- **文脈自由パターン（Context-Free Patterns）**
- **線形時相論理（Linear Temporal Logics）**
- これらの拡張

## 3. 時相論理に基づくモニタリング

### 3.1 時相論理モニタリングの概要

モニタリングとは、入力として与えられた時系列に沿ったイベント列が、時相論理などの形で与えられた仕様を満たすかどうか判定する問題である。

**主要な時相論理**：
- **LTL（線形時相論理）**
- **MTL（Metric Temporal Logic）**：実時間制約を含む
- **STL（Signal Temporal Logic）**：連続的な時間変化を扱う

### 3.2 時相論理モニタリングの効率性

線形時相論理（LTL）やMetric Temporal Logic（MTL）、Signal Temporal Logic（STL）といった時相論理では、モニタリングを効率的に行う方法が知られている。

**モニタリングの実現方法**：
モニタリングは、システムが仕様通りの振る舞いをしているかを実行時に確認する、実行時検証の実現方法の1つである。

**効率化の工夫**：
記録しておく必要のある期間が論理式から明確になるため、効率的なモニタリングが実現できる。そのため、モニタリングの分野ではMTLやそれに近い時相論理が用いられることが多い。

### 3.3 離散時間と連続時間

**離散時間モデル**：
実行時モニタリングの場合は、一定の周期で事実を観測したり、あるいは何かイベントが離散的に送られてくるようにして実装されるはずなので、離散的な時間で考えてもそれほど問題にはならない。

**連続時間モデル（STL）**：
サイバーフィジカルシステムのモニタリングは、ランタイム検証の中核手順として機能し、Signal Temporal Logic（STL）は時間制約を持つ要件を形式的に指定するための強力な意味論を持つよく知られた仕様言語である。

### 3.4 モニタ合成とオートマトン

**LTL式からオートマトンへ**：
無限のシステム実行上でLTL仕様をチェックする一般的な技術は、モデルと等価なビュッヒオートマトン（Büchi automaton）と、性質の否定と等価なもう一つのオートマトンを得ることである。

**LTL-FO+のためのオートマトンベースのランタイム検証**：
LTL-FO+（有界変数上の一階量化を含むLTLの拡張）のためのオートマトンベースのランタイム検証手続きが存在する。

**ロバスト意味論**：
ロバスト意味論を持つLTL式は決定性オートマトンによって監視できる。

## 4. 主要なランタイム検証ツール

### 4.1 JavaMOP / RV-Monitor

**JavaMOP**：
Monitoring-Oriented Programming（MOP）のインスタンスであり、ランタイム監視がソフトウェア開発と解析の基本原則としてサポートされるフレームワークである。指定された性質から自動的にモニタが合成され、元のシステムと統合されて実行時の動的振る舞いをチェックする。

**RV-Monitor**：
- Java用RV-MonitorはアカデミックなJavaMOPを強化
- C用RV-Monitorは組み込み制御ユニット向けRV-ECUを強化
- 複雑なアプリケーションやシステムの監視と実行トレース上の性質の強制を可能にする

**主要な特徴**：
- **パラメトリック監視**：JavaMOPは、複数の異なる論理形式主義を許可する唯一のパラメトリック監視システム
- **効率性**：ランタイムオーバーヘッドに関して最も効率的で、メモリ使用量に関しても非常に競争力がある
- **ユーザー定義アクション**：仕様が実行時に違反または検証されたとき、情報のログ記録からランタイムリカバリまで、任意のコードであるユーザー定義アクションがトリガーされる

**計装技術**：
JavaMOPはAspectJを使用してJavaのランタイム検証システムを実現している。

### 4.2 DejaVu

**概要**：
DejaVuは、イベントストリーム（トレース）を時相論理式に対して監視するためのScalaで書かれたプログラムである。式は、マクロと再帰ルールを加えた一階過去時制線形時相論理で記述される。

**データ表現**：
Binary Decision Diagrams（BDD）を使用してトレースで観測されたデータを表現する。

**実装アプローチ**：
DejaVuは、FO-PLTL式から明示的にScalaモニタを生成し、これらのモニタをトレース上でプログラムとして直接実行する。

**拡張版**：
- **TP-DejaVu**：2段階ランタイム検証用に最適化された拡張版
- **PyDejaVu**：Pythonの柔軟性とDejaVuの厳密な監視能力を組み合わせたツール

### 4.3 MonPoly

**概要**：
MonPolyは、一階MITL（Metric Interval Temporal Logic）に基づく監視ツールである。

**実装アプローチ**：
MonPolyのモニタは、式として暗黙的に定義され、その後クエリとして解釈される。

**DejaVuとの比較**：
- 最初の2つの性質に関して、DejaVuはMonPolyを最大3000倍のファクタで上回る
- Fifo性質に関しては、2つのシステムはやや同等だが、MonPolyがこの特定の性質ではより良好

**検証問題**：
これらのツールを比較する研究では、両ツールの出力にいくつかの不一致が見つかり、未検証ツールがMFOTLの標準意味論から逸脱するコーナーケースを示している。

### 4.4 その他のツール

**モニタリング実装ツール**：
- **MonPoly**：MFOTL（Metric First-Order Temporal Logic）
- **DejaVu**：FO-PLTL（First-Order Past-time LTL）
- **Reelay**
- **Copilot**

これらのツールは、時相論理モニタリングの分野で広く使用されている。

## 5. Aspect-Oriented Programming（AOP）との関係

### 5.1 AOPの基本概念

**Aspect-Oriented Programming（AOP）とは**：
モジュール性を高めることを目的としたプログラミングパラダイムであり、横断的関心事（cross-cutting concerns）の分離を可能にする。コードを修正せずに既存のコードに振る舞いを追加する（アドバイス）。

**AOPの主要概念**：
- **結合点（Join Points）**：メソッド呼び出しや属性へのアクセスなど、プログラムの実行における明確に識別された点
- **ポイントカット（Pointcuts）**：結合点を選択し、その実行コンテキストにアクセスするために使用される
- **アドバイス（Advice）**：ポイントカットとコードの本体から構成される
- **アスペクト（Aspects）**：ポイントカットとアドバイスのコレクション

### 5.2 ランタイム監視へのAOPの応用

**ランタイム監視の領域**：
ランタイム監視は、AOPの正準的な「ログ記録」例でさえ、AOPが効果的に展開されてきた領域の1つである。しかし、AOPは広範なランタイム監視アプリケーションの範囲全体のニーズをまだ完全にはサポートしていない。

**実用例**：
MOSAICOアプローチは、J2EEアプリケーションのアーキテクチャ特性を監視するためにAspectJを使用し、アスペクトはアスペクトテンプレートとアーキテクチャ特性を指定するProperty Sequence Chartsに基づいて作成される。

### 5.3 AI統合による最新の発展

AI モデルを既存の文献と統合することで、AOP、ランタイム監視、SMC（Statistical Model Checking）の理解が大幅に進展し、ソフトウェアの振る舞いをリアルタイムでより効果的に検証する新しい、未開拓の機会が提示されている。

## 6. オンライン vs オフラインモニタリング

### 6.1 基本的な違い

**オフラインモニタ**：
イベント後にシステムによって生成されたトレースを処理し、一般的に永続ストレージシステムからトレース実行を読み取る。

**オンラインモニタ**：
システムの実行中にトレースを処理する。

### 6.2 計装とオーバーヘッド

**システムと共に展開される場合**：
モニタがシステムと共に展開される場合、計装は通常最小限であり、ランタイムオーバーヘッドを低く保つために実行トレースは可能な限りシンプルである。

**テストに使用される場合**：
ランタイム検証がテストに使用される場合、より包括的な計装が可能であり、モニタが実行中のシステムのより洗練されたモデルを構築および分析できるように、重要なシステム情報でイベントを強化できる。

### 6.3 オーバーヘッドのトレードオフ

**システムがモニタの処理能力を超えるイベント頻度を生成する場合**：
オフライン方法のみが実行可能である。

**イベントのトレーシングがモニタによる単純なイベント処理よりも高いオーバーヘッドを引き起こす場合**：
同期オンラインモニタの方が低いオーバーヘッドを引き起こす。

**決定性オートマトンモデルでの研究結果**：
カーネル内でのイベントの同期処理は、同じイベントをトレースバッファに保存するよりも低いオーバーヘッドを引き起こす。これが、オンラインモニタ用のカーネル内インタフェースの開発を動機付けた。

## 7. ランタイムオーバーヘッドの問題

### 7.1 オーバーヘッドの発生源

ランタイム検証をシステムに統合する際の課題の1つは、結果として生じるランタイムオーバーヘッドを管理することである。オーバーヘッドは様々な要因から生じる：

- **モニタ呼び出し**：モニタの起動コスト
- **性質述語の計算と評価**：プログラムの状態に基づく性質の評価
- **プログラム計装とトレース抽出**：計装による潜在的なパフォーマンス低下
- **プログラムとモニタ間の干渉**：モニタがプログラムとリソースを共有する可能性

### 7.2 ゼロオーバーヘッド監視

**ゼロオーバーヘッドランタイム監視**：
特定の条件下で、ランタイムオーバーヘッドをゼロまたはほぼゼロに削減する技術が研究されている。これは、監視の最適化やハードウェア支援などによって達成される。

### 7.3 組み込みシステムでの効率化

**小規模システムでの課題**：
組み込みシステムでは、ランタイム監視の理論と実践は全体的によく開発されているが、特に欠陥検出の恩恵を受ける可能性のある小規模システムでは、期待されるほど一般的ではない。

**効率化の研究**：
小規模組み込みシステム向けの線形時相論理ランタイム監視をより効率的にする方法が議論されている。

## 8. ランタイム検証と仕様の関係

### 8.1 仕様の実行時検証

ランタイム検証は、形式仕様をシステムの実際の実行に対して検証する実用的な手段を提供する。これにより、仕様が単なる文書ではなく、実行可能で検証可能な成果物となる。

**仕様駆動開発**：
- 仕様を最初に定義
- 仕様から自動的にモニタを生成
- システム実行時に仕様適合性を継続的に検証

### 8.2 仕様の精緻化と改善

**フィードバックループ**：
ランタイム検証により、実行中の違反が発見されると、仕様の誤りや不完全性が明らかになる。これにより、仕様の精緻化と改善のフィードバックループが形成される。

**実世界での仕様検証**：
形式仕様が実世界のシステムの実際の振る舞いを正確に捉えているかを検証できる。

### 8.3 仕様のテスト性

ランタイム検証は、仕様自体がテスト可能であることを示す。これは、仕様記述の質を高めるインセンティブとなる。

## 9. ランタイム検証の応用分野

### 9.1 セキュリティとセーフティ

**セキュリティポリシー監視**：
システムがセキュリティポリシーに違反していないかをランタイムで監視。

**セーフティポリシー監視**：
安全性が重要なシステムにおいて、安全性要件が満たされているかを監視。

### 9.2 デバッグとテスト

**デバッグ支援**：
実行時の性質違反を検出することで、バグの原因を特定。

**テストの補完**：
従来のテストよりも厳密なアプローチとして、またはテストの一部として使用。

### 9.3 検証と妥当性確認

**形式検証の補完**：
モデル検査や定理証明などのオフライン検証技術の補完。

**妥当性確認**：
システムが仕様を満たすことの実行時確認。

### 9.4 プロファイリングと障害保護

**プロファイリング**：
システムの実行特性を監視し、パフォーマンス情報を収集。

**障害保護**：
異常な振る舞いを検出し、システムの障害を防止。

### 9.5 振る舞い変更とリカバリ

**ランタイムリカバリ**：
性質違反が検出された際に、自動的にリカバリアクションを実行。

**適応的振る舞い**：
実行時の状況に応じてシステムの振る舞いを動的に変更。

## 10. ランタイム検証と形式検証の比較

### 10.1 ランタイム検証の利点

**状態空間爆発の回避**：
ランタイム検証は、検証前に計算モデルを必要としないため、状態空間爆発を回避する。

**スケーラビリティ**：
ランタイム検証の複雑性は、可能なシステム状態の数に依存しないため、小規模および大規模の、潜在的に無限の状態空間を持つシステムに採用できる。

**実用性**：
実際の実行を監視するため、実世界の振る舞いを捉えることができる。

**自動化**：
多くの場合、完全に自動化可能。

### 10.2 ランタイム検証の限界

**完全性の欠如**：
モデル検査が探索されたすべての状態に対して正当性を明確に確認できるのに対し、ランタイム検証は観察された実行のみを検証する。

**網羅性の欠如**：
定理証明が厳密な数学的推論に基づいて正当性を確立するのに対し、ランタイム検証は実行時の振る舞い分析に重点を置く。

**単一実行パスの観察**：
テストと同様に、実行された特定のパスのみを検証し、すべての可能な実行パスを網羅しない。

### 10.3 モデル検査の特徴

**利点**：
- **網羅性**：すべての可能なシステム状態を潜在的に考慮するため、モデルの（不）正当性を保証
- **自動化**：多くの場合、完全に自動

**欠点**：
- **状態空間爆発**：一般に大規模システムにスケールしない
- **計算コスト**：回路のモデル検査は計算コストが高く、状態空間爆発問題に苦しむ
- **リソース制約**：網羅的アルゴリズムの計算複雑性は考慮される状態数に比例し、妥当な時間で状態空間を探索できるモデルにのみ採用可能

### 10.4 補完的な役割

ランタイム検証は、モデル検査や定理証明などのオフライン検証技術、およびテストやデバッグのような部分的解決策に対する有用な補完として機能する。

## 11. ランタイム検証の理論的基盤

### 11.1 健全性（Soundness）

**健全性の定義**：
検証において、健全性とは検証者がすべてのプログラム実行について推論しなければならないことを意味する。したがって、検証がバグがないと結論付けた場合、プログラムは安全である。

**ランタイム検証における健全性**：
ランタイム検証が性質違反を報告した場合、それは真の違反である（偽陽性がない）。

### 11.2 完全性（Completeness）

**完全性の定義**：
証明システムが健全であるとは、それが証明できる文がモデルで実際に真であることを意味し、完全であるとは、モデルについての任意の真の文を証明できることを意味する。

**ランタイム検証における完全性**：
ランタイム検証は、観察された実行のみを検証するため、一般に完全ではない。すべての可能な違反を検出する保証はない。

### 11.3 近似モデル検査

**エラー有界近似**：
状態空間爆発を緩和するために、正確な決定の代わりにエラー有界近似を計算する検証アプローチである。PAC学習、ランダム化シミュレーション、シナリオ最適化などの技術を採用する。

## 12. 最新の研究動向（2025年）

### 12.1 モジュラー・オンライン監視

2025年のSilvettiらの研究は、積分とフィルタ演算子を持つ時相論理仕様のモジュラー・オンライン監視に焦点を当てている。

**新規性**：
- 累積性質のためのスライディングウィンドウ上の新しい積分演算子
- スライディングウィンドウ演算子のためのフィルタリング演算子
- 拡張論理のための効率的なオンライン監視アルゴリズム

### 12.2 確率的予測を伴う監視

従来のハード判定を確率的予測と関連する信頼スコアに置き換える新しい監視アプローチが提案されており、予測の最終的な正当性を保証する。

### 12.3 プライバシー保護監視

サイバーフィジカルシステムのプライバシー保護ランタイム検証に関する研究が進行中である。

### 12.4 分散ランタイム検証

分散システムのスケーラブルなオンライン監視、メトリック時相性質の分散ランタイム検証に関する研究が進展している。

## 13. まとめと展望

ランタイム検証は、形式仕様とシステムの実際の実行を結びつける実用的な形式手法である。モデル検査や定理証明と比較して、状態空間爆発を回避し、大規模システムにスケールする利点を持つ一方で、観察された実行のみを検証するという限界がある。

**主要な貢献**：
- **実用的な形式検証**：形式仕様の実行時検証を可能にする
- **スケーラビリティ**：大規模および無限状態空間システムに適用可能
- **自動化**：仕様からモニタを自動生成
- **多様な応用**：セキュリティ、セーフティ、デバッグ、テスト、検証など

**主要な技術**：
- **時相論理モニタリング**：LTL、MTL、STLなど
- **モニタ合成**：仕様からオートマトンやプログラムを自動生成
- **AOP統合**：AspectJなどによる計装
- **効率化技術**：BDD、オンライン/オフライン監視、ゼロオーバーヘッド技術

**今後の展望**：
- **AI/機械学習との統合**：より高度な監視と予測
- **分散システム対応**：スケーラブルな分散監視
- **プライバシー保護**：センシティブなデータの保護
- **組み込みシステム最適化**：小規模システムでの効率化
- **確率的・量子的システム**：新しいシステムパラダイムへの拡張

ランタイム検証は、「仕様を実行時に検証する」という実用的なアプローチを提供し、形式手法の実用化において重要な役割を果たしている。仕様記述とシステム実装の間のギャップを埋め、継続的な検証を可能にすることで、より信頼性の高いソフトウェアシステムの構築に貢献している。

## 参考文献

- [Runtime verification - Wikipedia](https://en.wikipedia.org/wiki/Runtime_verification)
- [時相論理 (Temporal Logic) のモニタリングの調査](https://makenowjust-labs.github.io/blog/post/2024-03-09-temporal-logic-monitoring/)
- [Modular and Online Monitoring of Temporal Logic Specification with Integral and Filter](https://link.springer.com/chapter/10.1007/978-3-032-05435-7_8)
- [Runtime Verification for LTL in Stochastic Systems](https://link.springer.com/chapter/10.1007/978-3-032-05435-7_20)
- [Efficient Temporal Logic Runtime Monitoring for Tiny Systems](https://link.springer.com/chapter/10.1007/978-3-031-72044-4_1)
- [Runtime Monitoring of Time Window Temporal Logic](https://ieeexplore.ieee.org/document/9738484)
- [Runtime Verification for Linear-Time Temporal Logic](https://link.springer.com/chapter/10.1007/978-3-319-56841-6_5)
- [Distributed runtime verification of metric temporal properties](https://www.sciencedirect.com/science/article/abs/pii/S0743731523001715)
- [Extending Signal Temporal Logic with Quantitative Semantics](https://dl.acm.org/doi/10.1145/3377868)
- [RV-Monitor | Runtime Verification Inc](https://runtimeverification.com/monitor)
- [GitHub - runtimeverification/javamop](https://github.com/runtimeverification/javamop)
- [RV-Monitor: Efficient Parametric Runtime Verification](https://www.researchgate.net/publication/290917297_RV-Monitor_Efficient_Parametric_Runtime_Verification_with_Simultaneous_Properties)
- [RV-Android: Efficient Parametric Android Runtime Verification (PDF)](https://fsl.cs.illinois.edu/publications/daian-falcone-meredith-serbanuta-shiriashi-iwai-rosu-2015-rv.pdf)
- [An In-Depth Study of Runtime Verification Overheads (PDF)](https://www.cs.cornell.edu/~legunsen/pubs/GuanAndLegunsenRVOverheadStudyISSTA24.pdf)
- [JavaMOP: Efficient parametric runtime monitoring framework](https://www.researchgate.net/publication/254041585_JavaMOP_Efficient_parametric_runtime_monitoring_framework)
- [Runtime Verification — The Linux Kernel documentation](https://docs.kernel.org/trace/rv/runtime-verification.html)
- [runtime verification - an overview | ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/runtime-verification)
- [A Survey of Runtime Monitoring Instrumentation Techniques (PDF)](https://arxiv.org/pdf/1708.07229)
- [Scalable Online Monitoring of Distributed Systems](https://dl.acm.org/doi/10.1007/978-3-030-60508-7_11)
- [Zero Overhead Runtime Monitoring](https://link.springer.com/chapter/10.1007/978-3-642-40561-7_17)
- [Scalable Offline Monitoring](https://link.springer.com/chapter/10.1007/978-3-319-11164-3_4)
- [AI-Powered AOP: Enhancing Runtime Monitoring](https://thesai.org/Publications/ViewPaper?Volume=15&Issue=11&Code=ijacsa&SerialNo=13)
- [Aspect-oriented programming - Wikipedia](https://en.wikipedia.org/wiki/Aspect-oriented_programming)
- [A Tutorial on Runtime Verification](https://pure.manchester.ac.uk/ws/files/33443611/FULL_TEXT.PDF)
- [AOP for the domain of runtime monitoring](https://doi.org/10.1145/1509307.1509310)
- [Parametric Runtime Verification of C Programs](https://link.springer.com/chapter/10.1007/978-3-662-49674-9_17)
- [Formal verification - Wikipedia](https://en.wikipedia.org/wiki/Formal_verification)
- [A Tutorial on Runtime Verification and Assurance (PDF)](https://people.eecs.berkeley.edu/~sseshia/219c/spr19/lectures/RuntimeVerfication-and-Assurance.pdf)
- [Formal Verification | Runtime Verification Inc](https://runtimeverification.com/formal-verification)
- [A survey of challenges for runtime verification](https://link.springer.com/article/10.1007/s10703-019-00337-w)
- [Allen Linear Temporal Logic – Monitor Synthesis](https://www.researchgate.net/publication/221403098_Allen_Linear_Interval_Temporal_Logic_-Translation_to_LTL_and_Monitor_Synthesis-)
- [Automata-based monitoring for LTL-FO+](https://link.springer.com/article/10.1007/s10009-020-00566-z)
- [Linear Temporal Logic Based Monitoring](https://www.researchgate.com/publication/318543569_Linear_Temporal_Logic_LTL_Based_Monitoring_of_Smart_Manufacturing_Systems)
- [From LTL to rLTL monitoring](https://pmc.ncbi.nlm.nih.gov/articles/PMC9794548/)
- [Software Verification: Testing vs. Model Checking (PDF)](https://www.sosy-lab.org/research/pub/2017-HVC.Software_Verification_Testing_vs_Model_Checking.pdf)
- [Model checking - Wikipedia](https://en.wikipedia.org/wiki/Model_checking)
- [Model Checking and the State Explosion Problem (PDF)](https://pzuliani.github.io/papers/LASER2011-Model-Checking.pdf)
- [Model Checking and the State Explosion Problem](https://www.researchgate.net/publication/289682092_Model_Checking_and_the_State_Explosion_Problem)
- [DejaVu: A Monitoring Tool for First-Order Temporal Logic](https://www.researchgate.com/publication/326952117_DejaVu_A_Monitoring_Tool_for_First-Order_Temporal_Logic)
- [GitHub - havelund/dejavu](https://github.com/havelund/dejavu)
- [The DejaVu Runtime Verification Benchmark - NASA](https://ntrs.nasa.gov/citations/20210006244)
- [A Taxonomy for Classifying Runtime Verification Tools (PDF)](https://www21.in.tum.de/~traytel/papers/sttt21-tax_long/tax_long.pdf)
- [A Formally Verified Monitor for Metric First-Order Temporal Logic (PDF)](https://people.inf.ethz.ch/basin/pubs/rv19.pdf)
- [形式手法 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E6%89%8B%E6%B3%95)
- [形式的検証 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E7%9A%84%E6%A4%9C%E8%A8%BC)
- [形式手法のポイント（２）： 検証 - MRI](https://formal.mri.co.jp/outline/point-2.html)
- [形式手法とは？ - MRI](https://formal.mri.co.jp/outline/)
