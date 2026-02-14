# TLA+の理論と実践

## 概要

TLA+（Temporal Logic of Actions Plus）は、Leslie Lamportによって開発された形式仕様言語である。特に並行システムと分散システムの設計、モデリング、文書化、検証に用いられる。TLA+は「徹底的にテスト可能な疑似コード」と形容され、ソフトウェアシステムの青写真を描くツールとして位置づけられる。

TLA+の基盤となる理論は、1990年代初頭にLamportが開発したTLA（Temporal Logic of Actions: 行動の時相論理）であり、時相論理と行動論理を組み合わせたものである。TLAは、並行システムの仕様記述と推論のための論理体系であり、システムとその性質を同じ論理で表現できることが特徴である。

## Leslie Lamportの設計思想

### 数学に対するエンジニアの抵抗を克服する試み

Lamport自身がTLA+を「エンジニアの数学への反感を克服するための途方もない試み」と定義している。彼の実用的な仕様記述方法の探求は、1983年の論文「Specifying Concurrent Programming Modules」で結実し、状態遷移をプライムありとプライムなしの変数のブール値関数として記述するアイデアを導入した。

### アクションと時相式の統合

TLAは、時相式の中でアクションを使用できるようにしたことで、「並行システム検証で使われるすべての推論を形式化し体系化する洗練された方法を提供する」とLamportは述べている。TLA仕様の大部分は通常の非時相的な数学で構成されており、純粋に時相的な仕様よりも扱いやすいことをLamportは重視した。

### 状態機械による抽象化

Lamport の最新の論文「A Science of Concurrent Programs」（2024年6月版）では、抽象プログラムをTLA式として記述する方法が議論されている。この視点は、TLA+が単なる仕様言語ではなく、並行プログラムの科学的記述のための理論的基盤であることを示している。

### 引退と遺産

Lamportは2025年1月にMicrosoft Researchを引退した。しかし、TLA+は既に産業界で広く受け入れられており、彼の遺産は継続的に発展している。

## TLA+の数学的基盤

### ZFC集合論とZFM

TLA+の静的な部分は、ZFC（Zermelo-Fraenkel set theory with Choice: 選択公理付きツェルメロ-フレンケル集合論）に基づいた形式集合論である。Lamportはこれを「ZFM（ZF for Mathematics: 数学のためのZF）」と呼び、型付き形式主義との比較を含めて説明している。

TLA+の基盤は以下の2つから構成される：

1. **データ構造のための古典的ZFC集合論**: アルゴリズムが操作するデータ構造を表現する
2. **アルゴリズム実行記述のためのTLA**: 線形時間時相論理の変種であるTLA

TLA+では、集合がその構造を形成し、その構造内の要素を記述する論理理論は、一階述語論理とZFC集合論（通常の数学の標準的形式主義）に基づいている。

### 一階述語論理と集合論の統合

TLA+仕様は、基本的な集合論を使って安全性（悪いことが起こらない）を定義し、時相論理を使って活性（良いことがいずれ起こる）を定義する。この二層構造により、通常のエンジニアが慣れ親しんだ数学的記述と、並行・分散システムに特有の時間的性質の記述を統合している。

### 時相論理の役割

TLAは、同時に起こるシステムについての仕様記述と推論のための論理である。システムとその性質が同じ論理で表現されるため、「システムがその仕様を満たす」という主張も、「あるシステムが別のシステムを実装する」という主張も、論理的含意として表現される。

## TLA+の主要概念

### 状態と動作（Actions）

TLA+において、システムは状態機械として表現される：

- **状態（State）**: 変数の値の集合
- **動作（Action）**: 状態から状態への遷移を記述するブール値式
- **振る舞い（Behavior）**: 状態の無限列

動作は、プライムなし変数（現在の状態）とプライムあり変数（次の状態）のブール値関数として表現される。例えば、カウンタのインクリメント動作は `counter' = counter + 1` のように書かれる。

### スタタリング（Stuttering）

TLA+の重要な設計決定の一つは、すべての振る舞いがスタタリングステップ（何も変化しない状態遷移）を許容することである。スタタリングステップは、仕様で記述されていないシステムの他の部分の変更を表現する。

**スタタリング非感受性（Stuttering Insensitivity）**:
TLA+で書けるすべての性質はスタタリング非感受性を持つ。つまり、任意の時相TLA+式 F と振る舞い b に対して、b' が b にスタタリングステップを追加または削除して得られる振る舞いであれば、`b |= F` ⇔ `b' |= F` が成立する。

この性質は、精緻化（refinement）において極めて重要である。

### 安全性と活性

時相性質は2種類に分類される：

**安全性（Safety）性質:**
- システムが「悪いこと」をしないことを述べる
- 例: 「データベース制約を決して違反しない」
- 有限の接頭辞で違反を検出可能
- 振る舞いが安全性性質に違反する ⇔ その有限接頭辞が性質に違反する

**活性（Liveness）性質:**
- システムが「良いこと」をいずれ行うことを述べる
- 例: 「すべてのトランザクションはいずれコミットまたはロールバックする」
- 有限の時間では検証不可能
- TLCによる活性検証は安全性検証よりも大幅に時間がかかる

**実践的なモデル検査戦略:**
- 通常、大きな定数を使った安全性検証用モデルを作成
- より小さな定数を使った活性検証用モデルを別に作成

### 不変条件（Invariants）

TLA+の理論的には、「不変条件」は特別な概念ではない。TLAの論理体系自体には「不変条件」という特別扱いされる概念は存在しない。モデル検査器TLCが実用性と効率性の理由から不変条件を特別にサポートしているだけである。

不変条件は、すべての到達可能な状態で真となる述語として定義され、安全性性質の特別な場合である。

## TLA+の主要ツール群

### PlusCal

**概要:**
PlusCalは2009年に導入された疑似コードライクな言語であり、TLA+にトランスパイルされる。逐次アルゴリズムの仕様記述に特に有用である。

**特徴:**
- 手続き型プログラミング言語のような構文
- より読みやすく、プログラマーにとって親しみやすい
- PlusCalアルゴリズムはTLA+ツール（主にTLCモデル検査器）を使ってデバッグされる
- TLA+の能力をすべて利用できる（TLA+に変換されるため）

**使用例:**
AWSのDynamoDBの仕様は1445行のPlusCalコードで記述され、3つのバグを発見し、多くの最適化を可能にした。エンジニアは2-3週間でTLA+/PlusCalを学習した。

### TLC モデル検査器

**概要:**
TLCは、TLA+仕様の有限状態モデルを構築し、不変性性質をチェックするモデル検査器である。

**動作原理:**
1. 仕様を満たす初期状態の集合を生成
2. 定義されたすべての状態遷移について幅優先探索を実行
3. 不変条件違反や活性違反を検出

**スケーラビリティ:**
- DynamoDBの検証では、10台のcc1.4xlarge EC2インスタンスで分散版TLCを実行
- 最短のエラートレースは35の高レベルステップを含み、非常に微妙なバグを発見

**利点:**
- 高速なバグ発見（TLAPS検証前の事前チェックとして有用）
- 小さなエラーを素早く発見

**限界:**
- 有限モデル検査のため、無限状態システムや無限ドメインを完全には扱えない
- 活性性質の検査は安全性よりも大幅に遅い

### TLAPS（TLA+ Proof System）

**概要:**
TLAPSは、TLA+で書かれた証明を機械的にチェックする定理証明システムである。2012年に導入され、Microsoft Research-INRIA Joint Centreで開発された。

**設計原則:**
- 特定の定理証明器に依存しない証明言語
- 宣言的スタイルでの証明記述
- 個別の証明義務に変換し、バックエンド証明器に送信

**バックエンド証明器:**
- **主要**: Isabelle、Zenon
- **フォールバック**: SMTソルバー（CVC3、Yices、Z3）

**TLCとの相補性:**
- TLCが小さなエラーを迅速に発見 → TLAPS検証前のデバッグ
- TLAPSが有限モデル検査の能力を超えるシステム性質を証明

**用途:**
並行および分散アルゴリズムの正しさを証明するために設計された。形式検証が重要な安全性クリティカルシステムや、TLCでカバーできない無限状態システムの検証に使用される。

### TLA+ Toolbox

TLA+ ToolboxはTLA+のための統合開発環境（IDE）であり、以下を統合する：

- TLA+エディタ
- TLCモデル検査器のフロントエンド
- TLAPS証明システムのインターフェース
- 仕様の視覚化ツール

## TLA+による分散システム仕様

### 分散システムとTLA+

TLA+は、分散システムの複雑な振る舞い、特に並行性と障害に起因する微妙なバグを発見するために特に適している。

**TLA+が扱う分散システムの主要側面:**

1. **並行性**: 複数のプロセスの相互作用
2. **非決定性**: システムの複数の可能な遷移
3. **障害**: ノード障害、ネットワーク分断、メッセージ喪失
4. **タイミング**: 非同期通信、タイムアウト
5. **一貫性**: データの複製と一貫性保証

### 代表的な分散アルゴリズムの仕様

TLA+で仕様化される典型的なアルゴリズム：

- **Two-Phase Commit**: 分散トランザクションのアトミックコミットプロトコル
- **Paxos**: 分散合意アルゴリズム
- **Raft**: 理解しやすい合意アルゴリズム
- **Byzantine Fault Tolerance**: ビザンチン障害に耐える合意アルゴリズム

### Raftの例

RaftはDiego Ongaroによって設計された分散合意アルゴリズムであり、理解しやすさと実装の容易さを重視している。Raftの正しさは、TLA+仕様に基づく手動証明によって確立されている。

また、研究者はTLA+でRaftとPaxosがどの程度類似しているかを形式的に定義し、RaftはPaxosの精緻化と見なせると主張している。

## TLA+の産業活用事例

### Amazon Web Services（AWS）

**導入の歴史:**
2011年以降、AWSのエンジニアは重要なシステムの困難な設計問題を解決するために形式仕様とモデル検査を使用してきた。

**適用システム:**
- S3（Simple Storage Service）
- DynamoDB（NoSQLデータベース）
- その他10の大規模で複雑な実世界のシステム

**成果:**
- すべてのケースでTLA+が重要な価値を付加
- 微妙で深刻なバグを発見（他の技術では発見不可能）
- 正しさを犠牲にせず、複雑なアルゴリズムに対する積極的な性能最適化を可能に

**DynamoDBの事例:**

あるエンジニアがTLA+を学習し、数週間でシステムコンポーネントの詳細な仕様を記述した。モデル検査により、特定の障害と回復ステップのシーケンスが他の処理とインターリーブされた場合にデータ損失を引き起こす可能性のあるバグを発見した。

このバグは非常に微妙で、最短のエラートレースでも35の高レベルステップを含んでいた。このような複雑な相互作用は、通常のテストやコードレビューでは発見が極めて困難である。

**学習曲線:**
エントリーレベルからプリンシパルまでのエンジニアが、TLA+をゼロから学習し、2-3週間で有用な結果を得ることができた。

**組織的影響:**
AWSでの形式手法の使用は大成功であり、微妙で深刻なバグが本番環境に到達するのを防ぎ、品質を犠牲にせずに複雑なアルゴリズムに積極的な最適化を加える自信をエンジニアに与えた。

### Microsoft

**Azure Cosmos DB:**

Cosmos DBエンジニアリングチームは、分散アルゴリズムとプロトコルを数学的に仕様化し、正しさをモデル検査するためにTLA+に大きく依存している。これにより、設計決定を検証し、並行性と障害によって引き起こされるコーナーケースに対処している。

**一貫性モデルの形式仕様:**

Azure Cosmos DBの5つの一貫性レベル（強一貫性、有界陳腐性、セッション一貫性、一貫性プレフィックス、最終的一貫性）はすべてTLA+仕様言語を使って仕様化・検証され、TLA+モデルはGitHubでオープンソース化されている（[Azure/azure-cosmos-tla](https://github.com/Azure/azure-cosmos-tla)）。

**実践的影響:**

Azure Cosmos DBサービスのユーザー向け振る舞いを正確に定義する形式仕様に焦点を当てることで、研究者は既存のどの仕様よりも大幅に小さく概念的に単純でありながら、既存の詳細な仕様よりも広範囲のユーザー観測可能な振る舞いを表現するデータベースの形式仕様を書くことができた。

文書化された多くの追加振る舞いは、Cosmos DB開発チーム外ではほとんど理解されておらず、それに依存するMicrosoft製品でデータ一貫性エラーを引き起こしていた。形式仕様により、Cosmos DBの公開文書に重要な問題が提起され、Cosmos DBに依存する別のAzureサービス内の過去の大規模障害に対する根本的解決策が提供された。

### Cockroach Labs

**CockroachDB:**

CockroachDBは、ノード間の一貫性と信頼性を確保するためにRaftプロトコルを使用している。Raftは過去10年間に登場し、理解と実装がはるかに容易な合意アルゴリズムであることを約束していたため、CockroachDBはこれを選択した。

**形式検証の採用:**

TLA+は、DynamoDBやS3からCockroachDBが使用するRaft合意アルゴリズムまで、システムとアルゴリズムの検証に大きな成功を収めている。Cockroach Labsは、プロトコルを形式的に仕様化し、検証を通じて安全性性質を証明したかったため、Leslie Lamportによって開発された形式仕様言語であるTLA+に注目した。

**Raftの形式検証:**

Raftの正しさは、プロトコルのTLA+仕様に基づく手動証明によって確立されている。

## TLA+の学習リソース

### TLA+ Video Course

Leslie Lamportは「The TLA+ Video Course」を作成している。これは、プログラマーやソフトウェアエンジニアが自分自身のTLA+仕様を書く方法を教えるビデオ講義シリーズの始まりである。進行中の作品として位置づけられている。

**対象者:**
プログラミング概念の基本的理解と、初等数学の知識を前提とする。

**構成:**
- 各ビデオには完全なスクリプトが提供される
- スクリプトにはビデオで示され述べられたすべてが含まれる
- ビデオを見ずにスクリプトを読むこともできる
- 講義の復習や、ビデオを好まない人に適している

**カバーされるトピック:**
- TLA+と状態機械の入門
- Two-Phase Commitと記録（レコード）
- Paxos Commitと耐障害性アルゴリズム
- 実装と時相式

### Specifying Systems: The TLA+ Language and Tools

Lamportは2002年にTLA+の完全な教科書「Specifying Systems: The TLA+ Language and Tools for Software Engineers」を出版した。

**特徴:**
- より古いリソースだが、実践的よりも理論に重点
- より深い内容
- 理論により大きな重点を置いている
- 無料でダウンロード可能

**補完リソース:**
Lamportは、オンラインTLA+ビデオコースの他に、「The TLA+ Hyperbook」という更新されたTLA+リファレンスも作成しており、公式ウェブサイトから入手可能である。

### Learn TLA+

「Learn TLA+」は、実践的なハンズオンTLA+学習のためのコミュニティベースのリソースである。ビデオコースやSpecifying Systemsよりも実践的で、小さな例を通じて学習する。

- URL: [https://learntla.com/](https://learntla.com/)
- 時相性質、不変条件、精緻化などのコアコンセプトをカバー
- インタラクティブな例とチュートリアル

### 実践TLA+（日本語）

Hillel Wayneの「Practical TLA+」（Apress, 2018）の日本語翻訳「実践TLA+」が翔泳社から出版されている。

**内容:**
- TLA+を使った小さなサンプル仕様でバグを発見
- TLA+の演算子、論理、関数、PlusCal、モデル、並行性の基礎を教える
- TLA+をアルゴリズム性能、データ構造、ビジネスコード、MapReduceなど様々な実践的問題に適用

**日本での実践:**
Toretaなどの組織は、分散システム設計の堅牢性を確保するための形式仕様言語としてTLA+とPlusCalを使用しており、過去のネットワークタイムアウトとリトライ処理の問題を経験している。

日本語のTLA+文献は少なく、ほとんどのリソースは英語で入手可能である。

## 精緻化と実装の階層性

### 精緻化マッピング（Refinement Mapping）

**概念:**
精緻化マッピングは、実装の振る舞いをより抽象的な仕様の振る舞いに変換する方法を示す変換である。Martin AbadiとLeslie Lamportが1988年に提案した、低レベル仕様が高レベル仕様を実装していることを証明する技法である。

**動作原理:**
精緻化プロセスはゲームのように機能する：

1. 実装状態空間で動きを行った後
2. 抽象状態空間で「等価な」動きを行わなければならない
3. 「等価な」動きが常に行えれば、実装は抽象仕様を精緻化している

**数学的表現:**
下位レベルの仕様（実装）Impl が上位レベルの仕様（抽象）Spec を精緻化するとは、Impl のすべての振る舞いが Spec の振る舞いでもあることを意味する：`Impl ⇒ Spec`

### 仕様の階層構築

アルゴリズムを複数の詳細レベル（A、B、C）で仕様化することが有益である：
- Aが最も詳細
- Cが最も抽象的

そして、ある性質Pについて `C ⇒ P` を検証する。`A ⇒ B ⇒ C` が成立するため、`A ⇒ P` も成立する。ここで、Aはコードに十分近いレベルで仕様化され、容易に実装できる。

**利点:**
好きなだけ抽象的または精緻化された仕様の階層全体を作成できる。より抽象的な仕様と精緻化マッピングを構築することで、形式証明よりも安価に多くの洞察が得られる。

### 予言変数（Prophecy Variables）

**課題:**
Herlihy と Wingは、精緻化マッピングが機能しない線形化可能な並行キュー実装の例を提供した。並行キューが逐次キューの高レベル仕様を実装していることを証明する精緻化マッピングを定義することができなかった。

**解決策:**
Lamport と Abadiは後に、Herlihy と Wingによって明らかにされた精緻化マッピングの問題を解決する技法として、予言変数のアイデアを提案した。

**制約:**
TLA+のすべての精緻化は、抽象仕様の振る舞いを完全に記述する必要がある。

## TLA+の実践における課題と限界

### 学習曲線

**一般的な技術採用の課題:**
- 採用を困難にするのは技術そのもの以外、人間の反応である
- 恐れ、躊躇、自信の欠如が表面化し、人々は適応能力に疑問を持つ
- 態度、個性、社会的影響、信頼が、使いやすさや機能性と同じくらい採用に影響する

**キャズム（溝）の問題:**
技術採用の課題の大部分は、アーリーアダプターとアーリーマジョリティの間のギャップ（「キャズムを越える」として知られる問題）で発生する。

**TLA+固有の課題:**
- 数学的形式主義への抵抗
- エンジニアが慣れ親しんだプログラミングとは異なる記述スタイル
- 初期投資（学習時間）が必要

**成功要因（AWS事例）:**
エントリーレベルからプリンシパルまでのエンジニアが2-3週間でTLA+を習得できたことは、適切な動機付けとサポートがあれば学習曲線を克服できることを示している。

### 産業採用の障壁

1. **即時の利益が見えにくい**: 形式仕様の価値は、防いだバグの数（見えないもの）で測られるため、ROIが明確でない
2. **既存のプロセスとの統合**: 既存の開発ワークフローにTLA+を組み込む方法が明確でない
3. **ツールの成熟度**: TLA+ Toolboxは強力だが、現代的なIDEの使い勝手には及ばない
4. **人材不足**: TLA+を使える人材が少ない
5. **文化的抵抗**: 「動くコードが仕様」という文化との対立

### 技術的限界

**モデル検査の限界:**
- **状態空間爆発**: 大きなシステムでは状態数が指数的に増加
- **有限モデル**: TLCは有限モデル検査のため、無限ドメインを完全には扱えない
- **活性検証のコスト**: 活性性質の検査は安全性よりも大幅に遅い

**形式証明の限界:**
- **証明コスト**: TLAPSでの証明は時間と専門知識を要する
- **証明の保守**: システム変更時に証明も更新する必要がある

**表現力の限界:**
- 確率的性質の記述が困難
- リアルタイム性質の記述は可能だが複雑

### スケーラビリティの課題

大規模システムでは、TLA+仕様自体が巨大化し管理が困難になる可能性がある。モジュール化と抽象化が重要だが、適切なレベルを見つけることが課題である。

## TLA+の適用領域と効果的な使用

### 最も効果的な適用領域

1. **分散システムの設計初期段階**: 実装前のアーキテクチャ検証
2. **安全性クリティカルシステム**: 航空、医療、金融などの高信頼性要求システム
3. **複雑な並行アルゴリズム**: Paxos、Raft、Byzantine合意など
4. **プロトコル設計**: 通信プロトコル、セキュリティプロトコル

### 効果的でない領域

1. **UIロジック**: ユーザーインターフェースの振る舞い
2. **シンプルなCRUDアプリケーション**: 複雑性が低くTLA+のオーバーヘッドが正当化されない
3. **迅速なプロトタイピング**: 初期探索段階では重すぎる

### TLA+と他のアプローチの組み合わせ

**効果的な組み合わせ:**
- **TLA+ + Property-Based Testing**: TLA+で性質を記述し、QuickCheckなどでテスト
- **TLA+ + モデルベース開発**: TLA+仕様からコード骨格を生成
- **TLA+ + 静的解析**: TLA+で保証した性質を静的解析ツールで実装レベルで確認

## TLA+の将来展望

### AI/機械学習との統合

- TLA+仕様からテストケースの自動生成
- 自然言語仕様からのTLA+コード生成（GPT-4などのLLM活用）
- バグパターンの学習と予測

### ツールの進化

- より使いやすいIDE
- ビジュアル化ツールの改善
- クラウドベースのTLC実行環境（AWSでの事例のように）
- CI/CDパイプラインへの統合

### 教育の普及

- 大学のカリキュラムへの組み込み
- オンライン学習プラットフォームの充実
- 産業界でのトレーニングプログラム

### 標準化と相互運用性

- 他の形式手法ツールとの統合
- 業界標準仕様言語との相互変換
- 仕様のバージョン管理とコラボレーションツール

## まとめ

TLA+は、Leslie Lamportの深い洞察と実用主義が結実した形式仕様言語である。ZFC集合論という堅固な数学的基盤の上に、時相論理とアクションの概念を統合し、並行・分散システムの複雑な振る舞いを厳密かつ理解しやすい形で記述できる。

**TLA+の主要な強み:**

1. **数学的厳密性とエンジニアリング実用性の両立**: 形式的証明も可能だが、モデル検査による迅速なバグ発見も可能
2. **スタタリング非感受性**: 精緻化と合成を容易にする優れた理論的性質
3. **豊富なツールエコシステム**: PlusCal、TLC、TLAPSの組み合わせ
4. **産業界での実績**: AWS、Microsoft、Cockroach Labsなど大規模システムでの成功事例

**TLA+の課題:**

1. **学習曲線**: 数学的形式主義に慣れていないエンジニアには敷居が高い
2. **ツールの成熟度**: 現代的なIDEと比較するとまだ改善の余地あり
3. **即時の ROI が見えにくい**: 予防したバグは不可視
4. **スケーラビリティ**: 巨大システムでは状態空間爆発の問題

**TLA+が答える「仕様とは何か」:**

TLA+の視点では、**仕様とは、システムの許容される振る舞い（状態の無限列）の集合を定義する時相論理式である**。仕様は実装の制約であると同時に、実装が満たすべき性質の記述でもある。精緻化の概念により、仕様は階層的に構造化でき、抽象仕様から具体的実装まで数学的に厳密な関係を保つことができる。

TLA+の成功は、形式手法が「象牙の塔の理論」ではなく、実世界の複雑なシステムで実践的価値を提供できることを実証している。AWSでの「すべてのケースで重要な価値を付加」という評価は、適切な問題領域において、TLA+が投資に見合う（あるいはそれを大きく上回る）リターンをもたらすことを示している。

Lamportの2025年の引退は一つの区切りだが、TLA+のコミュニティと産業界での採用は今後も継続的に成長すると期待される。特に、分散システムとクラウドコンピューティングの重要性が増す現代において、TLA+のような厳密な設計手法の価値はますます高まっている。

---

## 主要参考文献とソース

### TLA理論の基礎
- [The Temporal Logic of Actions (ACM TOPLAS)](https://dl.acm.org/doi/10.1145/177492.177726)
- [Temporal logic of actions - Wikipedia](https://en.wikipedia.org/wiki/Temporal_logic_of_actions)
- [The Temporal Logic of Actions - Leslie Lamport (PDF)](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf)
- [A Temporal Logic of Actions Leslie Lamport (1990)](https://lamport.azurewebsites.net/pubs/old-tla-src.pdf)
- [TLA in Practice and Theory Part 3: The (Temporal) Logic of Actions](https://pron.github.io/posts/tlaplus_part3)

### TLA+言語と数学的基盤
- [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)
- [TLA in Practice and Theory Part 1: The Principles of TLA+](https://pron.github.io/posts/tlaplus_part1)
- [TLA in Practice and Theory Part 2](https://pron.github.io/posts/tlaplus_part2)
- [Specifying Systems - Leslie Lamport (PDF)](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)
- [A Science of Concurrent Programs - Leslie Lamport (2024年6月版)](https://lamport.org/tla/science.pdf)

### ツール
- [GitHub - tlaplus/tlaplus: TLC model checker and TLA+Toolbox](https://github.com/tlaplus/tlaplus)
- [TLA+ Proofs (TLAPS)](https://cseweb.ucsd.edu/~daricket/papers/fm2012.pdf)
- [TLA+ Proofs - arXiv](https://arxiv.org/abs/1208.5933)
- [PlusCal Tutorial - Introduction](https://lamport.azurewebsites.net/tla/tutorial/intro.html)
- [learning:pluscal - TLA+ Wiki](https://docs.tlapl.us/learning:pluscal)

### AWS事例
- [Use of Formal Methods at Amazon Web Services (PDF)](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)
- [How Amazon Web Services Uses Formal Methods - CACM](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/)
- [Systems Correctness Practices at Amazon Web Services - CACM](https://cacm.acm.org/practice/systems-correctness-practices-at-amazon-web-services/)
- [Why Amazon Chose TLA+ - SpringerLink](https://link.springer.com/chapter/10.1007/978-3-662-43652-3_3)
- [Paper notes: Use of Formal Methods at Amazon Web Services](https://vishnubharathi.codes/blog/paper-notes-use-of-formal-methods-at-amazon-web-services/)

### Microsoft事例
- [GitHub - Azure/azure-cosmos-tla: Azure Cosmos TLA+ specifications](https://github.com/Azure/azure-cosmos-tla)
- [Understanding Inconsistency in Azure Cosmos DB with TLA+ (arXiv)](https://arxiv.org/abs/2210.13661)
- [TLA+ Specifications of the Consistency Guarantees Provided by Cosmos DB - Microsoft Research](https://www.microsoft.com/en-us/research/video/tla-specifications-of-the-consistency-guarantees-provided-by-cosmos-db/)

### Cockroach Labs事例
- [Consensus, made thrive - Cockroach Labs Blog](https://www.cockroachlabs.com/blog/consensus-made-thrive/)
- [Parallel Commits - Cockroach Labs Blog](https://www.cockroachlabs.com/blog/parallel-commits/)
- [Raft Consensus Algorithm](https://raft.github.io/)
- [In Search of an Understandable Consensus Algorithm (Raft paper)](https://raft.github.io/raft.pdf)

### 学習リソース
- [TLA+ Video Course - Leslie Lamport](https://lamport.azurewebsites.net/video/videos.html)
- [Learning TLA+ - Leslie Lamport](https://lamport.azurewebsites.net/tla/learning.html)
- [Learn TLA+](https://learntla.com/)
- [Temporal Properties - Learn TLA+](https://learntla.com/core/temporal-logic.html)

### 安全性と活性
- [Safety, Liveness, and Fairness - Leslie Lamport (2019)](https://lamport.azurewebsites.net/tla/safety-liveness.pdf)
- [Liveness and Fairness in TLA+](https://will62794.github.io/my-notes/notes/Liveness_and_Fairness_in_TLA+/Liveness_and_Fairness_in_TLA+.html)

### 精緻化
- [Specification Refinement - Hillel Wayne](https://www.hillelwayne.com/post/refinement/)
- [Hiding, Refinement, and Auxiliary Variables - Leslie Lamport](https://lamport.azurewebsites.net/tla/hiding-and-refinement.pdf)
- [TLA in Practice and Theory Part 4: Order in TLA+](https://pron.github.io/posts/tlaplus_part4)
- [Auxiliary Variables in TLA+ (arXiv)](https://arxiv.org/pdf/1703.05121)

### 日本語リソース
- [実践TLA+ - 翔泳社](https://www.shoeisha.co.jp/book/detail/9784798169163)
- [[TLA+] 分散システムを設計する際に形式仕様を導入してみた](https://note.com/hden/n/nf7098496da0f)
- [Amazon Web Service（AWS）と形式手法](https://formal.mri.co.jp/news/2015/10/amazon-web-serviceaws.html)
- [分散合意アルゴリズム Raft を TLA+ で検証する](https://www.orecoli.com/entry/2020/06/29/080000)
- [TLA+チートシート](https://zenn.dev/riita10069/articles/bc689cae1c7bc0)
