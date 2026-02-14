# 合意アルゴリズムの形式検証

## 概要

分散システムにおける合意（consensus）は、複数のノードが単一の値または値の列について合意に達するための基本的プリミティブである。合意アルゴリズムは、障害やネットワーク分断の存在下でも、安全性（safety：異なるノードが異なる決定をしない）と活性（liveness：最終的に進捗する）を保証しなければならない。

合意アルゴリズムの正しさは極めて重要であり、誤りはデータ喪失、不整合、システム停止など深刻な結果を招く。このため、Paxos、Raft、Zab、Viewstamped Replicationといった主要な合意アルゴリズムに対して、形式仕様と機械的検証による厳密な正しさの証明が行われてきた。

本稿では、これらの合意アルゴリズムの形式検証の現状、使用される技法、主要なツールと結果について調査する。

## 合意アルゴリズムの基礎

### 合意の性質

合意アルゴリズムは以下の3つの性質によって特徴づけられる：

1. **安全性（Safety）**: ノードは、ノードの一つによって提案された有効な値について合意する
2. **活性（Liveness）**: ノードは最終的に合意に達する
3. **耐障害性（Fault-tolerance）**: ネットワークに障害がある場合でもソリューションは機能しなければならない

### FLP不可能性定理

1985年のFischer、Lynch、Pattersonによる有名なFLP不可能性結果は、少なくとも1つのプロセスがクラッシュ障害を持つ可能性がある完全非同期メッセージパッシング分散システムにおいて、合意を達成するための決定論的アルゴリズムは不可能であることを証明した。

しかし、FLPは合意に決して到達できないとは述べていない。モデルの仮定の下で、**どのアルゴリズムも常に有界時間で合意に到達することはできない**と述べているだけである。

**FLP結果の実践的意味：**
分散合意の任意のソリューションは、3つの性質のうち最大2つしか持てないことを大まかに述べている。つまり、どのアルゴリズムも安全、活性、耐障害性を同時に持つことはできない。

**回避策：**
- **最小限のネットワーク仮定**: 多くの合意アルゴリズムは、最小限で合理的なネットワーク仮定があれば、安全性、活性、耐障害性の3つすべてを持つことができる
- **ランダム化アルゴリズム**: ランダム化合意アルゴリズムは、ネットワーク内の知的なDoS攻撃者などの最悪ケースのスケジューリングシナリオの下でも、圧倒的な確率で安全性と活性の両方を達成することにより、FLP不可能性結果を回避できる

### 安全性と活性の分離

安全性性質は、「悪いこと」が任意の実行で起こらないことを指定する。活性性質は、「良いこと」がすべての実行で起こることを指定する。**すべての性質は、安全性性質と活性性質の連言として表現可能である**。

安全性性質の違反は有限の接頭辞で検出可能である（悪いことは有限の時点で起こる必要がある）。活性性質は有限の時間では検証不可能である。

## Paxosの形式検証

### Paxosアルゴリズムの概要

Paxosは、Leslie Lamportによって設計された古典的な合意アルゴリズムである。1989年に最初に提出され、1998年にジャーナル論文として出版された。Paxosは、洗練された形式主義を提供し、耐障害性分散合意プロトコルの安全性に関する最も初期の証明の一つを含んでいた。

Lamportの状態機械複製（SMR）とPaxosは、合意と複製方法を設計し推論するための**事実上の標準フレームワーク**となった。Google、Yahoo、Microsoft、Amazonを含む多くの企業が、Paxosの基礎を採用した重要な情報システムを構築している。

### TLA+による形式仕様

Paxos合意アルゴリズムは、**TLA+（Temporal Logic of Actions）**を使用して形式仕様化され、**TLAPS（TLA+ Proof System）**を使用して書かれた証明が自動的にチェックされている。

#### Basic Paxosの仕様と証明

Lamport、Merz、Doligezは、Basic Paxosの仕様と証明を作成した。この基礎的な作業が、後続のMulti-Paxosやその他の変種の検証の土台となった。

#### Multi-Paxosの形式検証

**概要：**
Lamportの分散合意のためのMulti-Paxosアルゴリズムの形式仕様と検証が記述されている。仕様はTLA+で書かれ、証明はTLAPSを使用して書かれ、自動的にチェックされている。

**アプローチ：**
Lamport、Merz、DoligezによるBasic Paxosの仕様と証明を基礎として、Multi-Paxosとその証明の理解を促進するために、Basic Paxosとの差異を最小化することを目指した。

**主要な技術的貢献：**
- 仕様における重要な変更は、各プロセスに対して2つの数値を含む操作を3要素タプルの集合を含む操作に置き換えること
- これがBasic PaxosとMulti-Paxos間の最小の概念的差異を正確に捉える
- しかし、集合とタプルの扱いのため、証明は大幅に困難になる

**証明の焦点：**
証明は、アルゴリズムの**安全性性質（safety property）**に焦点を当てている。TLAPSはMulti-Paxosの安全性と活性を証明するために使用されており、Multi-Paxosが強一貫性性質を満たすことを確立している。

### Byzantine Paxosの形式検証

**概要：**
Leslie Lamportは、任意の障害を許容するBasic Paxosの変種であるByzantine PaxosのTLA+仕様を書き、それがBasic Paxosを精緻化（refine）することのTLAPSチェック済み証明を作成した。

**証明の状態：**
この定理の安全性部分の形式証明が書かれ、TLAPSプルーフシステムによってチェックされた。TLA+精緻化の安全性性質の証明は、TLAPSプルーフシステムによって完全にチェックされている。

ただし、TLAPSはまだ時相推論を扱えないため、特定のステップの証明は省略されている。

**TLAPSの広範な応用：**
TLAPSは、Byzantine Paxosの正しさ、Memoirセキュリティアーキテクチャ、Pastry分散ハッシュテーブルのコンポーネント、Spire合意アルゴリズムの正しさを証明するために使用されている。

### Paxos関連の自動証明への取り組み

「Towards an Automatic Proof of Lamport's Paxos」という研究では、LamportのPaxosの自動証明に向けた取り組みが紹介されている。

## Raftの形式検証

### Raftアルゴリズムの概要

Raftは、Paxos系アルゴリズムの代替として設計された合意アルゴリズムである。Diego Ongaroによって設計され、**理解しやすさ**と**実装の容易さ**を重視している。

Raftの特徴：
- Paxosと同等の性能を持ちながら、格段の理解しやすさを提供
- ロジック分離することでPaxosよりも理解しやすい
- 安全性が形式的に証明されている
- 複製されたログを管理するための合意アルゴリズム
- システムを構築するための情報がすべて記述されている

**産業採用：**
Raftアルゴリズムは、CockroachDB、TiDB、MongoDBなど多くの分散データベース（NewSQLだけでなく）で利用されている。

### TLA+による形式仕様

Diego OngaroのPh.D.論文には、TLA+で書かれたRaftの形式仕様が含まれており、わずかに更新されたバージョンが公開されている。

**仕様の詳細：**
- Raft合意アルゴリズムのTLA+形式仕様が利用可能（[GitHub: ongardie/raft.tla](https://github.com/ongardie/raft.tla)）
- 仕様は約400行
- 証明の対象として機能
- **Log Completeness Property**がTLA証明システムを使用して機械的に証明されている

### Coq/Verdiによる機械的検証

#### Verdiフレームワーク

**Verdi**は、ワシントン大学によるCoqフレームワークであり、実行可能な分散システムを実装し形式的に検証するためのものである。PLDI 2015で発表された。

**主要な特徴：**

1. **形式性ギャップの回避**: Verdiは、モデルと実装の間の形式性ギャップを避けるCoqツールチェーンを提供する
2. **複数の障害モデル**: Verdiは理想的から現実的までいくつかの異なる障害モデルをサポート
3. **検証済みシステム変換器（VST）**: 共通の耐障害性技法をカプセル化する

**ワークフロー：**
プログラマーは分散システムを仕様化し、4つの定義を提供することで実装する：
- システム内のノードの名前
- ノードが応答する外部入力・出力と内部ネットワークメッセージ
- 各ノードが維持する状態
- 各ノードが実行するメッセージ処理コード

プログラマーは、特定のベースラインネットワークセマンティクスを仮定してシステムが正しいことを証明する。

**実行可能コードへの変換：**
実際のハードウェアでVerdiシステムを実行するために、イベントハンドラコードをOCamlに抽出し、低レベルネットワーク通信を処理するVerdiランタイムライブラリのシムの一つとリンクする必要がある。

#### Raftの線形化可能性の証明

**画期的成果：**
Verdiは、**Raft状態機械複製アルゴリズムの線形化可能性（linearizability）の最初の機械的にチェックされた証明**を提示した。

**証明の規模：**
証明は、5,000行のRaft実装に対して**45,000行の証明コード**（Coq言語での手動注釈）で構成されている。これは、合意プロトコルでの推論の困難さと必要な手動作業を示している。

#### 実装ギャップの対処

Verdiの重要な革新は、実装-仕様ギャップに対処することである：

- **理想化された障害モデルでの検証**: 開発者は最初に理想化された障害モデルの下でアプリケーションを検証できる
- **VST適用**: 検証済みシステム変換器（VST）を適用して、より敵対的な環境で類似の性質を持つことが保証されたアプリケーションを得る
- **追加の証明負担なし**: より現実的な障害モデルへの正しさ保証の転送に追加の証明負担がない

**「Planning for Change」論文：**
Doug Woos、James R. Wilcox、Steve Anton、Zachary Tatlock、Michael D. Ernst、Thomas Andersonによる「Planning for Change in a Formal Verification of the Raft Consensus Protocol」（CPP, 2016年1月）は、Raftの形式検証における変更への計画について述べている。

### 仕様駆動アプローチ（最近の発展）

最近の研究では、仕様駆動アプローチが導入されている：

1. TLA+を使用してRaftを仕様化し、モデル検査器で正しさを検証
2. この検証済み仕様に基づいてプロトコルを実装
3. モデル検査器ツールを使用して実装検証のためのテストケースを自動生成

この「The Development of a TLA+ Verified Correctness Raft Consensus Protocol」というアプローチは、2024年に発表された。

## Zab（ZooKeeper Atomic Broadcast）の形式検証

### Zabプロトコルの概要

Zab（ZooKeeper Atomic Broadcast）は、分散調整サービスZooKeeperのために特別に設計されたアトミックブロードキャストプロトコルであり、経路回復をサポートする。

**用途：**
クラスタ管理、ロードバランシング、データ公開・購読などのシナリオで広く使用され、ZooKeeperのデータ一貫性を保証するための中核アルゴリズムである。

### 形式仕様アプローチ

複数の形式手法がZabプロトコルの検証に適用されている：

#### TLA+による仕様

**モデルベースランタイムトレースチェッキング：**
形式仕様言語TLA+とそのモデル検査ツールTLCに基づくモデルベースランタイムトレースチェッキングシステムが設計され、分散ZooKeeperクラスタの振る舞いに対してオンライン検証を実行する。

**仕様の詳細：**
研究者はZabプロトコルをTLA+でモデル化し、仕様から抽象化された3つの性質をモデル検査器TLCによって検証した：
- 2つの活性性質
- 1つの安全性性質

**階層的仕様：**
研究者は、TLA+で3つのレベルの仕様を段階的に取得した：
1. **プロトコル仕様**: Zabプロトコルを明確に仕様化
2. **システム仕様**: ZooKeeper開発のための文書として機能
3. **テスト仕様**: ZooKeeper実装の探索的テストを導く

**GitHub統合：**
ZooKeeperプロジェクトには、Zabのための TLA+ を使用した形式仕様と検証を提供するプルリクエストがある（ZOOKEEPER-3615、[GitHub PR #1690](https://github.com/apache/zookeeper/pull/1690)）。

**信頼性向上への応用：**
「Leveraging TLA+ Specifications to Improve the Reliability of the ZooKeeper」（arXiv:2302.02703）という研究は、TLA+仕様を活用してZooKeeperの信頼性を向上させる方法を示している。

#### CSP（Communicating Sequential Processes）による検証

**Process Analysis Toolkit（PAT）：**
PAT を利用して、以下の6つの重要な性質を検証：
1. Deadlock Freedom（デッドロックフリー）
2. Divergence Freedom（発散フリー）
3. Data Reachability（データ到達可能性）
4. Consistency（一貫性）
5. Sequentiality（逐次性）
6. Atomicity（原子性）

**CSPによる形式化：**
「Formalization and Verification of the Zab Protocol Using CSP」という研究がこのアプローチを記述している。

## Viewstamped Replicationの形式検証

### プロトコルの概要

Viewstamped Replicationは、分散システムのための最も初期の合意アルゴリズムの一つである。1988年5月にBrian OkiのPh.D.論文で導入され、Paxosの最初の出版より約1年早い。

**設計：**
ログ複製概念と状態機械を中心に設計されている。

### 形式証明の状態

**元々の論文：**
アルゴリズムが2012年に再検討された際、形式的安全性性質が論文に有用な追加であったことが示唆されている。これは、元のViewstamped Replication論文が、他の一部の合意プロトコルとは異なり、包括的な安全性性質の形式証明を含んでいなかったことを示している。

**精緻化マッピングによる分析：**
しかし、精緻化マッピングを通じてViewstamped Replicationの形式分析が行われている。Paxos、Viewstamped Replication、Zabは、クラッシュ障害を伴う非同期環境での高可用性のための複製プロトコルであり、精緻化マッピングがそれらの類似性に関する質問に対処するために使用されている。

**プロトコルの複雑性：**
Viewstamped Replicationは、複数の相互依存するサブプロトコル（正常操作、ビュー変更、状態転送、回復、再構成）から構成されており、これらのサブプロトコルのいずれかを実装する際のエラーは、全体の安全性を損なう可能性がある。

**TLA+による理解：**
「Understand Viewstamped Replication with Rust, Automerge, and TLA+」という研究が、TLA+を使用したViewstamped Replicationの理解を助けている。

### Paxos、Viewstamped Replication、Zabの比較

**「Vive La Différence」論文：**
「Paxos vs. Viewstamped Replication vs. Zab」という論文は、これら3つのプロトコルの詳細な比較を提供している。プロトコルは、簡潔な仕様として表現され、実行可能な実装に段階的に精緻化され、プロトコル実装の設計決定の正しさに対する原則的理解を可能にする。

## IronFleet：実用的分散システムの検証

### 概要

IronFleetは、分散システム実装の安全性と活性を、Dafnyを使用して自動機械検証するための方法論である。TLAスタイルの状態機械精緻化とHoare論理検証のユニークな組み合わせに基づいて、実用的で証明可能に正しい分散システムを構築するための方法論を記述している。

### 検証アプローチ

**3層アーキテクチャ：**
IronFleetは、分散システムの実装と証明を3つの層に構成する：
1. **高レベル仕様層**
2. **分散プロトコル層**
3. **実装層**

**精緻化と検証の組み合わせ：**
- **TLAスタイル状態機械精緻化**を使用してプロトコルレベルの並行性について推論
- **Floyd-Hoaスタイル命令型検証**を使用して実装の複雑性について推論

### 並行性の扱い

IronFleetの主要な革新の一つは、並行分散システムの検証の課題に対処することである。

**原子性の仮定：**
複数のホストでの低レベル操作のインターリーブ実行についての複雑な推論を避けるため、証明はすべての実装ステップが原子的プロトコルステップを実行すると仮定する。

**還元引数（Reduction Argument）：**
実際の実装の実行は原子的ではないため、原子性を仮定する証明が実際のシステムの証明と同等に有効であることを示すために還元引数を使用する。

### 実践的デモンストレーション

IronFleetは、方法論を以下について実証している：
- **Paxosベースの複製状態機械ライブラリ**の複雑な実装
- **リースベースのシャード化キーバリューストア**

**証明された性質：**
- 各システムが簡潔な安全性仕様に従うことを証明
- 望ましい活性要件を証明

**画期的成果：**
IronFleetは、**実用的分散プロトコルと実装の活性性質を機械的に検証した最初のシステム**である。

### 産業への影響

IronFleetの形式検証ツール（TLA+とTLC）は、2005年のリリース前にMicrosoftのXbox 360のハードウェアで使用される一貫性プロトコルの重大なエラーを発見するために使用された。

## 合意の安全性と活性の証明

### 証明技法

数学的技法（集合、関係、一階述語論理を含む）が、一貫性保証を記述し、プロトコルを精度を持って定義するために使用され、正の結果（プロトコルの正しさの証明）と負の結果の両方を証明することが可能になる。

### 安全性証明

**定義：**
安全性性質は、実行で起こらないことが明確に定義された時点で検出可能である。

**Paxos/Raftの例：**
- **合意性（Agreement）**: 2つのノードが異なる値を決定しない
- **妥当性（Validity）**: 決定された値はいずれかのノードが提案した値である

**証明技法：**
- 不変条件の導出と証明
- 状態遷移の安全性分析
- 精緻化マッピング

### 活性証明

**定義：**
活性性質は、すべての実行で最終的に「良いこと」が起こることを保証する。

**課題：**
活性証明は、以下の理由で安全性証明よりも困難である：
- 無限の振る舞いを扱う必要がある
- 公平性仮定（fairness assumptions）が必要
- タイミングや非同期性の仮定が影響する

**IronFleetの貢献：**
IronFleetは、実用的分散プロトコルと実装の活性性質を機械的に検証した最初のシステムであることが特筆される。

### 線形化可能性（Linearizability）

線形化可能性は、並行オブジェクトの正しさ条件であり、すべての操作が瞬時に起こる単一の時点があるように見えることを要求する。

**Verdi/Raftの貢献：**
Verdiは、Raft状態機械複製アルゴリズムの線形化可能性の最初の機械的にチェックされた証明を提示した。

### 強最終一貫性（Strong Eventual Consistency）

**定義：**
最終一貫性は、オブジェクトへのすべての書き込みが停止すれば、最終的にすべてのプロセスが同じ値を読み取ることとして定義される。

**検証：**
Isabelle/HOL対話型証明支援器における、CRDTアルゴリズムの正しさを検証するためのモジュール式で再利用可能なフレームワークが開発されている。ネットワークモデルを形式化に含めることで正しさの問題を回避し、定理がすべての可能なネットワーク振る舞いで成立することを証明している。

## 形式検証の実践的課題

### 証明の規模と複雑性

**Verdi/Raftの例：**
5,000行のRaft実装に対して45,000行の証明コード（9倍）が必要。これは以下を示している：
- 合意プロトコルでの推論の困難さ
- 必要な手動作業の膨大さ
- 専門知識の必要性

### 実装ギャップ

**課題：**
形式仕様と実際の実装の間にはしばしば「ギャップ」が存在する：
- 仕様は理想化された環境を仮定
- 実装は現実の制約（タイミング、I/O、障害モデル）に対処する必要がある

**Verdiの解決策：**
- 検証済みシステム変換器（VST）による段階的精緻化
- OCaml抽出による実行可能コードへの変換
- ランタイムシム（shim）による低レベル通信の処理

### ツールの限界

**TLAPS の限界：**
- まだ時相推論を完全にはサポートしていない
- 一部の証明ステップは手動または省略される

**スケーラビリティ：**
- 大規模システムでは証明が巨大化
- 証明の保守が困難
- 変更への対応コストが高い

### 学習曲線

形式検証ツールの習得には時間がかかる：
- TLA+、Coq、Dafnyなどの言語の学習
- 証明技法の習得
- ドメイン知識（分散システム理論）の必要性

## 最近の発展と将来方向

### AI/LLMの活用

**証明支援：**
「A Case Study on the Effectiveness of LLMs in Verification with Proof Assistants」という最近の研究が、証明支援器を使用した検証におけるLLMの効果についてケーススタディを提供している。

### 仕様駆動開発

TLA+で仕様化→モデル検査で検証→検証済み仕様から実装→自動テスト生成、という仕様駆動アプローチが2024年に提案されている。

### 自動化の進展

「Towards an Automatic Proof of Lamport's Paxos」など、証明の自動化に向けた研究が進行中である。

### 新しい合意プロトコル

**MongoRaftReconfig:**
分散動的再構成プロトコルMongoRaftReconfigの形式的で機械検証されたTLA+安全性証明が提示されている（2022年）。

### ツールの成熟

- TLAPSの時相推論サポートの改善
- Verdiの新しい障害モデルと VST
- より良い統合開発環境とツールチェーン

## 産業での採用事例

### Google

PaxosをBigTable、Chubbyロックサービス、Spannerなどで使用。

### Amazon

DynamoDBなどでPaxos/Raftベースの合意を使用。AWSではTLA+を使用して設計を検証（詳細は「Amazon/AWSのTLA+活用事例」を参照）。

### Microsoft

Azure Cosmos DBでMulti-Paxosを使用。TLA+で形式仕様を作成（GitHubでオープンソース化）。

### Cockroach Labs

CockroachDBでRaftを使用。TLA+で形式検証。

### MongoDB

MongoRaftReconfigプロトコルの形式検証。

### Apache ZooKeeper

Zabプロトコルの形式仕様と検証（TLA+、CSP）。

## まとめ

合意アルゴリズムの形式検証は、分散システムの信頼性向上に不可欠である。Paxos、Raft、Zab、Viewstamped Replicationといった主要なアルゴリズムは、TLA+、Coq/Verdi、Dafny/IronFleetなどのツールを使用して厳密に検証されてきた。

**主要な成果：**

1. **Paxos**: TLA+/TLAPSによるBasic、Multi、Byzantine Paxosの形式証明
2. **Raft**: TLA+仕様、Coq/Verdiによる線形化可能性の機械的証明
3. **Zab**: TLA+とCSPによる複数レベルの仕様と検証
4. **IronFleet**: Paxosベースシステムの安全性と活性の両方の機械的検証

**形式検証の価値：**

- **バグの早期発見**: 実装前の設計段階で微妙なバグを発見
- **正しさの保証**: 数学的に厳密な正しさの証明
- **文書化**: 仕様が正確で曖昧さのない文書として機能
- **変更管理**: 変更の影響を形式的に分析可能

**課題：**

- 証明の規模と複雑性（実装の9倍の証明コード）
- 実装ギャップの克服
- ツールの限界（特に時相推論）
- 高い学習曲線と専門知識の必要性

**将来展望：**

- AI/LLMによる証明支援
- 自動化の進展
- ツールの成熟とユーザビリティ向上
- 仕様駆動開発の普及

合意アルゴリズムの形式検証は、理論から実践へ移行しつつある。Google、Amazon、Microsoft、Cockroach Labsなどの主要企業が本番環境で形式検証された合意アルゴリズムを使用していることは、この技術の実用的価値を実証している。

形式検証は「銀の弾丸」ではないが、分散システムの正しさを保証するための最も強力なツールの一つである。証明のコストは高いが、それによって防がれるバグの重大性を考えれば、重要なシステムへの投資は正当化される。

---

## 主要参考文献とソース

### Paxos形式検証
- [Formal Verification of Multi-Paxos for Distributed Consensus (arXiv:1606.01387)](https://arxiv.org/abs/1606.01387)
- [Towards an Automatic Proof of Lamport's Paxos (arXiv:2108.08796)](https://arxiv.org/abs/2108.08796)
- [Byzantine Paxos Proof - Leslie Lamport](https://lamport.azurewebsites.net/tla/byzpaxos.html)
- [Byzantizing Paxos by Refinement (PDF)](https://lamport.azurewebsites.net/tla/byzsimple.pdf)
- [DrTLAPlus/Paxos/Paxos.tla - GitHub](https://github.com/tlaplus/DrTLAPlus/blob/master/Paxos/Paxos.tla)

### Raft形式検証
- [Raft Consensus Algorithm](https://raft.github.io/)
- [GitHub - ongardie/raft.tla: TLA+ specification for the Raft consensus algorithm](https://github.com/ongardie/raft.tla)
- [In Search of an Understandable Consensus Algorithm (PDF)](https://raft.github.io/raft.pdf)
- [The Development of a TLA+ Verified Correctness Raft Consensus Protocol (2024)](https://link.springer.com/chapter/10.1007/978-981-97-7244-5_40)
- [Planning for Change in a Formal Verification of the Raft Consensus Protocol](https://jamesrwilcox.com/raft-proof.pdf)

### Verdi/Coq
- [GitHub - uwplse/verdi: A framework for formally verifying distributed systems implementations in Coq](https://github.com/uwplse/verdi)
- [Verdi: A Framework for Implementing and Formally Verifying Distributed Systems (PDF)](https://homes.cs.washington.edu/~ztatlock/pubs/verdi-wilcox-pldi15.pdf)
- [GitHub - uwplse/verdi-raft: Raft in Coq using Verdi](https://github.com/uwplse/verdi-raft)
- [Verdi: Formally Verifying Distributed Systems](https://verdi.uwplse.org/)

### IronFleet
- [IronFleet: Proving Practical Distributed Systems Correct (PDF)](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf)
- [Ironclad/ironfleet/README.md - GitHub](https://github.com/microsoft/Ironclad/blob/main/ironfleet/README.md)
- [IronFleet: Proving Practical Distributed Systems Correct - the morning paper](https://blog.acolyer.org/2015/10/15/ironfleet-proving-practical-distributed-systems-correc/)
- [Proving Safety and Liveness of Practical Distributed Systems (PDF)](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet-cacm.pdf)

### Zab/ZooKeeper
- [Specification and Verification of the Zab Protocol with TLA+](https://dl.acm.org/doi/abs/10.1007/s11390-020-0538-7)
- [GitHub - apache/zookeeper PR #1690: ZOOKEEPER-3615](https://github.com/apache/zookeeper/pull/1690)
- [Leveraging TLA+ Specifications to Improve the Reliability of the ZooKeeper (arXiv:2302.02703)](https://arxiv.org/pdf/2302.02703)
- [Formalization and Verification of the Zab Protocol Using CSP](https://www.researchgate.net/publication/376031286_Formalization_and_Verification_of_the_Zab_Protocol_Using_CSP)

### Viewstamped Replication
- [Viewstamped Replication Revisited (PDF)](http://pmg.csail.mit.edu/papers/vr-revisited.pdf)
- [Viewstamped Replication explained](https://blog.brunobonacci.com/2018/07/15/viewstamped-replication-explained/)
- [Vive La Différence: Paxos vs. Viewstamped Replication vs. Zab (PDF)](https://www.cs.cornell.edu/fbs/publications/viveLaDifference.pdf)
- [Understand Viewstamped Replication with Rust, Automerge, and TLA+](https://medium.com/@polyglot_factotum/understand-viewstamped-replication-with-rust-automerge-and-tla-7a94e9e4d553)

### 安全性・活性・FLP
- [Consensus (computer science) - Wikipedia](https://en.wikipedia.org/wiki/Consensus_(computer_science))
- [Different Perspectives on FLP Impossibility (arXiv:2210.02695)](https://arxiv.org/html/2210.02695v9)
- [Safety and Liveness — Blockchain in the Point of View of FLP Impossibility](https://medium.com/codechain/safety-and-liveness-blockchain-in-the-point-of-view-of-flp-impossibility-182e33927ce6)
- [Verifying Strong Eventual Consistency in Distributed Systems (arXiv:1707.01747)](https://arxiv.org/pdf/1707.01747)

### 日本語リソース
- [Raft(分散合意アルゴリズム)について - GitHub Gist](https://gist.github.com/sile/ad435262c17eb79f133d)
- [分散合意アルゴリズム Raft を理解する - Qiita](https://qiita.com/torao@github/items/5e2c0b7b0ea59b475cce)
- [Raft (アルゴリズム) - Wikipedia](https://ja.wikipedia.org/wiki/Raft_(%E3%82%A2%E3%83%AB%E3%82%B4%E3%83%AA%E3%82%BA%E3%83%A0))
- [分散合意アルゴリズム入門：Paxos・Raft・PBFT・PoW/PoSの原理と実装ポイント](https://everplay.jp/column/21759)
