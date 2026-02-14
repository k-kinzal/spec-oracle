# ゴール指向要求工学（Goal-Oriented Requirements Engineering）

## 概要

ゴール指向要求工学（Goal-Oriented Requirements Engineering, GORE）は、システムが達成すべき目標（ゴール）を起点として要求を分析・導出する要求工学の一アプローチである。従来の機能中心のアプローチとは異なり、「何を達成したいのか」「どういった体験が欲しいか」というゴールやニーズから出発し、それを段階的に詳細化して要求仕様を導出する。

GOREは、要求の完全性、一貫性、トレーサビリティを向上させ、ステークホルダー間の合意形成を支援する強力な手法として、1990年代から発展してきた。代表的な手法にKAOS、i*（iStar）、NFRフレームワークがあり、それぞれ異なる視点と形式化のレベルでゴールモデリングにアプローチする。

## ゴール指向要求工学の基本概念

### ゴールとは何か

ゴールとは、システムが達成すべき状態や性質を記述したものである。GOREでは、ゴールを起点として要求を体系的に導出することで、「なぜその要求が必要なのか」という根拠を明確にし、要求の妥当性を検証可能にする。

ゴールは以下のような階層構造を持つ：

- **高レベルゴール（戦略的ゴール）**: ビジネス目標や組織の使命に対応する抽象的なゴール
- **中レベルゴール**: 高レベルゴールを達成するための具体的な方策
- **低レベルゴール（要求）**: 単一のエージェント（人間、デバイス、ソフトウェア）が実現可能な操作的なゴール

### ゴールと要求の関係

要求は本質的に「細分化されたゴール」であり、ゴールの具体化である。ゴール指向アプローチでは、トップゴールから始めて段階的に詳細化（リファインメント）を繰り返し、最終的に単一のエージェントが達成可能なレベルまで分解する。このプロセスにより、要求とビジネス目標の間の明確なトレーサビリティが確立される。

### ゴールの分類

ゴールは性質によって以下のように分類される：

1. **機能ゴール（Functional Goals）**: システムが提供すべきサービスや機能
2. **非機能ゴール（Non-Functional Goals / Quality Goals）**: システムの品質特性（性能、セキュリティ、使用性など）
3. **ソフトゴール（Softgoals）**: 明確な充足条件を持たない、程度の問題として扱われるゴール

また、時間的性質による分類もある：

- **Maintain ゴール（安全性）**: ある状態を常に維持する（□(P→Q)）
- **Achieve ゴール（活性性）**: ある状態をいずれ達成する（P→◊Q）
- **Avoid ゴール（安全性）**: ある状態を決して起こさない（□(P→¬Q)）

## 主要なGORE手法

### KAOS（Keep All Objectives Satisfied）

KAOSは、ベルギーのルーヴァン・カトリック大学とオレゴン大学で1990年にAxel van Lamsweerdeらによって開発された、最も形式的なGORE手法の一つである。

#### KAOSの特徴

1. **二層アプローチ**: 半形式的なグラフィカル表現と形式的な時相論理による記述を組み合わせる
2. **AND/OR分解**: ゴールを部分ゴールに段階的に分解し、AND精緻化（すべての部分ゴールを満たせば親ゴールが満たされる）とOR精緻化（いずれかの代替案で親ゴールが満たされる）を用いる
3. **エージェントへの責任割当**: 詳細化されたゴールを、それを実現できるエージェント（人間、デバイス、ソフトウェアコンポーネント）に割り当てる
4. **形式的検証**: リアルタイム時相論理を用いて、ゴール精緻化の妥当性やゴール間の矛盾を検証できる

#### KAOSの主要概念

- **ゴール（Goal）**: 達成すべき目標の形式的記述
- **エージェント（Agent）**: ゴールを実現する能動的な要素（人間、ソフトウェア、デバイス）
- **オブジェクト（Object）**: エージェントが操作する受動的な要素
- **操作（Operation）**: エージェントが実行する行動
- **制約（Constraint）**: システムやドメインに関する不変条件
- **障害（Obstacle）**: ゴールの達成を妨げる状況

#### ゴールのオペレーショナル化

KAOSの中核的なプロセスは、ゴールを操作的な仕様（operationalization）に変換することである。これは、高レベルのゴールから、操作の事前条件・事後条件・トリガー条件を導出し、それらがドメイン理論と組み合わさることでゴールが満たされることを形式的に証明するプロセスである。

KAOSでは、ドメインの事前・事後条件（indicative：現実の記述）と、望ましい事前・事後条件（optative：要求の記述）を区別する。後者は、ゴールを確実に満たすために条件を強化したものである。

#### 障害分析（Obstacle Analysis）

KAOSの特徴的な技法として、障害分析がある。障害とは、ゴールや要求が満たされない状況を形式的に定義したものである。障害を同定し、それをAND/OR分解して精緻化することで、フォールトツリー分析に類似したリスク分析を行い、より完全で堅牢な要求仕様を導出できる。

障害分析のプロセス：
1. ゴールの否定から障害を導出
2. 障害をAND/OR分解して根本原因を特定
3. 障害を解消または軽減するための対策ゴールを導入
4. 対策ゴールをシステム要求として詳細化

#### KAOSのツールサポート

KAOSを支援する主なツールとして、Objectiverがある。ただし、2023年現在、産業界での広範な採用は限定的であり、主に大学での教育に使われている。

### i*（iStar）フレームワーク

i*（アイスター）は、トロント大学のEric Yuらによって開発された、組織環境とそのステークホルダーの戦略的関係をモデリングする手法である。名前の「i*」は「分散した意図性（distributed intentionality）」を意味する。

#### i*の特徴

i*は、KAOSよりも社会的・組織的側面に焦点を当て、アクター間の依存関係と戦略的推論を重視する。システムを孤立した技術要素としてではなく、意図・動機・信念を持つ社会的アクターの相互作用として捉える。

#### i*の主要モデル

**1. 戦略的依存（Strategic Dependency, SD）モデル**

アクター間の依存関係を記述する。依存は以下の要素で構成される：

- **Depender（依存者）**: 何かを必要とするアクター
- **Dependee（被依存者）**: その必要を満たす能力を持つアクター
- **Dependum（依存対象）**: 依存される目標、タスク、リソース、またはソフトゴール

依存の種類：
- ゴール依存：目標の達成を依存
- タスク依存：特定の活動の実行を依存
- リソース依存：物理的・情報的リソースの提供を依存
- ソフトゴール依存：品質特性の実現を依存

**2. 戦略的根拠（Strategic Rationale, SR）モデル**

SDモデルがアクター間の外部関係を記述するのに対し、SRモデルはアクター内部の意図的構造を記述する。各アクターが依存関係を持つ理由と、内部でどのように目標を達成するかの戦略を明示する。

SRモデルの要素：
- **Goal（ゴール）**: 達成すべき状態
- **Task（タスク）**: 目標を達成するための具体的活動
- **Resource（リソース）**: 必要な物理的・情報的資源
- **Softgoal（ソフトゴール）**: 品質基準や非機能要件
- **Means-ends links（手段-目的リンク）**: タスクがゴールを達成する手段であることを示す
- **Task decomposition（タスク分解）**: タスクを部分タスクに分解

#### 機会と脆弱性の分析

i*の重要な概念として、依存による「機会（opportunity）」と「脆弱性（vulnerability）」がある。他者に依存することで、自分では達成困難な目標を実現できる機会を得る一方、依存相手が失敗すればシステム全体が影響を受ける脆弱性が生じる。

依存の強度は3段階で表現され、脆弱性のレベルを示す：
- 弱い依存：代替手段が容易に存在する
- 中程度の依存：代替手段は限定的
- 強い依存：代替手段がない、または非常に困難

#### iStar 2.0

2016年に発表されたiStar 2.0は、i*の核心概念を洗練し、より一貫性のある透明な原則セットを確立した改良版である。コアランゲージとして明確に定義され、jUCMNavなどのツールでサポートされている。

### NFRフレームワーク（Non-Functional Requirements Framework）

NFRフレームワークは、Lawrence Chungらによって開発された、非機能要求（Non-Functional Requirements, NFR）を体系的に扱うためのゴール指向手法である。

#### NFRフレームワークの特徴

NFRフレームワークは、性能、セキュリティ、使用性、保守性といった非機能要求を「ソフトゴール」として扱う。ソフトゴールは、完全に満たすことが困難であり、「十分に満たされた（satisficed）」かどうかを程度の問題として判断する。

#### ソフトゴール相互依存グラフ（Softgoal Interdependency Graph, SIG）

SIGは、NFRフレームワークの中核となるモデリング記法である。ソフトゴールとその間の精緻化関係や貢献関係を視覚的に表現する。

**ソフトゴールの種類：**
- **NFRソフトゴール**: 非機能要求そのもの（例：「システムのセキュリティ[高]」）
- **操作化ソフトゴール**: NFRを実現するための具体的手段（例：「暗号化を使用する」）
- **主張ソフトゴール（Claim）**: 設計判断の根拠や仮定（例：「HTTPSで十分なセキュリティが得られる」）

**貢献リンクの種類：**
- **MAKE（++）**: 子が満たされれば親は確実に満たされる（強い正の貢献）
- **HELP（+）**: 子が満たされれば親は部分的に満たされる（正の貢献）
- **HURT（-）**: 子が満たされると親は部分的に満たされなくなる（負の貢献）
- **BREAK（--）**: 子が満たされると親は確実に満たされなくなる（強い負の貢献）
- **SOME（?）**: 貢献の方向や程度が不明

#### Satisficing（充足化）の概念

NFRフレームワークでは、すべてのNFRを「完全に達成する」のではなく「十分に満たす（satisfice）」ことを目指す。これは、Herbert Simonの意思決定理論に由来する概念である。ソフトゴールは以下のようなラベルを持つ：

- **Satisficed（満足化された）**: 十分に満たされている
- **Weakly Satisficed（弱く満足化された）**: ある程度満たされている
- **Weakly Denied（弱く否定された）**: ある程度満たされていない
- **Denied（否定された）**: 満たされていない
- **Unknown（不明）**: 満足度が評価できない

これらのラベルは、SIGのボトムアップ評価（operationalizationから伝播）によって決定される。

#### NFR型とパターン

NFRフレームワークは、典型的なNFRの精緻化と解決策を「NFR型」として予めパターン化し、再利用することで網羅的な分析を支援する。例えば、「セキュリティ」NFRは「機密性」「完全性」「可用性」に標準的に分解でき、それぞれに対する典型的な操作化手法（暗号化、アクセス制御、冗長化など）が知られている。

### 手法の比較

| 側面 | KAOS | i* | NFRフレームワーク |
|------|------|-----|-------------------|
| **焦点** | システム機能とエージェント | 組織とステークホルダーの戦略 | 非機能品質特性 |
| **形式化レベル** | 高（時相論理） | 中（半形式的） | 中（定性的推論） |
| **主要概念** | ゴール精緻化、障害 | 依存、機会と脆弱性 | ソフトゴール、貢献 |
| **エージェント** | ソフトウェア中心 | 人間と組織中心 | 設計決定中心 |
| **トレードオフ** | 競合解消パターン | 代替手段の評価 | 貢献の相殺分析 |

## ゴール、ニーズ、体験、仕様の関係

### ゴールとユーザーニーズ

ゴール指向要求工学では、「何を達成したいのか」という問いが出発点となる。これは、ユーザーの真のニーズを捉えるアプローチである。しかし、ユーザー自身が本当のニーズを把握していない場合も多く、表面的な要望（want）と真の必要性（need）を区別する必要がある。

要求工学における3層モデル：
1. **要望（Want / 希望）**: ユーザーやステークホルダーの初期の希望やアイデア
2. **要求（Requirement / 必要性）**: 技術的・組織的文脈を考慮した本質的なニーズ
3. **要件（Specification / 仕様）**: 要求を実現するための具体的な技術的制約と設計

ゴール指向アプローチは、この要望→要求→要件の変換を、ゴールの階層的精緻化としてモデル化する。

### 体験設計とゴール

近年の製品開発では、ユーザーに提供する「体験価値」の設計が重視される。体験設計（Experience Design）では、ユーザージャーニーやシナリオを通じて、ユーザーがどのような文脈でどのような感情や行動を持つかを記述する。

ゴール指向要求工学と体験設計の接点：

1. **ユーザーゴールの抽出**: ユーザージャーニーの各段階で、ユーザーが何を達成しようとしているかを同定
2. **シナリオとゴールの対応**: シナリオの各エピソードは、特定のドメインゴールに対応する
3. **体験品質のソフトゴール化**: 「楽しい」「直感的」といった体験目標をソフトゴールとして扱い、設計判断との貢献関係を分析

### シナリオ仕様：表現と制約の両面

会話で議論された「シナリオ仕様は表現と制約の両面を持つ」という洞察は、ゴール指向要求工学の文脈で以下のように理解できる：

**表現としてのシナリオ：**
- 望ましい挙動や体験の具体例を示す
- ステークホルダー間のコミュニケーションツール
- 要求の源泉となる物語

**制約としてのシナリオ：**
- シナリオを満たすことが要求となる
- シナリオから導出される不変条件や事前・事後条件
- テストケースの基礎

ゴール指向では、シナリオから抽象化されたゴールを導出し、そのゴールを満たす条件を形式的に記述することで、表現と制約の橋渡しをする。

### ゴールから仕様へのトレーサビリティ

ゴール指向アプローチの最大の利点の一つは、ビジネス目標から技術仕様までの明確なトレーサビリティを確立できることである。

**トレーサビリティの利点：**
- **完全性検証**: すべてのゴールが要求によってカバーされているか確認できる
- **一貫性検証**: ゴール間の競合や矛盾を検出できる
- **変更影響分析**: ゴールの変更が下位の要求や設計にどう影響するかを追跡できる
- **正当化**: 各要求が存在する理由を説明できる

要求トレーサビリティマトリクス（RTM）では、ゴール、要求、設計、実装、テストの間のリンクを記録し、完全性と一貫性を継続的に検証する。統計的研究では、トレーサビリティ情報が完全なコンポーネントほど欠陥率が低いことが示されている。

## ゴール指向要求工学の実践

### 要求抽出（Requirements Elicitation）

ゴール指向の要求抽出プロセス：

1. **高レベルゴールの同定**: ビジネス目標、組織の使命、ステークホルダーの期待から開始
2. **ゴールの精緻化**: WHYとHOWの質問を繰り返してゴールを分解
   - WHY: なぜこのゴールが必要か？→ より高レベルのゴール
   - HOW: このゴールをどう達成するか？→ より低レベルのゴール
3. **代替案の探索**: OR精緻化を用いて複数の実現手段を検討
4. **エージェントの同定**: 各ゴールを誰が・何が実現するかを決定
5. **障害の分析**: ゴール達成を妨げる要因を同定し、対策を導出

### インタビューとストーリーテリング

ゴール指向の要求抽出では、「ゴールフォーカスト・インタビュー」が有効である：

- **ストーリーエリシテーション**: ユーザーに過去の経験や望ましい未来の物語を語ってもらい、そこからゴールを抽出
- **Jobs To Be Done (JTBD)**: ユーザーが「雇いたい仕事」の文脈でゴールを理解する
- **5つのWHY**: 表面的な要望から根本的なニーズへ掘り下げる

これらの技法により、ユーザーが明示的に述べない暗黙の目標や制約を発見できる。

### ゴールモデルの検証

ゴールモデルの品質を評価する観点：

- **完全性（Completeness）**: すべての重要なゴールがモデルに含まれているか
- **一貫性（Consistency）**: ゴール間に矛盾がないか
- **実現可能性（Feasibility）**: すべてのゴールが現実的に達成可能か
- **複雑性（Complexity）**: モデルが理解・管理可能な複雑度か

KAOSでは形式的検証により矛盾を自動検出できる。NFRフレームワークでは、貢献の伝播分析によって、設計決定が非機能ゴールに及ぼす影響を評価できる。

### ツールサポート

ゴール指向要求工学を支援するツール：

- **Objectiver**: KAOS専用ツール。ゴールモデルの編集と形式検証をサポート。産業利用は限定的。
- **jUCMNav**: Eclipse基盤のURN（User Requirements Notation）ツール。GRL（Goal-oriented Requirement Language）とUCM（Use Case Maps）を統合サポート。
- **piStar / iStar Tool**: iStar 2.0のWebベースモデリングツール
- **CAIRIS**: セキュリティ要求に特化したGOREツール。GRLモデル生成をサポート
- **GORO Tool**: 異なるGORE手法間のモデル変換ツール（例：iStarからKAOSへ）

### AI・LLMの活用（2024-2025年の動向）

最近の研究では、大規模言語モデル（LLM）をゴールモデル生成に活用する試みが始まっている。2025年の論文では、GPT-4などのLLMを用いて、ユーザーストーリーから自動的にゴールモデル（GRL形式）を生成する手法が提案されている。反復的プロンプトエンジニアリングにより、意図的要素を抽出し、XML表現を生成してjUCMNavで可視化する。

また、持続可能なIoTシステムの文脈では、ゴール指向要求分析（GORA）手法が、機能要求と非機能要求（エネルギー効率、セキュリティなど）を同時に最適化する要求仕様、リソース配分、持続可能性の実現に活用されている（2025年5月）。

## ゴール指向要求工学の課題と限界

### 形式化のコスト

KAOSのような高度に形式的な手法は、厳密な検証を可能にする一方、時相論理の知識や専門ツールの習得が必要であり、実践のハードルが高い。多くのプロジェクトでは、形式化の利益がコストを上回らない場合がある。

### ツールサポートの不足

Objectiverを除けば、KAOSの産業利用を示す証拠は乏しい（2023年時点）。オープンソースツールは存在するが、商用グレードの統合環境は限られている。これは、GORE手法の普及を妨げる要因となっている。

### ソフトゴールの定量化

NFRフレームワークのソフトゴールは定性的であり、「どの程度満たされれば十分か」の客観的基準を欠く。NFR+などの拡張では、測定可能なNFRの概念を導入しているが、主観的な品質属性の定量化は依然として困難である。

### スケーラビリティ

大規模システムでは、ゴールモデルが巨大化し、視覚的に理解困難になる。KAOS論文では、視覚的に効果的なゴールモデルの設計原則が議論されているが、完全な解決策ではない。複雑度メトリクスにより、モデルの管理可能性を評価する研究もある。

### 組織文化との整合性

ゴール指向アプローチは、従来のウォーターフォール型にもアジャイル型にも適用可能だが、組織の文化や開発プロセスとの整合が重要である。特に、「すべての要求の根拠を明示する」という原則は、スピード重視の文化と緊張関係を生む可能性がある。

## ゴール指向要求工学の将来展望

### 形式手法との統合

KAOSの時相論理基盤は、モデル検査や定理証明などの形式検証技術と自然に接続できる。Event-Bへの変換やZ仕様への翻訳の研究があり、ゴールモデルから検証可能な形式仕様への自動生成が進展している（例：CBTCシステムのiStarモデルからZ形式仕様への変換）。

### 法規制への対応

Legal GRLのような拡張により、法規制や標準への準拠をゴールとしてモデル化し、システム要求との関係を明示化する研究が進んでいる。規制要求が頻繁に変更される分野（金融、医療、データプライバシー）では特に有用である。

### AI支援によるゴールモデリング

LLMの進展により、自然言語記述からのゴールモデル自動生成、ゴールの精緻化提案、競合の自動検出などが現実的になりつつある。ただし、生成されたモデルの妥当性検証は人間の専門家が行う必要がある。

### 体験設計との融合

UXデザインとGOREの融合は今後の重要な方向性である。ユーザージャーニーからゴールを抽出し、体験品質をソフトゴールとして定量化し、デザイン決定との貢献関係を分析する統合フレームワークが求められる。

### アジャイル開発への適応

伝統的にGOREは要求の事前分析を重視してきたが、アジャイル開発との融合も進んでいる。プロダクトゴールの設定、ユーザーストーリーからのゴール抽出、スプリント計画へのゴールモデルの活用などが模索されている。

## まとめ

ゴール指向要求工学は、「何を達成したいのか」という根本的な問いから出発し、ビジネス目標から技術仕様までの明確な道筋を提供する強力なアプローチである。KAOS、i*、NFRフレームワークという主要手法は、それぞれ異なる強みを持ち、相互補完的である：

- **KAOS**: 形式的厳密性、システム中心、障害分析
- **i***: 社会的文脈、ステークホルダー関係、戦略分析
- **NFRフレームワーク**: 品質特性、トレードオフ、設計決定

これらの手法は、要求の完全性、一貫性、トレーサビリティを大幅に向上させ、「なぜその要求が必要なのか」を明確にすることで、ステークホルダー間の合意形成と変更管理を支援する。

会話で議論された「ゴール・ニーズの一段下のニュアンス」は、ゴール精緻化の過程で具体化される。「どういった体験が欲しいか」は、体験ゴールやソフトゴールとして表現され、設計決定へとつながる。「シナリオ仕様の表現と制約の両面」は、ゴールモデルを介して統合され、要求の本質と実現手段の間の橋渡しとなる。

ゴール指向要求工学は、単なる技法の集合ではなく、要求を「達成すべき目標」として捉える思考の枠組みであり、仕様を「ゴール達成のための手段」として位置づける哲学である。この視点は、「仕様とは何か」という根本的な問いに、目的論的な答えを提供する：**仕様とは、ゴールを実現するための許容可能な実装の集合を定義するものである**。

---

## 主要参考文献とソース

### KAOS関連
- [KAOS (software development) - Wikipedia](https://en.wikipedia.org/wiki/KAOS_(software_development))
- [Goal-Oriented Requirements Engineering (GORE): KAOS](https://www.utdallas.edu/~chung/SYSM6309/KAOS-AORE.pdf)
- [KAOS Tutorial (2007)](https://www.cse.msu.edu/~cse870/Materials/GoalModeling/KaosTutorial-2007.pdf)
- [Handling Obstacles in Goal-Oriented Requirements Engineering](http://www.cs.ucf.edu/~turgut/heng_than.pdf)
- [Goal-Driven Requirements Engineering: the KAOS Approach](https://webperso.info.ucl.ac.be/~avl/gore.php)
- [Formal refinement patterns for goal-driven requirements elaboration](https://dl.acm.org/doi/10.1145/239098.239131)

### i* / iStar関連
- [i* - Wikipedia](https://en.wikipedia.org/wiki/I*)
- [i* Intentional STrategic Actor Relationships modelling](http://www.cs.toronto.edu/km/istar/)
- [iStar 2.0 Language Guide](https://ar5iv.labs.arxiv.org/html/1605.07767)
- [The i* Framework for Goal-Oriented Modeling](https://www.researchgate.net/publication/305113064_The_i_Framework_for_Goal-Oriented_Modeling)
- [Strategic dependency (SD)](https://ics.uci.edu/~alspaugh/cls/shr/istar.html)

### NFRフレームワーク関連
- [Non-functional requirements framework - Wikipedia](https://en.wikipedia.org/wiki/Non-functional_requirements_framework)
- [Softgoal Interdependency Graphs](https://link.springer.com/chapter/10.1007/978-1-4615-5269-7_3)
- [Extending the NFR Framework with Measurable Non-Functional Requirements](https://ceur-ws.org/Vol-553/paper2.pdf)
- [Quantitative Non Functional Requirements evaluation using softgoal weight](https://jisis.org/wp-content/uploads/2022/11/jisis-2016-vol6-no1-03.pdf)

### GORE一般・比較研究
- [Goal-Oriented Requirements Engineering: An Overview of the Current Research](https://www.cs.utoronto.ca/~alexei/pub/Lapouchnian-Depth.pdf)
- [Comparing GORE frameworks: I-star and KAOS](https://www.researchgate.net/publication/221235167_Comparing_GORE_frameworks_I-star_and_KAOS)
- [Goal-Oriented Requirements Engineering: State of the Art and Research Trend](https://jurnalnasional.ump.ac.id/index.php/JUITA/article/view/9827)
- [Goal-oriented requirements engineering: an extended systematic mapping study](https://link.springer.com/article/10.1007/s00766-017-0280-z)

### ツールサポート
- [Goal and Scenario Modeling, Analysis, and Transformation with jUCMNav](https://www.researchgate.net/publication/224503839_Goal_and_Scenario_Modeling_Analysis_and_Transformation_with_jUCMNav)
- [Generating Goal-oriented Requirements Language models — CAIRIS](https://cairis.readthedocs.io/en/latest/grl.html)
- [GitHub - GORO Tool](https://github.com/nemo-ufes/gorotool)
- [Goal Model Extraction from User Stories Using Large Language Models](https://link.springer.com/chapter/10.1007/978-3-031-70245-7_19)

### 最新研究（2024-2025）
- [Enhancing Sustainable IoT Systems Through a Goal-Oriented Requirements Analysis Framework (2025年5月)](https://www.mdpi.com/2076-3417/15/11/5826)
- [iStar Goal Model to Z Formal Model Translation and Model Checking](https://dl.acm.org/doi/10.1145/3633065)

### トレーサビリティと検証
- [Requirements traceability - Wikipedia](https://en.wikipedia.org/wiki/Requirements_traceability)
- [Requirements Validation Techniques](https://www.geeksforgeeks.org/software-engineering/software-engineering-requirements-validation-techniques/)
- [Traceability Management of Socio-Cyber-Physical Systems](https://www.mdpi.com/2673-3951/4/2/9)

### 実践と体験設計
- [Goal-Oriented Requirements Elicitation to Improve Acceptance and Use](https://www.scitepress.org/papers/2009/22939/22939.pdf)
- [User-Centered Design: Specifying Requirements For a Project](https://agentestudio.com/blog/user-centered-design-specification)
- [Eliciting user goals - Part 1](https://www.userfocus.co.uk/articles/eliciting-user-goals-part1.html)
- [Goal-Oriented Requirements Engineering: Starting from your Product Goal](https://www.eclipsesuite.com/goal-oriented-requirements-engineering/)

### 日本語資料
- [要求工学 第14回：ゴール分析](https://www.bcm.co.jp/site/2005/2005-12/05-yokyu-12/05-yokyu-121.html)
- [ゴール指向要求分析（KAOS法、アイスター）](https://tech.yokohama/6247/)
- [要求工学入門 - ソフトウェア品質シンポジウム2011](https://engineering.linecorp.com/ja/blog/requirement-engineering-intro-software-quality-2011)
- [要求定義のコツ！要求工学知識体系(REBOK)を活用したフレームワーク化](https://qualitycube.jp/2022/12/7/requirements-engineering/)
- [ユーザーの本質的ニーズに辿り着くために必要な3つの視点](https://goodpatch.com/blog/about-user-modeling)
- [システム開発におけるユーザーニーズの重要性と要件定義の最適化](https://service.route06.com/blog/156)
