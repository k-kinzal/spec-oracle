# UMLと半形式的仕様

## 1. UMLとは

UML（Unified Modeling Language、統一モデリング言語）は、システム設計を可視化するための標準的な方法を提供する汎用的なビジュアルモデリング言語である。ソフトウェアを中心としたシステムの仕様を記述、可視化、構築、文書化することを目的としている。

### 1.1 基本的特徴

- **汎用性**: オブジェクト指向の汎用的なビジュアルモデリング言語
- **標準化**: OMG（Object Management Group）によって管理される業界標準
- **半形式的性質**: グラフィック記法、厳密な自然言語、形式言語の組み合わせ
- **可視化**: システムのアーキテクチャと設計を可視化する手段

### 1.2 UMLの半形式的性質

UMLは**半形式的（Semi-formal）仕様記述言語**として分類される。これは以下の理由による：

- UMLのメタモデルは、グラフィック記法、（厳密な）自然言語、形式言語の組み合わせで記述される
- 言語構成要素の仕様に自然言語を使用することで、完全に形式的ではなく半形式的となる
- 完全に形式的な言語（Z、VDMなど）と非形式的な自然言語の中間に位置する
- 形式的要素を持ちながらも、技術者以外のステークホルダーにも理解しやすい

## 2. UMLの歴史と標準化

### 2.1 誕生の背景

UMLは、3人の著名な方法論者の協力によって始まった。彼らは総称して「The Three Amigos（三銃士）」と呼ばれる：

- **Grady Booch**: Booch法の開発者
- **James Rumbaugh**: OMT（Object Modeling Technique）の開発者
- **Ivar Jacobson**: OOSE（Object-Oriented Software Engineering）の開発者

### 2.2 開発の経緯

- **1994年10月**: UMLの取り組みが正式に開始。RumbaughがRational SoftwareのBoochに合流
- **初期段階**: BoochとRumbaughがモデルを統合モデルに統合
- **続く段階**: RationalがJacobsonのObjectory社を買収し、彼らのモデルをUMLに統合
- **1996年**: UML Partnersコンソーシアムが組織され、UML仕様の完成とOMGへの提案を推進
- **1997年1月**: UML Partners' UML 1.0ドラフトがOMGに提案
- **1997年8月**: UML 1.1がOMGに提出
- **1997年11月**: OMGがUML 1.1を採択

### 2.3 バージョンの変遷

#### UML 1.x系
- **UML 0.9/0.91（1996年）**: 最初の公開版
- **UML 1.0（1997年1月）**: OMGへの最初の提案
- **UML 1.1（1997年11月）**: OMGによる正式採択
- **UML 1.3, 1.4, 1.5**: バグや問題点の修正を含むマイナーバージョン
- **UML 1.4.2（2005年）**: ISO/IEC 19501:2005として国際標準化

#### UML 2.x系
- **UML 2.0（2004年10月採択、2005年11月完成）**:
  - 新しい図とモデリング要素を追加
  - コンポジット図（Composite Structure Diagram）
  - タイミング図（Timing Diagram）
  - 相互作用概要図（Interaction Overview Diagram）

- **UML 2.5（2015年6月）**: 正式版リリース
- **UML 2.5.1（2021年5月時点の最新版）**

## 3. UMLの図の種類と仕様記述能力

UML 2.2以降、14種類のUML図が定義されている。これらは2つの主要カテゴリに分類される。

### 3.1 構造図（Structural Diagrams）

システムの静的なアーキテクチャ、構造を構成する要素、およびそれらの接続方法を表現する。モデル化されたシステム内のさまざまなオブジェクトを示す。

#### 3.1.1 クラス図（Class Diagram）
- **目的**: アプリケーションの構造の一般的なモデルを作成
- **仕様記述能力**:
  - システムのクラス、属性、メソッドを指定
  - オブジェクト間の関係を定義
  - 継承、集約、関連、依存などの関係を表現
  - 静的な型構造の記述に強力
- **使用場面**: オブジェクト指向設計、データベース設計、システムアーキテクチャ

#### 3.1.2 オブジェクト図（Object Diagram）
- **目的**: 特定の時点でのオブジェクトのインスタンスとその関係を示す
- **仕様記述能力**: 実行時の具体的なオブジェクト構造のスナップショット

#### 3.1.3 コンポーネント図（Component Diagram）
- **目的**: システムの物理的な構成要素とその依存関係を示す
- **仕様記述能力**: ソフトウェアコンポーネントの構造と相互作用を記述

#### 3.1.4 複合構造図（Composite Structure Diagram）
- **目的**: クラスやコンポーネントの内部構造を表現
- **仕様記述能力**: ランタイムの構造的な関係を詳細に記述（UML 2.0で追加）

#### 3.1.5 配置図（Deployment Diagram）
- **目的**: ハードウェアとソフトウェアの物理的な配置を示す
- **仕様記述能力**: システムの物理的なアーキテクチャと配置構成

#### 3.1.6 パッケージ図（Package Diagram）
- **目的**: モデル要素のグループ化と依存関係を表現
- **仕様記述能力**: 大規模システムの組織化と名前空間の管理

#### 3.1.7 プロファイル図（Profile Diagram）
- **目的**: UMLの拡張メカニズムを定義
- **仕様記述能力**: ドメイン固有の拡張とステレオタイプの定義

### 3.2 振る舞い図（Behavioral Diagrams）

システムで何が起こるべきかを示す。オブジェクトがどのように相互作用して機能するシステムを作るかを記述する。

#### 3.2.1 ユースケース図（Use Case Diagram）
- **目的**: システムの機能要求を表現
- **仕様記述能力**:
  - アクターとシステムの相互作用を記述
  - システムの境界と機能範囲を定義
  - 要求仕様の可視化に有効
- **使用場面**: 要求分析、ステークホルダーとのコミュニケーション

#### 3.2.2 アクティビティ図（Activity Diagram）
- **目的**: メソッドの内部振る舞いを記述
- **仕様記述能力**:
  - 内部的に生成されるアクションによって駆動されるフローを表現
  - システムの制御フローを図示
  - 並行処理、分岐、合流を表現
  - ビジネスプロセスやアルゴリズムの記述
- **使用場面**: ワークフロー設計、アルゴリズム記述

#### 3.2.3 状態機械図（State Machine Diagram）
- **目的**: オブジェクトのライフサイクルを示す
- **仕様記述能力**:
  - 時間と外部刺激の変化に応じたクラスの動的振る舞いをモデル化
  - オブジェクトが生涯を通じて通過する状態の順序を示す
  - 状態遷移、イベント、ガード条件を記述
  - リアクティブシステムの振る舞い仕様
- **使用場面**: プロトコル設計、イベント駆動システム

#### 3.2.4 相互作用図（Interaction Diagrams）

相互作用図は振る舞い図のサブセットで、システムのコンポーネント間の制御とデータのフローを強調する。以下の4種類がある：

##### a) シーケンス図（Sequence Diagram）
- **目的**: 時系列でのオブジェクト間の相互作用を示す
- **仕様記述能力**:
  - 相互作用に参加するアクター/オブジェクトと生成されるイベントを時系列で表示
  - ライフライン、メッセージ、実行仕様を表現
  - 単純なランタイムシナリオのグラフィカルな仕様
  - メッセージの順序と非同期通信の記述
- **使用場面**: プロトコル設計、API設計、メソッド呼び出しシーケンス

##### b) コミュニケーション図（Communication Diagram）
- **目的**: オブジェクト間の構造的な関係とメッセージ交換を表現
- **仕様記述能力**: シーケンス図と同様の情報を構造重視で表現

##### c) インタラクション概要図（Interaction Overview Diagram）
- **目的**: 複数の相互作用の制御フローを表現
- **仕様記述能力**: アクティビティ図とシーケンス図を組み合わせた高レベルの記述（UML 2.0で追加）

##### d) タイミング図（Timing Diagram）
- **目的**: 時間制約を持つ相互作用を表現
- **仕様記述能力**: 状態遷移とタイミング制約を詳細に記述（UML 2.0で追加）

### 3.3 各図の仕様記述能力の評価

| 図の種類 | 静的構造 | 動的振る舞い | 相互作用 | 時間制約 | 形式性 |
|---------|---------|------------|---------|---------|-------|
| クラス図 | ◎ | △ | △ | × | ○ |
| シーケンス図 | △ | ◎ | ◎ | ○ | ○ |
| 状態機械図 | × | ◎ | △ | ○ | ◎ |
| アクティビティ図 | × | ◎ | ○ | △ | ○ |
| ユースケース図 | × | ○ | ○ | × | △ |
| コンポーネント図 | ◎ | △ | ○ | × | ○ |
| 配置図 | ◎ | × | × | × | ○ |

◎: 非常に強い、○: 強い、△: 中程度、×: 弱い/該当なし

## 4. OCL（Object Constraint Language）

### 4.1 OCLの概要

OCL（Object Constraint Language）は、UMLモデルに適用される規則を記述する宣言型言語である。IBMで開発され、現在はUML標準の一部となっている。

### 4.2 OCLの目的

- **曖昧さの排除**: 自然言語の曖昧さを持たない
- **複雑な数学の回避**: 複雑な数学の固有の困難さを持たない
- **副作用なしの制約**: 副作用のない制約を表現する形式言語
- **UMLの形式化**: UML自身の意味論を形式化するために使用
- **精密な制約表現**: UMLユーザーがモデルの構造に関する精密な制約を表現する手段

### 4.3 OCLの特徴

- **宣言型**: 手続き型ではなく宣言型の表現
- **型システム**: 強い型システムを持つ
- **コレクション操作**: 集合、バッグ、シーケンスなどの操作をサポート
- **ナビゲーション**: UMLモデル内のオブジェクト間をナビゲート
- **不変条件**: クラスの不変条件（invariant）を記述
- **事前条件・事後条件**: 操作の事前条件（pre-condition）と事後条件（post-condition）を記述

### 4.4 OCLの使用例

```ocl
-- クラスの不変条件
context Person inv:
    self.age >= 0 and self.age <= 150

-- 操作の事前条件と事後条件
context BankAccount::withdraw(amount: Integer)
    pre: amount > 0 and self.balance >= amount
    post: self.balance = self.balance@pre - amount
```

### 4.5 OCLの意味論

OCL自身の形式的意味論が研究されており、UML Object Constraint Languageのフォーマライゼーションに関する研究が行われている。OCL仕様のClause 10では、UMLを使ってOCLの意味論が記述されている。

### 4.6 OCLの標準化

OCLはスタンドアロン言語ではなく、UMLの不可欠な部分である。OCL式はUMLモデルのコンテキスト内に配置される必要がある。仕様はOMG（Object Management Group）によって公式UML標準の一部として維持されている。

- **OCL 2.4**: 2014年2月にリリースされた主要バージョン

## 5. UMLの意味論の曖昧さ問題

### 5.1 根本的な問題

OMG標準で提示されるUMLの意味論は、平易な言語（plain language）で非形式的に定義されている。この形式的意味論の欠如は曖昧さの問題をもたらす。これは、システム開発プロセスの自動化や、検証、モデル検査、変換、コード生成をサポートするツールの設計において特に重要である。

### 5.2 具体的な曖昧さの事例

#### 5.2.1 状態機械図の曖昧さ

研究により、UML 2.0状態機械において、以下の問題が検出されている：

- **29の問題点**: 曖昧さ、矛盾、不必要に強い制限
- **意味の問題**: 6つの状態機械を使って問題のある意味を例示
- **解釈の多様性**: 同じモデルに対して複数の解釈が可能

#### 5.2.2 シーケンス図の曖昧さ

- **UML 2.0での変更**: シーケンス図が大幅に変更され、言語の表現力が大幅に増加
- **意味論の欠如**: 言語の正確な意味論を定義せずに実施された
- **実装の困難**: ツール実装者が独自の解釈を行う必要がある

#### 5.2.3 アクティビティ図の曖昧さ

研究者は、アクティビティの意味論の形式化を試みる際に、以下を指摘している：

- **矛盾**: UML仕様内の矛盾
- **情報不足**: UML仕様における情報の欠如による問題
- **制約の不明確さ**: 制御フローと並行性の意味が不明確

### 5.3 形式化への取り組み

UMLの曖昧さを解決するため、様々な形式化のアプローチが提案されている。

#### 5.3.1 時相論理によるアプローチ

- **目的**: UML状態機械の最も基本的な意味論の側面を形式化
- **手法**: 時相論理（Temporal Logic）を使用
- **利点**: 厳密な数学的基盤を提供

#### 5.3.2 形式言語の統合

研究者は、以下のような形式言語を用いてUMLを補完している：

- **Z言語**: クラス図と統合
- **CSP**: 状態機械図と統合
- **プロセス代数**: アクティビティ図の意味論を定義

#### 5.3.3 メタモデルの形式化

- **目的**: UMLメタモデル自体を形式的に記述
- **手法**: Isabelle/HOL、Coquなどの定理証明器を使用
- **成果**: よりアクセスしやすい形式的仕様

### 5.4 不整合の管理

研究により、UMLモデルにおける不整合の管理に関する系統的レビューが行われている。以下が含まれる：

- **検出**: 不整合の検出手法
- **診断**: 不整合の原因分析
- **解決**: 不整合の解決戦略
- **防止**: 不整合の発生防止

## 6. UMLとフォーマルメソッドの橋渡し

### 6.1 Precise UML（pUML）

**Precise UML（pUML）グループ**は、UML図のための正確な意味モデルを開発するために設立された。

#### 目的
- UML図の基盤となる正確な意味モデルを開発
- 図的変換規則の集合の基礎として使用
- UMLダイアグラムについて形式的推論を可能にする

#### アプローチ
- 数学的技法を利用してUMLモデリング概念の適切な意味論を探求
- 正確で一貫性があり理解可能な方法で意味論を定義するUML意味論文書を開発
- 自然言語で書かれた文書として提供

### 6.2 Foundational UML（fUML）

**Foundational UML（fUML）**は、標準的で正確な実行意味論を持つUMLのサブセットである。

#### 特徴
- **実行可能性**: モデルが従来のプログラミング言語のプログラムと全く同じ意味で実行可能
- **抽象度**: モデリング言語の抽象度と表現力を持つ
- **標準化**: OMGによって標準化

#### 含まれる構成要素
- クラス、関連、データ型、列挙などの構造的モデリング構成要素
- UMLアクティビティを使った振る舞いモデリング能力

#### 参照実装
- オープンソースのfUML Reference Implementationが提供されている
- モデルの実行と検証を可能にする

### 6.3 Executable UML（xUML）

**Executable UML（xUML）**は、単一の主題の振る舞いを実行できるほど詳細に定義できるUMLのプロファイルである。

#### 特徴
- **実行可能性**: 人間だけでなく、テストと検証を通じて実際に実行できる
- **コード生成**: プラットフォーム固有のモデルとターゲットコードに直接完全に変換可能
- **モデル駆動アーキテクチャ**: MDA（Model Driven Architecture）をサポート

#### 使用目的
- UMLモデルを曖昧なく人間の読者によって解釈可能に構築
- 実際の実行を通じてテストと検証
- ターゲットコードへの直接的かつ完全な翻訳

#### ドメインベースモデリング
- システムのドメイン（アスペクトや関心事）の識別が必要
- 各ドメインは概念的実体が住む自律的世界
- 各ドメインは他のドメインから独立してモデル化可能（関心の分離）

#### アクション言語
- xUMLはAction Semantic Languageを使用してモデルアクションを指定
- モデル実行を可能にする

### 6.4 MDA（Model Driven Architecture）との関係

**MDA**は、プログラミング言語やプラットフォームなどの技術から独立してシステムを設計・構築するためのフレームワークである。

#### Executable UMLとMDAの関係
- Executable UMLは、MDAが誕生した際に使用されたUMLプロファイル
- プラットフォーム独立モデル（PIM: Platform Independent Model）の仕様をサポート
- PIMからプラットフォーム固有モデル（PSM: Platform Specific Model）へのコンパイルをサポート

### 6.5 形式手法との統合アプローチ

#### UMLと形式手法の組み合わせ
- **抽象的なモデリング**: UML状態図でシステムオブジェクトの振る舞いを抽象的にモデル化
- **詳細化**: 各状態図にfUMLアクティビティ図の形で実装決定を追加
- **検証**: 形式手法のツールで検証

#### 利点
- UMLの表現力と理解しやすさ
- 形式手法の厳密性と検証能力
- ツールサポートの活用

## 7. SysML（Systems Modeling Language）

### 7.1 SysMLの概要

SysML（Systems Modeling Language）は、システムエンジニアリングアプリケーションのための汎用モデリング言語で、広範なシステムやシステム・オブ・システムズの仕様、解析、設計、検証、妥当性確認をサポートする。

### 7.2 UMLとの関係

- **UMLの拡張**: SysMLは、UMLのプロファイルメカニズムを使用したUMLのサブセットの拡張として定義される
- **開発主体**: Object Management Group（OMG）とInternational Council on Systems Engineering（INCOSE）の協力により開発
- **起源**: 2001年1月にINCOSEのModel Driven Systems Design作業部会がUMLをシステムエンジニアリングアプリケーション向けにカスタマイズする決定を行ったことに始まる

### 7.3 UMLに対する改善点

SysMLは、ソフトウェアモデリング言語として開発されたUMLに対して、システムエンジニアリング固有の改善を提供する：

- **制限の除去**: UMLのソフトウェア中心の制限を除去
- **新しい図**: 2つの新しい図タイプを追加
  - 要求図（Requirements Diagram）
  - パラメトリック図（Parametric Diagram）

### 7.4 SysMLの特徴

#### サイズと複雑さ
- **小規模言語**: 比較的小さく、学習と適用が容易
- **図の削減**: UML 2の14図のうち7図を使用し、2図を追加
- **構成要素の削減**: UMLのソフトウェア中心の構成要素を多数削除

#### モデリング範囲
SysMLは以下を含む広範なシステムをモデル化可能：
- ハードウェア
- ソフトウェア
- 情報
- プロセス
- 人員
- 設備

### 7.5 SysMLの図タイプ

SysMLは9つの図タイプを持つ：

#### UMLから継承した図（7つ）
1. アクティビティ図
2. シーケンス図
3. ステートマシン図
4. ユースケース図
5. ブロック定義図（UMLのクラス図に相当）
6. 内部ブロック図（UMLの複合構造図に相当）
7. パッケージ図

#### SysML固有の図（2つ）
1. **要求図（Requirements Diagram）**: システム要求とその関係を表現
2. **パラメトリック図（Parametric Diagram）**: パラメータ間の制約を表現（性能解析、トレードオフ分析）

## 8. UMLの限界と批判

### 8.1 アジャイル開発との緊張関係

#### 原則の不一致
- **Big Upfront Design**: UMLは、プロジェクト開始前に要求と設計を定めるアプローチに最適
- **変化への対応困難**: まだ完全に記述されていない製品に対して作業を行うため、スケジュール設定が困難
- **文書化の優先度**: UMLスキーマは、動作するソフトウェアを優先する際に、常に適応・更新が最も容易な文書形式ではない
- **時間の消費**: 作業中のソフトウェアが優先される場合、UML作成に時間がかかる

#### アジャイル実践との相性
研究や議論により、アジャイル環境におけるUML図の価値は限定的であり、プロジェクトが進行中にダイアグラムを継続的に更新する努力は、その努力に見合わない可能性があると指摘されている。

### 8.2 保守とメンテナンスの負担

#### 作成と維持のコスト
- **作成の労力**: UMLダイアグラムの作成には、かなりの労力、スキル、ツールサポートが必要
- **同期の必要性**: UMLダイアグラムは、変化するコードや要求と同期させる必要があり、コストがかかる
- **セットアップと維持**: ソフトウェアコードとの同期には、セットアップと維持に時間が必要で、ソフトウェア開発プロジェクトに作業を追加

#### 実務での現実
ソフトウェアエンジニアリングの実践では、ほとんどの実践者は形式的なUML仕様を使用せず、代わりに非形式的な手書き図を使用するが、これらはしばしばUML要素を含む。

### 8.3 過度な分析とフォーカスの喪失

#### 設計への過度な重点
- **過剰分析**: UML図でソフトウェアスコープを見ることで、ソフトウェアプロジェクトのステークホルダーが問題を過剰分析する可能性
- **フォーカスの喪失**: ソフトウェア機能に過度な時間と注意を費やすことで、人々がフォーカスを失う原因となる
- **設計への偏重**: UMLは設計に多くの重点を置き、一部の開発者や企業にとって問題となる

### 8.4 カバレッジの不十分さ

#### UMLの限界
- **不十分性**: UMLは十分ではなく、UMLで定義されたアーティファクトにモデリングレパートリーを制限すると、他の技法の潜在的な生産性向上を放棄することになる
- **他の技法の必要性**: 効果的なモデリングには、UML以外の技法やアーティファクトも必要

### 8.5 複雑さと管理の問題

#### 図の複雑化
- **圧倒的な複雑さ**: ソフトウェア開発と併せてUML図を作成する際、図が圧倒的または過度に複雑になる可能性があり、開発者にとって混乱と欲求不満の原因となる
- **完全性の不可能**: 開発者は、ソフトウェアツールのすべてのシナリオを図にマッピングすることは不可能
- **スケーラビリティの問題**: 大規模システムでは図の管理が困難

### 8.6 創造者の見解

UMLの創造者自身も、UMLの現状と将来について様々な意見を持っている。いくつかの批判的な視点も示されている。

## 9. UMLの実用性と現代的位置づけ

### 9.1 実用的な価値

#### 適用場面
UMLは以下の場面で特に有効である：

- **コミュニケーション**: チーム間、ステークホルダー間の共通言語
- **設計の文書化**: アーキテクチャの可視化と文書化
- **初期設計**: システムの初期設計段階での構造把握
- **教育**: ソフトウェアエンジニアリングの教育ツール

#### 選択的使用
現代の実践では、以下のようなアプローチが推奨される：

- **必要な図だけを作成**: すべての図を作成するのではなく、価値のある図だけを選択
- **軽量な使用**: 詳細すぎない、スケッチレベルの使用
- **ツールの適切な選択**: ホワイトボード、簡易ツール、専門ツールの使い分け
- **継続的更新の回避**: 毎回更新するのではなく、必要時に再作成

### 9.2 形式手法との補完関係

UMLは完全に形式的ではないが、以下の役割で形式手法と補完関係にある：

- **入口**: 形式手法への入口として機能
- **可視化**: 形式的仕様の可視化手段
- **OCLによる強化**: OCLで制約を追加することで形式性を向上
- **fUML/xUMLへの発展**: 実行可能なモデルへの進化

### 9.3 産業での採用

#### 採用されている分野
- **エンタープライズアーキテクチャ**: 大規模システムの全体設計
- **組込みシステム**: SysMLとの組み合わせ
- **ソフトウェアアーキテクチャ**: 高レベルの構造設計
- **要求管理**: ユースケース図を中心とした要求定義

#### 限定的な採用の理由
- アジャイル開発の普及
- ドキュメント維持コスト
- ツールの複雑さ
- 代替手法の出現（DSL、軽量記法など）

## 10. まとめ

### 10.1 UMLの位置づけ

UMLは**半形式的仕様記述言語**として、完全に形式的な言語（Z、VDM、TLA+など）と非形式的な自然言語の中間に位置する。この中間的な性質が、UMLの最大の強みであり同時に限界でもある。

#### 強み
- **理解しやすさ**: グラフィカルな記法により、技術者だけでなく非技術者も理解可能
- **標準化**: 業界標準として広く認識されている
- **ツールサポート**: 多数のツールが利用可能
- **表現力**: 14種類の図により多様な視点を表現
- **拡張性**: プロファイルメカニズムによる拡張が可能

#### 限界
- **曖昧さ**: 意味論が非形式的で曖昧さが残る
- **検証の困難**: 形式的検証が困難（OCL、fUMLを除く）
- **保守コスト**: ダイアグラムの維持に労力が必要
- **アジャイルとの摩擦**: 軽量・迅速な開発スタイルとの相性が悪い
- **過剰な複雑さ**: 14種類の図すべてを使うと複雑化

### 10.2 適切な使用方法

#### 推奨されるアプローチ
1. **選択的使用**: 必要な図だけを作成（通常は5-7種類程度）
2. **適切な詳細度**: 過度に詳細にせず、理解に必要な情報のみ
3. **OCLの活用**: 制約が重要な場合はOCLで補完
4. **fUML/xUMLの検討**: 実行可能性や検証が必要な場合
5. **形式手法との組み合わせ**: 重要部分は形式的手法で補完

#### 避けるべきアプローチ
1. すべての図を完璧に作成しようとする
2. コードとの完全な同期を維持しようとする
3. UMLだけで完全な仕様を表現しようとする
4. 形式的検証が必要な場合にUMLだけに依存する

### 10.3 今後の展望

#### 進化の方向性
- **実行可能性の向上**: fUML、xUMLの発展
- **形式手法との統合**: 意味論の形式化の進展
- **ツールの改善**: AI支援、自動検証の統合
- **軽量化**: 簡略化されたプロファイルの普及
- **ドメイン特化**: SysMLのような特定分野向け拡張

#### 課題
- アジャイル開発との共存方法
- 意味論の曖昧さの解消
- 保守コストの削減
- 形式的検証能力の向上

UMLは完璧ではないが、適切に使用すれば、ソフトウェアとシステムの設計における価値あるツールである。その半形式的性質を理解し、強みを活かし限界を補完することで、効果的に活用できる。

## 参考文献・出典

### UML基礎
- [統一モデリング言語 - Wikipedia](https://ja.wikipedia.org/wiki/%E7%B5%B1%E4%B8%80%E3%83%A2%E3%83%87%E3%83%AA%E3%83%B3%E3%82%B0%E8%A8%80%E8%AA%9E)
- [Unified Modeling Language - Wikipedia](https://en.wikipedia.org/wiki/Unified_Modeling_Language)
- [UML (統一モデリング言語) とは? 入門最適ガイド - Lucidchart](https://www.lucidchart.com/pages/ja/what-is-UML-unified-modeling-language)
- [What is a UML Diagram? | Miro](https://miro.com/diagramming/what-is-a-uml-diagram/)
- [What Is a UML Diagram: Types, Examples, and Uses | Atlassian](https://www.atlassian.com/work-management/project-management/uml-diagram)

### UML図の種類
- [UML Diagram Types | Learn About All 14 Types of UML Diagrams - Creately](https://creately.com/blog/diagrams/uml-diagram-types-examples/)
- [UML 2.5 Diagrams Overview](https://www.uml-diagrams.org/uml-25-diagrams.html)
- [Unified Modeling Language (UML) Diagrams - GeeksforGeeks](https://www.geeksforgeeks.org/system-design/unified-modeling-language-uml-introduction/)
- [UML - Behavioral Diagram vs Structural Diagram - Visual Paradigm](https://www.visual-paradigm.com/guide/uml-unified-modeling-language/behavior-vs-structural-diagram/)
- [UML sequence diagrams overview - UML Diagrams](https://www.uml-diagrams.org/sequence-diagrams.html)
- [UML activity diagrams - UML Diagrams](https://www.uml-diagrams.org/activity-diagrams.html)

### OCL
- [Object Constraint Language - Wikipedia](https://en.wikipedia.org/wiki/Object_Constraint_Language)
- [Object Constraint Language Version 2.4 - OMG](https://www.omg.org/spec/OCL/2.4/PDF)
- [UML - Object Constraint Language (OCL) - Tutorialspoint](https://www.tutorialspoint.com/uml/uml_object_constraint_language.htm)
- [The Ultimate Object Constraint Language (OCL) tutorial](https://modeling-languages.com/ocl-tutorial/)
- [On Formalizing the UML Object Constraint Language OCL | Springer](https://link.springer.com/chapter/10.1007/978-3-540-49524-6_35)

### UML意味論と曖昧さ
- [15 Interpretation Problems in the Semantics of UML 2.5.1 Activities | Springer](https://link.springer.com/chapter/10.1007/978-3-319-99981-4_25)
- [UML 2.0 Sequence Diagrams' Semantics](https://home.mit.bme.hu/~micskeiz/sdreport/uml-sd-semantics.pdf)
- [Managing Inconsistencies in UML Models: A Systematic Literature Review](https://www.jsoftware.us/vol12/263-JSW15240.pdf)
- [Formalizing UML State Machine Semantics for Automatic](https://www.comp.nus.edu.sg/~pat/uml/techreport/uml_sm_semantics.pdf)

### UMLと形式手法
- [The UML as a Formal Modeling Notation | Springer](https://link.springer.com/chapter/10.1007/978-3-540-48480-6_26)
- [Developing the UML as a Formal Modelling Notation](https://arxiv.org/pdf/1409.6928)
- [Defining Precise Semantics for UML | Springer](https://link.springer.com/chapter/10.1007/3-540-44555-2_10)
- [Foundational UML (fUML) Reference Implementation](https://modeldriven.github.io/fUML-Reference-Implementation/)
- [Executable UML - Wikipedia](https://en.wikipedia.org/wiki/Executable_UML)

### SysML
- [Systems modeling language - Wikipedia](https://en.wikipedia.org/wiki/Systems_modeling_language)
- [What is SysML? | OMG SysML](http://www.omgsysml.org/what-is-sysml.htm)
- [UML Diagrams vs. SysML Diagrams | Lucidchart](https://www.lucidchart.com/blog/uml-diagrams-vs-sysml-diagrams)
- [SysML FAQ: What is the relation between SysML and UML?](https://sysml.org/sysml-faq/what-is-relation-between-sysml-and-uml.html)

### UML歴史
- [UML 2001: A Standardization Odyssey - ACM](https://cacm.acm.org/research/uml-2001/)
- [History Of Unified Modeling Language (UML) - StudySection](https://studysection.com/blog/history-of-unified-modeling-language-uml/)

### UML批判
- [Be Realistic About the UML: It's Simply Not Sufficient - Agile Modeling](http://agilemodeling.com/essays/realisticUML.htm)
- [How Agile is UML actually? | Medium](https://medium.com/@frederik_62300/how-agile-is-uml-actually-1df9546ab7ed)
- [Is UML Still Relevant Today? - Managed Agile](https://managedagile.com/is-uml-still-relevant-today/)
- [What are the benefits and challenges of using UML in agile development? - LinkedIn](https://www.linkedin.com/advice/3/what-benefits-challenges-using-uml-agile-development)

### MDA
- [Executable UML: A Foundation for Model-Driven Architecture - Amazon](https://www.amazon.com/Executable-UML-Foundation-Model-Driven-Architecture/dp/0201748045)
- [Model-driven architecture - Wikipedia](https://en.wikipedia.org/wiki/Model-driven_architecture)
