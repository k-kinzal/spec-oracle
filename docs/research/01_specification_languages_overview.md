# 仕様記述言語の概観

## 1. 仕様記述言語とは

仕様記述言語（Specification Language）は、システムやソフトウェアの仕様を記述するためのコンピュータ言語である。プログラミング言語よりも高い抽象度でシステムを記述し、システムが「何をすべきか」を表現する（「どのように実現するか」ではない）。

形式的仕様記述（Formal Specification）は、数学的に基礎づけられた技術であり、システムやソフトウェアの実装を支援し、システムの振る舞いを記述し、重要な性質を厳密かつ効果的な推論ツールによって検証することを目的とする。

## 2. 仕様記述言語の分類

仕様記述言語は、その形式性の度合いによって以下の3つのカテゴリに分類される。

### 2.1 形式的（Formal）仕様記述言語

数学的に厳密な構文と意味論を持つ言語。曖昧さを排除し、自然言語に固有の多義性を解消する。

#### 特徴
- 論理学や代数学に基づく形式的記述
- 曖昧さのない厳密な意味論
- 自動検証やツールサポートが可能
- 「好ましい性質」の保証や「好ましくない性質」の不存在を証明可能

#### 代表的な言語

**モデルベース仕様記述言語（Model-based Specification）**
- **Z言語（Z notation）**: 集合論と述語論理に基づく。システムの状態を集合、関数、関係で表現
- **VDM-SL（Vienna Development Method - Specification Language）**: 集合、関数、型システムを使ってシステムの状態や振る舞いを数学的に記述。航空、鉄道、金融システムなどの安全性が重視される分野で使用
- **B-Method / Event-B**: 抽象機械記法（AMN: Abstract Machine Notation）を使用。段階的詳細化による仕様開発
- **Alloy**: 軽量な形式手法。リレーショナルロジックに基づくモデル検査
- **TLA+（Temporal Logic of Actions）**: 時相論理に基づく。並行・分散システムの仕様記述に適する

**代数的仕様記述言語（Algebraic Specification）**
- 抽象データ型（ADT）の記述に適する
- 構文部分：演算のシグネチャ（名前、入力、出力、定義域、値域）
- 意味部分：公理や等式による演算間の関係定義
- オブジェクト指向設計のクラスやインターフェースの記述に応用可能

**プロセス代数・並行システム仕様記述言語**
- **LOTOS（Language Of Temporal Ordering Specification）**: 並行システムや通信プロトコルの仕様記述に特化。通信プロトコル、分散システム、リアルタイムシステムの設計に利用
- **CSP（Communicating Sequential Processes）**: Tony Hoareによって1978年に提唱。並行システムの相互作用パターンを記述
- **SDL（Specification and Description Language）**: リアクティブ・分散システムの振る舞いを曖昧さなく記述。元々は通信システムのプロトコル仕様記述法だったが、現在はプロセス制御やリアルタイムアプリケーションにも使用

**時相論理ベース言語（Temporal Logic-based Languages）**
- **LTL（Linear Temporal Logic）**: 線形時相論理。Amir Pnueliが1977年にコンピュータプログラムの形式検証のために提案
- **CTL（Computational Tree Logic）**: 計算木論理。Clarke and Emersonによって開発
- **CTL***: LTLとCTLを組み合わせたもの。1986年にEmerson and Halpernによって定義

**アサーションベース仕様記述**
- **Hoare Logic**: プログラムの正当性を証明するための論理体系。事前条件と事後条件によるプログラム検証

### 2.2 半形式的（Semi-formal）仕様記述言語

形式的要素とグラフィカル記法、自然言語記述を組み合わせた言語。

#### 特徴
- 完全に形式的ではないが、一定の構造を持つ
- グラフィック記法と自然言語を併用
- 技術者以外のステークホルダーにも理解しやすい
- UMLのメタモデルは、グラフィック記法、（厳密な）自然言語、形式言語の組み合わせで記述されており、自然言語を使用することで半形式的となる

#### 代表的な言語
- **UML（Unified Modeling Language）**: ソフトウェア開発やシステムエンジニアリング、鉄道システムモデリング、サプライチェーン管理、ビジネスプロセスモデリングなどで使用される半形式的グラフィカル言語
- **OCL（Object Constraint Language）**: UMLモデルに適用される規則を記述する宣言型言語。IBMで開発され、現在はUML標準の一部。自然言語の曖昧さと複雑な数学の困難さのどちらも持たない表現を提供
- **SysML（Systems Modeling Language）**: マルチテクノロジーシステムのシステムエンジニアリングに適用されたUML。システム仕様、要求定義とトレーシング、システム開発、テスト、検証・妥当性確認、および開発チーム間のコミュニケーションに使用

### 2.3 非形式的（Informal）仕様記述言語

自然言語（日本語、英語など）を使った要求仕様記述。

#### 特徴
- 構造化されていない自然言語を使用
- 非技術的なステークホルダーにとって理解しやすく、アクセスしやすい
- ステークホルダー間のコミュニケーションを促進

#### 欠点
- 矛盾（contradictions）
- 曖昧さ（ambiguities）
- 漠然とした表現（vagueness）
- 不完全な記述（incomplete statements）
- 解釈の多様性によるリスク

## 3. 仕様記述言語の歴史的発展

### 3.1 初期の発展（1960年代〜1970年代）

- **1960年代**: プログラミング言語の発展と共に、プログラムの正当性検証への関心が高まる
- **1969年**: Tony HoareがHoare論理を提案。プログラムの事前条件・事後条件による正当性証明の基礎を築く
- **1977年**: Amir Pnueliが線形時相論理（LTL）をコンピュータプログラムの形式検証のために提案
- **1978年**: Tony HoareがCSP（Communicating Sequential Processes）を発表

### 3.2 形式手法の確立（1980年代）

- **1980年代初頭**: VDMやZ言語などのモデルベース仕様記述言語が確立
- **1980年代中盤**: Clarke and EmersonがCTL（Computational Tree Logic）とCTLモデル検査を開発
- **1985年**: Lichtenstein and PnueliがLTLのモデル検査を定義
- **1986年**: Emerson and HalpernがCTL*（LTLとCTLの組み合わせ）を定義
- **1980年代後半**: LOTOSが通信プロトコルの仕様記述言語として発展

### 3.3 現代の発展（1990年代〜現在）

- **1990年代**: UMLの登場により半形式的仕様記述が普及
- **1995-1999年**: Intelがシンボリックモデル検査を使った検証努力を経て、形式仕様記述言語ForSpecを開発
- **1999年**: TLA+の仕様記述が「Specifying Concurrent Systems with TLA+」論文で紹介され、同年Yuan YuがTLA+仕様のためのTLCモデル検査器を開発
- **2000年代**: Alloyなどの軽量形式手法が登場
- **2010年代〜現在**: Event-B、モデル駆動開発（MDD）、形式手法の産業応用が拡大

## 4. アプローチによる分類

### 4.1 モデル指向（Model-oriented）仕様記述

システムの状態モデルとして仕様を表現。よく理解された数学的実体（集合や関数など）を使って構築し、システム操作がシステムの状態にどう影響するかを定義する。

- **代表言語**: VDM、Z
- **特徴**: ライフサイクルの後期フェーズでの使用に適している
- **欠点**: 小さな変更が仕様全体に大きな変更をもたらす可能性がある

### 4.2 性質指向（Property-oriented）仕様記述

システムの振る舞いを性質の集合として定義。公理によって関数とソート間の関係を記述する抽象的スタイル。

- **代表例**: 代数的仕様記述
- **特徴**: 容易に変更可能なため、要求仕様記述に適している
- **利点**: 公理を別の公理に簡単に置き換えられる

### 4.3 振る舞い指向（Behavior-oriented）仕様記述

システムの振る舞いに焦点を当てた仕様記述。一貫性、安全性、信頼性、非終了性などの性質を含む。

- **応用**: マルチモーダルアプリケーションの仕様記述とテスト

### 4.4 操作的（Operational）仕様記述

実行モデルとプロセスの振る舞いに焦点を当てる。

- **代表例**: Paisley、GIST、Petriネット、プロセス代数

## 5. 保証の有無による分類

### 5.1 検証可能な形式手法

形式的仕様記述言語を使用することで、実装が仕様を満たすことの証明や検証が可能となる。

#### モデル検査（Model Checking）
- 「実行・観測」に基づいた検証
- ツールが可能な状態遷移を網羅的に調べ、性質が成り立つかどうかを検証
- 全探索によって制約が満たされることを確認
- **代表ツール**: TLA+ (TLCモデル検査器)、Alloy、SPIN、NuSMV

#### 定理証明（Theorem Proving）
- システム設計の階層化による検証
- 詳細化に矛盾がないかを（自動）定理証明で示す
- 論理学や代数学に基づく厳密な証明
- **代表手法**: Coq、Isabelle/HOL、HOL

#### 型システム（Type Systems）
- ライトウェイト形式手法の一例
- コンパイル時に特定のクラスのエラーを防ぐ
- プログラミング言語に組み込まれた形式的保証

### 5.2 保証のレベル

形式手法を使用することで、以下の保証が得られる：

- **正当性の保証**: ソフトウェアがある性質を満たしていることを論理的に検証
- **不具合の不在保証**: 一定の不具合が存在しないことを保証
- **検証による設計の妥当性確認**: 仕様が設計の正当性を検証
- **実装の検証**: プログラムが仕様を満たすことを証明

### 5.3 半形式的・非形式的手法の制約

半形式的および非形式的仕様記述では、形式的な保証は得られない。しかし以下の利点がある：

- コミュニケーションの容易さ
- 理解のしやすさ
- 開発の初期段階での柔軟性

## 6. 応用分野

### 6.1 ハードウェア設計

- **ハードウェア記述言語（HDL）**: デジタル回路を設計するための言語。回路の設計と構成を記述
- **ハードウェア・ソフトウェア協調設計（コデザイン）**: ハードウェアとソフトウェアを同時に、区別なく設計・合成

### 6.2 通信プロトコル

- **SDL**: 元々通信システムのプロトコル仕様の記述法として開発。電話業界での標準
- **LOTOS**: 並行システムや通信プロトコルの仕様記述に特化

### 6.3 安全性重視システム

- **航空・鉄道システム**: VDM-SLなどが使用される
- **金融システム**: 形式的検証により信頼性を担保

### 6.4 リアルタイムシステム

- **プロセス制御**: SDL、LOTOSなどが利用される
- **リアルタイムアプリケーション**: 時相論理ベースの仕様記述

### 6.5 産業での実績

- **NASA**: 形式手法の専門部署を持ち、宇宙機器の信頼性確保に活用
- **Intel**: 形式手法専門部署を持ち、ハードウェア設計の検証に使用
- **鉄道・航空関係**: 大規模システムの開発で大きな成果

## 7. 仕様記述言語の利点と課題

### 7.1 利点

- **曖昧さの排除**: 形式的仕様は数学的に厳密で曖昧さがない
- **自動検証**: ツールによる自動的な性質の検証が可能
- **設計の早期検証**: 実装前に設計の問題を発見できる
- **ドキュメント化**: 厳密な仕様書として機能
- **保守性の向上**: 仕様の変更影響を厳密に追跡可能
- **要求の明確化**: 曖昧さを排除することで要求の精度が向上

### 7.2 課題

- **学習コスト**: 形式手法の習得には高度なスキルが必要
- **記述の複雑さ**: システム全体の仕様を表現するには膨大な量の記述が必要
- **ツールの成熟度**: すべての形式手法が成熟したツールサポートを持つわけではない
- **普及の遅れ**: 長い研究段階の歴史があるが、産業での普及は限定的
- **コストと時間**: 形式的検証には時間とコストがかかる

## 8. まとめ

仕様記述言語は、非形式的な自然言語から高度に形式的な数学的記法まで幅広いスペクトラムを持つ。形式性が高いほど厳密な検証が可能になる一方、学習コストや記述の複雑さも増大する。

プロジェクトの性質、安全性要求、チームのスキル、開発コストなどを考慮して、適切なレベルの形式性を持つ仕様記述言語を選択することが重要である。

現代では、形式手法は研究段階を超えて、航空宇宙、鉄道、金融、ハードウェア設計など、信頼性が極めて重要な分野で実用化されている。今後、ツールの改善と教育の普及により、より広範な分野での活用が期待される。

## 参考文献・出典

### 日本語Wikipedia
- [仕様記述言語 - Wikipedia](https://ja.wikipedia.org/wiki/%E4%BB%95%E6%A7%98%E8%A8%98%E8%BF%B0%E8%A8%80%E8%AA%9E)
- [仕様及び記述言語 - Wikipedia](https://ja.wikipedia.org/wiki/%E4%BB%95%E6%A7%98%E5%8F%8A%E3%81%B3%E8%A8%98%E8%BF%B0%E8%A8%80%E8%AA%9E)
- [形式仕様記述 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E4%BB%95%E6%A7%98%E8%A8%98%E8%BF%B0)
- [形式手法 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E6%89%8B%E6%B3%95)
- [形式的検証 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E7%9A%84%E6%A4%9C%E8%A8%BC)
- [ハードウェア記述言語 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%8F%E3%83%BC%E3%83%89%E3%82%A6%E3%82%A7%E3%82%A2%E8%A8%98%E8%BF%B0%E8%A8%80%E8%AA%9E)

### 英語Wikipedia
- [Specification language - Wikipedia](https://en.wikipedia.org/wiki/Specification_language)
- [Formal specification - Wikipedia](https://en.wikipedia.org/wiki/Formal_specification)
- [Category:Formal specification languages - Wikipedia](https://en.wikipedia.org/wiki/Category:Formal_specification_languages)
- [Z notation - Wikipedia](https://en.wikipedia.org/wiki/Z_notation)
- [Formal methods - Wikipedia](https://en.wikipedia.org/wiki/Formal_methods)
- [Model-based specification - Wikipedia](https://en.wikipedia.org/wiki/Model-based_specification)
- [Object Constraint Language - Wikipedia](https://en.wikipedia.org/wiki/Object_Constraint_Language)
- [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)
- [Linear temporal logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_temporal_logic)
- [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)

### 学術・技術資料
- [Z Formal Specification Language – An Overview – IJERT](https://www.ijert.org/z-formal-specification-language-an-overview)
- [Informal, semi-formal, and formal approaches to the specification of software requirements - UBC Library](https://circle.ubc.ca/handle/2429/5607)
- [What is Property-Oriented Specification | IGI Global](https://www.igi-global.com/dictionary/property-oriented-specification/60951)
- [形式手法とは？｜ディペンダブル・システムのための形式手法の実践ポータル](https://formal.mri.co.jp/outline/)
- [形式手法のポイント（２）： 検証 ｜ディペンダブル・システムのための形式手法の実践ポータル](https://formal.mri.co.jp/outline/point-2.html)
- [形式仕様記述言語の概要と代表的な言語解説 - なんちゃってプログラマーの日記](https://nakaterux.hatenablog.com/entry/2024/08/29/221700)

### その他のリソース
- [Formal Specification Languages](https://www.rbjones.com/rbjpub/cs/csfm02.htm)
- [ScienceDirect - Formal Specification](https://www.sciencedirect.com/topics/computer-science/formal-specification)
- [ScienceDirect - Specification Language](https://www.sciencedirect.com/topics/computer-science/specification-language)
- [ScienceDirect - Algebraic Specifications](https://www.sciencedirect.com/topics/computer-science/algebraic-specifications)
