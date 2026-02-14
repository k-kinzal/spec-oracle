# 仕様の階層性と「1つの仕様」概念

## 概要

本調査では、「全体として1つの仕様がある」という感覚と、その仕様が階層的に構成される概念について学術的背景を探る。基底宇宙の概念、多層的な宇宙の合成、荒めで包括的な仕様から詳細な仕様への段階的精密化（stepwise refinement）、および体験やゴールといった最も抽象的なレベルからの仕様記述の理論的基盤を調査する。

## 1. 段階的詳細化（Stepwise Refinement）の理論

### 1.1 Wirthによる段階的詳細化法の提唱

段階的詳細化法は、1971年にNiklaus Wirthが論文"Program Development by Stepwise Refinement"で体系化した概念である。Wirthは、プログラミングを「タスクをサブタスクに、データをデータ構造に分解する一連の設計決定」として捉え、段階的な精密化のプロセスとして定式化した。

段階的詳細化法の基本原理は以下の通りである：

1. **最も抽象的な手続きから開始**: 単一の入力と出力を持つ最も抽象的な手続きから始める
2. **段階的な詳細化**: 抽象的な手続きの内部処理を追加の手続きで置き換えることで、より詳細なバージョンを段階的に構築する
3. **複雑性の管理**: このプロセスを繰り返すことで、複雑なプログラムを体系的に記述できる

Wirthが提唱する段階的詳細化は、トップダウン設計の基盤となり、構造化プログラミングの中核的な技法として確立された。

参考：
- [Program Development by Stepwise Refinement](http://sunnyday.mit.edu/16.355/wirth-refinement.html)
- [段階的詳細化法 - Wikipedia](https://ja.wikipedia.org/wiki/%E6%AE%B5%E9%9A%8E%E7%9A%84%E8%A9%B3%E7%B4%B0%E5%8C%96%E6%B3%95)

### 1.2 Dijkstraとの関係

Edsger W. Dijkstraは、Wirthの仕事に先立つ1969年に"Notes on Structured Programming"（EWD 249）を発表し、段階的詳細化の理論的基盤を築いた。Dijkstraは、問題をヌル状態から開始し、一度に1要素ずつ拡張して最終的な解決策に到達するという視点を提示した。

DijkstraとWirthの貢献により、段階的詳細化は以下のように理解されるようになった：

- **問題の段階的拡張**: 問題を段階的に拡張していくプロセス
- **正しさの保証**: 各精密化ステップで正しさを維持する
- **モジュール性の獲得**: 精密化プロセス中に得られるモジュール性が、プログラムの変更や拡張の容易さを決定する

参考：
- [Program development by stepwise refinement – the morning paper](https://blog.acolyer.org/2016/10/14/program-development-by-stepwise-refinement/)
- [Stepwise refinement | Cornell CS](https://www.cs.cornell.edu/courses/JavaAndDS/stepwise/stepwise.html)

### 1.3 現代的な応用：MBSEとモデルベース開発

段階的詳細化の概念は、現代のモデルベースシステムズエンジニアリング（MBSE）やモデルベース開発（MBD）にも引き継がれている：

**MBSE における段階的詳細化レイヤリングアプローチ**:
- 各ドメイン間を移動しながら粗く詳細化した段階で要求充足を確認
- レイヤーの粒度を決定した後、有機的かつ段階的に詳細化
- 従来のドメイン別（構造、振る舞い、要求、検証）の詳細化とは異なるアプローチ

**MBD における段階的詳細化**:
- システム要求、動作、アーキテクチャを粗から細の抽象度で反復的に設計
- 設計フェーズに応じた同一抽象度での要求・動作・アーキテクチャの分析

参考：
- [MBSE 用語集 Stepwise Refinement Layering Approach](https://www.zuken.co.jp/solution/mbse/glossary-stepwise_refinement_layering_approach/)
- [MBDとは？ | IDAJ](https://www.idaj.co.jp/about-mbd/)

## 2. 形式手法における精密化理論

### 2.1 抽象化と精密化の関係

形式手法では、抽象化と精密化は相補的な概念として理解される：

**抽象化（Abstraction）**:
- 設計者が手続きとデータを指定しつつ、低レベルの詳細を抑制することを可能にする
- 注目する側面に特化し、不要な実現詳細を捨象する
- ツールが効率的かつ体系的に検査を実行できるようにする
- 人間が重要な本質に集中して問題を分析できるようにする

**精密化（Refinement）**:
- 設計が進むにつれて低レベルの詳細を明らかにする
- 抽象的な仕様から具体的な実装へと段階的に変換する
- 各段階で正しさの保証を維持する

両概念は、設計が進化するにつれて完全な設計モデルを作成するのに役立つ。

参考：
- [国立情報学研究所 石川冬樹「形式手法と仕様記述」の探求に向けて](https://research.nii.ac.jp/~f-ishikawa/work/files/2012-05-11-SQiP-intro.pdf)
- [Software Engineering Chapter 9 Design](https://uomustansiriyah.edu.iq/media/lectures/5/5_2019_05_16!05_23_44_AM.pdf)

### 2.2 Refinement Calculus

Ralph-Johan BackとJoakim Wrightによる精密化計算（Refinement Calculus）は、段階的精密化の数学的基盤を提供する形式手法である。

**主要な特徴**:
- プログラム構築のための段階的精密化の形式的アプローチ
- 最終的な実行可能プログラムの要求動作を抽象的で実行不可能な「プログラム」として指定
- 正しさを保証する一連の変換を通じて精密化
- 高階論理（higher-order logic）内で形式化
- 格子理論（lattice theory）を数学的基盤として使用

Carroll Morganも精密化計算の分野で重要な貢献をしており、精密化に関する多くのアイデアと競争的な環境を提供した。

精密化計算は、プログラムの正しさを証明し、数学的に厳密な方法でプログラム精密化を計算することを可能にする。

参考：
- [Refinement Calculus: A Systematic Introduction | Springer](https://www.springer.com/gp/book/9780387984179)
- [Refinement calculus - Wikipedia](https://en.wikipedia.org/wiki/Refinement_calculus)
- [On the Refinement Calculus (PDF)](https://www.cs.ox.ac.uk/files/3391/PRG70.pdf)

### 2.3 B Method と Event-B における抽象機械と精密化

B Methodとその後継であるEvent-Bは、抽象機械の概念を中心とした段階的精密化の体系的なアプローチを提供する。

**抽象機械（Abstract Machine）**:
- 最初の最も抽象的なバージョンで、設計者は設計の目標を指定
- 精密化ステップ中に、目標を明確化したり、データ構造やアルゴリズムの詳細を追加して抽象機械をより具体的にする

**精密化プロセス**:
- 精密化中に作成された新しいバージョンは、一貫性があり、抽象機械のすべての特性を含むことを証明する必要がある
- 決定論的バージョン（Implementation）が達成されるまで精密化を継続

**Event-Bの特徴**:
- 集合論を使用したモデリング
- 精密化を使用してシステムを異なる抽象レベルで表現
- これらの精密化レベル間の一貫性を検証するための数学的証明の使用
- Rodin Platformによるツールサポート

**イベント精密化**:
- 機械が別の機械を精密化する場合、各抽象イベントの精密化を提供する必要がある
- 1つのイベントが1つの抽象イベントを精密化する、または多数のイベントが1つの抽象イベントを精密化する
- 精密化で新しいイベントを導入可能

参考：
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [Using The Event-B Method For Critical Systems | Medium](https://medium.com/axons/using-the-event-b-method-for-critical-systems-c8a7beb38214)
- [An Introduction to the Event-B Modelling Method](https://www.southampton.ac.uk/~tsh2n14/publications/chapters/eventb-dbook13.pdf)

## 3. 仕様記述言語における階層と合成

### 3.1 ZとVDMにおける仕様の構造化

ZとVDM（Vienna Development Method）は、仕様の階層化と合成に異なるアプローチを取る形式仕様言語である。

**Z Notation のアプローチ**:
- より単純なコンポーネントから仕様を構築する利点
- これらのコンポーネントの仕様は、完全な状態の事前開発を必要としない
- 状態を分割し、操作が必要とする状態の部分のみで操作を指定しようとする
- 部分的な仕様からの構築が可能

**VDM のアプローチ**:
- 操作を指定する前に完全な状態のモノリシックな記述を提供
- 状態自体は構造化されている
- 状態の一部のみにアクセス・更新する操作に対処するため、各操作への状態コンポーネントの読み取りおよび書き込みインポートを使用
- どのコンポーネントが読み取られ、書き込まれるかを明示的に記述

**共通点**:
- Z、B、VDMは根本的に大きく異なるわけではない
- 基盤と目標において類似している
- 両方とも、指定者が要求を正確に記述し、これらの仕様を正しく設計に精密化することを可能にする

参考：
- [Comparative Analysis of Formal Specification Languages Z ... (PDF)](https://inpressco.com/wp-content/uploads/2015/06/Paper1082086-2091.pdf)
- [VDM and Z: A Comparative Case Study (PDF)](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)

### 3.2 合成的仕様（Compositional Specification）

合成的仕様は、複雑なシステムを機能的コンポーネントに分解し、それぞれを独立してカプセル化されたシステムとしてコーディングできることを意味する。

**基本原理**:
- 複合システムの仕様は、そのコンポーネントの仕様から得ることができる
- 厳密なモジュラー仕様手法には、各コンポーネントが単独で正しく動作すれば、他のコンポーネントと協調して正しく動作することを主張する証明規則が必要

**応用と利点**:
- コンポーネントベースシステムでは、仕様は入出力アクションの同期を通じて環境との相互作用の時間的順序を制約できる
- 製造システムでは、形式的アプローチにより、機能的側面をタイミング側面と直交して考慮できる
- 合成的証明は、複雑なシステムの異なる部分の動作の合成が、全体システムの望ましいグローバル仕様を保証することを形式的に証明できる

**全体としての1つの仕様**:
合成的仕様のアプローチにおいて重要なのは、個々のコンポーネントの仕様が存在しつつ、それらを合成することで「全体として1つの仕様」が形成されるという考え方である。各部分の仕様は独立して記述・検証できるが、同時にそれらは全体システムの一部として意味を持つ。

参考：
- [Compositional specification in rewriting logic | arXiv](https://arxiv.org/abs/1908.11769)
- [Compositional specification and verification of distributed systems | ACM](https://dl.acm.org/doi/10.1145/174662.174665)
- [Composing specifications | ACM](https://dl.acm.org/doi/10.1145/151646.151649)

## 4. 抽象化の階層性

### 4.1 抽象化レベルの理論

ソフトウェア開発とシステム工学における抽象化レベルは、複雑性を管理するための階層的フレームワークを提供する。

**抽象化レベルの3層構造**（ソフトウェア保守の文脈）:
1. **実装抽象（Implementation Abstraction）**: 最も詳細な情報を提供する低レベル抽象
2. **設計抽象（Design Abstraction）**: 異なるコンポーネントについてのより詳細な中間レベル抽象
3. **仕様抽象（Specification Abstraction）**: システムの概要を提供する高レベル抽象

**システムアーキテクチャにおける多層階層**:
- システムレベル、サブシステムレベル、コンポーネントレベル、オブジェクトレベル
- 各レベルは責任と機能の境界を表す
- 特定レベルでの具体的アーキテクチャは、次の低レベルでの対応する抽象アーキテクチャよりも高い抽象レベルでの記述である

**階層的精密化**:
- プログラムは、手続き的詳細のレベルを連続的に精密化することによって開発される
- 巨視的な機能記述（手続き的抽象）を段階的に分解することによって階層が開発される
- プログラミング言語ステートメントに到達するまで継続

参考：
- [Abstraction Levels in Reverse Engineering - GeeksforGeeks](https://www.geeksforgeeks.org/abstraction-levels-in-reverse-engineering/)
- [A hierarchical abstraction model for software engineering (PDF)](https://www.researchgate.net/publication/234818080_A_hierarchical_abstraction_model_for_software_engineering)
- [Abstraction Level - an overview | ScienceDirect](https://www.sciencedirect.com/topics/engineering/abstraction-level)

### 4.2 トップダウン設計における階層性

トップダウン設計は、仕様の階層性を実践するための体系的なアプローチである。

**トップダウン設計の原理**:
- 最初にシステム全体を定式化
- その後、システムの個々の部分の設計を段階的に詳細化
- 上位レベルの設計から下位レベルの設計へ順に進める
- 上位レベルの設計変更を自動的に下位の設計に反映可能

**段階的詳細化プロセス**:
1. システム全体の把握
2. システムを構成するサブシステムの設計
3. サブシステムを構成する機能の設計
4. 機能を構成するモジュールの設計

**利点**:
- 設計における無駄な作業を削減
- 大幅な設計工数の低減
- システム全体の見通しの良さ

参考：
- [トップダウン設計手法の概念 | 安田電子設計事務所](https://www.yasuda-elec.com/tec-topdown.php)
- [トップダウン設計とボトムアップ設計 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%88%E3%83%83%E3%83%97%E3%83%80%E3%82%A6%E3%83%B3%E8%A8%AD%E8%A8%88%E3%81%A8%E3%83%9C%E3%83%88%E3%83%A0%E3%82%A2%E3%83%83%E3%83%97%E8%A8%AD%E8%A8%88)

### 4.3 日本の組込みソフトウェア開発における階層化

日本の組込みソフトウェア開発では、仕様定義を以下の3段階に細分化することが一般的である：

1. **ソフトウェア要求定義（SWP1）**: 最も抽象的な要求レベル
2. **ソフトウェア・アーキテクチャ設計（SWP2）**: 中間的な構造設計レベル
3. **ソフトウェア詳細設計（SWP3）**: 最も具体的な詳細設計レベル

この階層化により、各段階で適切な抽象度を維持しながら、段階的に詳細化を進めることができる。

参考：
- [技術レポート「内部設計書に書くべきこと〜組込みソフト開発の場合〜」| ソフテック](https://www.softech.co.jp/mm_191106_tr.htm)

## 5. ゴール指向要求工学における階層性

### 5.1 KAOS方法論

KAOS（Knowledge Acquisition in automated specification / Keep All Objectives Satisfied）は、ゴールを階層的に構造化する要求工学手法である。

**KAOSの基本構造**:
- 1990年にオレゴン大学とルーヴァン大学でAxel van Lamsweeerdeらによって設計
- 要求をゴールダイアグラムから計算できる
- 各構文要素は2層構造を持つ：
  - 外側のグラフィカルな意味層：概念がその属性と関係で宣言される
  - 内側の形式的な層：概念を形式的に定義する

**ゴール階層の重要性**:
- ゴールの識別は、自然に「なぜ（why）」「どのように（how）」「他にどのような方法で（how else）」という質問を繰り返すことにつながる
- ステークホルダーの要求は、しばしばゴール（または手段-目的）階層の詳細化を通じて明らかになる
- より高いレベルのゴールは、より低いレベルのゴールが最初に達成されることを要求する

**KAOSの特徴**:
- 障害（obstacles）を明示的に表現する
- ゴールと要求の間の表記上の違いは、タスクとゴールの違いよりも明確

参考：
- [Goal-Oriented Requirements Engineering | van Lamsweerde (PDF)](https://objectiver.com/fileadmin/download/documents/presentations/KaosCEE-AvL.pdf)
- [KAOS (software development) - Wikipedia](https://en.wikipedia.org/wiki/KAOS_(software_development))
- [Goal-Oriented Requirements Engineering: An Overview (PDF)](https://www.cs.utoronto.ca/~alexei/pub/Lapouchnian-Depth.pdf)

### 5.2 i* フレームワーク

i*（i-star）は、KAOSと並ぶもう一つの主要なゴールモデリング手法である。

**i*の特徴**:
- エージェント間の依存関係をゴールやタスクと共に表現
- KAOSよりもタスクとゴールの間の表記上の違いが明確
- KAOSと比較して、特定のシステムをモデリングする際の理解しやすさが高いという研究結果もある

**KAOSとi*の違い**:
- KAOSは障害を明示的に表現するが、i*は表現しない
- ゴール指向の仕様記述で利用可能なアプローチにおける重要な違い

参考：
- [A controlled experiment to evaluate the understandability of KAOS and i* | ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0164121214002143)

### 5.3 要求の粒度レベル

ゴール指向要求工学では、要求の粒度（granularity）が階層性を理解する上で重要な概念となる。

**粗粒度（Coarse-grained）要求**:
- より一般的なゴールに関連
- 協調的なゴールや高レベルのビジネスプロセスに関連
- 単一のタスクではなく、1人以上のユーザーのタスクのセットを集約
- 単一の高レベル仕様内で様々なユーザーゴール要求をグループ化

**細粒度（Fine-grained）要求**:
- より具体的で詳細なタスクレベルの要求
- 粗粒度要求を実現するために必要な下位レベルのゴール

**階層的関係**:
- レベルが高いほど、ゴールはより一般的
- より高レベルのゴールを達成するには、他の低レベルのゴールが最初に達成される必要がある

参考：
- [Functional Requirements and their levels of granularity | Requirements Engineering Magazine](https://re-magazine.ireb.org/articles/functional-requirements-and-their-levels-of-granularity)

## 6. ユーザー体験とゴールから見た最も荒い仕様

### 6.1 ユーザー体験ゴールと仕様

ユーザー体験（UX）ゴールは、仕様の階層において最も抽象的で「荒い」レベルを表す。

**UXゴールの役割**:
- 体験駆動設計の前提条件は、どのような体験を設計するかを定義すること
- ユーザー体験ゴールは、意図された体験を具体化する
- すべての他の要求に影響を与える

**UXゴール設定へのアプローチ**:
UXゴール設定のための洞察とインスピレーションを得るための5つのアプローチ：
1. ブランド（Brand）
2. 理論（Theory）
3. 共感（Empathy）
4. 技術（Technology）
5. ビジョン（Vision）

各アプローチは異なる視点をもたらし、UXの学際的な性格をサポートする。

**ユーザー中心設計における階層**:
- ユーザー中心設計（UCD）プロセスでは、ユーザーが最優先
- インターフェース設計のためのユーザーのニーズと好みがサポートされる
- ユーザーが楽しい体験を持ち、タスクゴールを容易に完了できる手段を保証

参考：
- [Defining user experience goals to guide the design of industrial systems (PDF)](https://www.academia.edu/12707759/Defining_user_experience_goals_to_guide_the_design_of_industrial_systems)
- [User-Centered Design: Specifying Requirements For a Project | AGENTE](https://agentestudio.com/blog/user-centered-design-specification)

### 6.2 抽象要求から具体要求への変換

最も荒い抽象要求から具体的な要求への階層的変換は、以下のように理解できる：

**最上位層：体験とゴール**
- ユーザー体験の質的側面
- ビジネスゴールと組織の目標
- ブランド価値とビジョン

**中間層：機能要求とユーザビリティ要求**
- 粗粒度の機能要求
- ユーザビリティゴール
- システムレベルの制約

**下位層：詳細仕様**
- 細粒度の機能要求
- 具体的なインターフェース仕様
- 実装レベルの詳細

この階層構造により、「全体として1つの仕様」でありながら、異なる抽象度で異なる側面を記述することが可能になる。

参考：
- [Usability Requirement - an overview | ScienceDirect](https://www.sciencedirect.com/topics/computer-science/usability-requirement)

## 7. システム思考と全体仕様の概念

### 7.1 システム思考の原理

システム思考は、「全体として1つの仕様がある」という感覚を理論的に支える思考法である。

**システム思考の定義**:
- 解決すべき問題を「システム」として捉え、包括的かつ体系的に考える問題解決手法
- 複数の要素間のつながりや全体最適化に焦点を当てる
- 点と線を単一の「面」として扱い、1つの統合された図に描き出す

**氷山モデル（Iceberg Model）の4層構造**:
1. **出来事（Events）**: 海面上の見える部分
2. **パターン（Patterns）**: 出来事の中期的傾向
3. **構造（Structures）**: パターンを生成するもの
4. **メンタルモデル（Mental Models）**: 基盤となる思考の枠組み

この4層構造は、仕様の階層性と対応しており、表面的な要求から深層の原理まで、一貫した全体像を提供する。

**論理思考との違い**:
- 論理思考：物事を分解して個々の要素を理解
- システム思考：論理思考が困難とする複雑な問題に対処、点と線を「面」として統合

参考：
- [システム思考とは？ | GLOBIS](https://globis.jp/article/dic_ygomfocq-7/)
- [システム思考とは？氷山モデルを詳しく解説 - あそぶ社員研修](https://asobu-training.com/column/3245/)
- [エンジニアのためのシステム思考入門 | Qiita](https://qiita.com/hikarim/items/1b99a47137861c74a17e)

### 7.2 論理アーキテクチャと全体最適化

システム全体の最適化に繋がる論理アーキテクチャ定義の考え方も、「1つの仕様」概念を支える。

**論理要素の階層整理**:
- 論理要素の数が多い場合、各論理要素の責務の特徴から階層を整理
- 位置づけを明確にすることで全体の見通しを良くする
- 部分最適ではなく全体最適を目指す

**階層化アーキテクチャ**:
- 論理要素それぞれの責務の特徴から階層を整理
- 全体として矛盾なく、調和の取れた1つのシステムとして機能

参考：
- [システムの全体最適化に繋がる論理アーキテクチャ定義 | eureka-box](https://www.eureka-box.com/media/column/a48)
- [階層化アーキテクチャを知っていますか？ | Qiita](https://qiita.com/minibot/items/6deb8f34e31c6f3cd120)

### 7.3 抽象化能力と階層の統合

抽象化能力は、階層的な仕様を統合して「1つの全体仕様」として理解するための鍵となる。

**抽象化の本質**:
- 「強調したい一面を明確にする」ために行われる
- 対象としている領域に対して矛盾なく抽象化する必要がある
- 抽象度を変えることによって、物の見方と行動を変える

**抽象化と目的の関係**:
- 目的に応じて適切な抽象度を選択
- 異なる抽象度での記述を統合して全体像を把握
- システム設計の精度を高める考え方

抽象化能力により、詳細な仕様と高レベルのゴールを同時に保持し、それらが「1つの仕様」の異なる表現であることを理解できる。

参考：
- [抽象化能力の重要性 | note](https://note.com/tshunsk/n/n7c6c9c53edb8)
- [目的と抽象化の関係性から分かる、システムの設計精度を高める考え方 | Speaker Deck](https://speakerdeck.com/minodriven/purpose-abstraction-design)
- [チーム全員が知っててほしい抽象化のこと - LIVESENSE ENGINEER BLOG](https://made.livesense.co.jp/entry/2017/10/10/101000)

## 8. 基底宇宙と多層宇宙の概念

### 8.1 基底宇宙の概念的理解

「基底宇宙」という用語は、形式手法の文献では直接的には一般的ではないが、その背後にある概念は以下のように理解できる：

**基底宇宙としての最も抽象的な仕様**:
- システムの存在目的や価値を定義する最上位の抽象レベル
- ユーザー体験、ビジネスゴール、ビジョンといった「荒めで包括的」な記述
- すべての詳細な仕様がここから派生し、ここに回帰する基盤

**「近い別の宇宙」の解釈**:
- 基底宇宙に近い抽象レベルでの別の仕様記述
- 異なる視点やステークホルダーからの仕様表現
- 同じ抽象度で異なる側面を記述する並行的な仕様

### 8.2 多層宇宙の合成

「宇宙は多層でありそれらを合成することで1つの仕様ができる」という考え方は、以下の理論的基盤に支えられている：

**合成的仕様記述**:
- 異なるコンポーネントの仕様を合成して全体仕様を形成
- 各コンポーネントは独立した「宇宙」として記述
- 合成により全体として一貫した1つの仕様を構築

**階層的精密化**:
- 各抽象レベルが独自の「宇宙」を形成
- 段階的精密化により上位の宇宙から下位の宇宙へ変換
- すべての層を通じて一貫性と正しさを維持

**多視点アーキテクチャ**:
- 要求、構造、振る舞いといった異なる視点からの仕様
- 各視点が独自の「宇宙」を提供
- これらを統合して完全なシステム仕様を形成

参考：
- [From Viewpoints and Abstraction Levels in Software Engineering (PDF)](https://www.researchgate.net/publication/278798076_From_Viewpoints_and_Abstraction_Levels_in_Software_Engineering_Towards_Multi-ViewpointsMulti-Hierarchy_in_Software_Architecture)

### 8.3 「1つの仕様」としての統合

「全体として1つの仕様がある」という感覚は、以下のように理論的に支えられている：

**システム全体の一貫性**:
- すべての階層、すべての視点が、単一のシステムの異なる表現
- 精密化関係により、抽象と具象が論理的に結びつく
- 合成により、部分仕様が全体仕様に統合される

**トレーサビリティ**:
- 最も抽象的なゴールから最も具体的な実装まで追跡可能
- 各要素が全体の中での位置と役割を持つ
- 変更の影響が階層を通じて伝播

**意味論的一貫性**:
- 形式手法における精密化の正しさ保証
- 各レベルでの仕様が同じシステムを記述
- 数学的証明により一貫性を保証

この統合された視点により、詳細な技術仕様と高レベルのビジネスゴールが、実際には「1つの仕様」の異なる表現であることが理解できる。

## 9. まとめ

仕様の階層性と「1つの仕様」概念は、以下の理論的基盤によって支えられている：

1. **段階的詳細化理論**: Wirth、Dijkstraによる段階的精密化の原理は、抽象から具象への体系的な変換を提供する

2. **形式的精密化**: Refinement Calculus、B Method、Event-Bは、精密化の数学的基盤と正しさの保証を提供する

3. **合成的仕様**: 部分仕様を合成して全体仕様を形成する理論は、「多層宇宙の合成」という概念を支える

4. **抽象化階層**: 実装、設計、仕様という多層的な抽象化は、階層的な理解を可能にする

5. **ゴール指向要求工学**: KAOS、i*などの手法は、最も荒いゴールから詳細な要求への階層的な分解を体系化する

6. **ユーザー体験とゴール**: UXゴールは、仕様階層の最上位、最も「荒めで包括的」なレベルを提供する

7. **システム思考**: 全体最適化と多層的理解の枠組みは、「1つの仕様」という統合的視点を支える

これらの理論と実践により、「全体として1つの仕様がある」という感覚は、単なる直感ではなく、確固たる学術的・工学的基盤を持つ概念として理解できる。基底宇宙としての最も抽象的なゴールから、多層的な詳細化を経て具体的な実装に至るまで、すべては一貫した「1つの仕様」の異なる表現なのである。
