# 形式仕様言語の詳細調査

本ドキュメントでは、保証のある形式仕様言語（Formal Specification Languages）について個別に詳細を調査する。各言語の理論的基盤、表現能力、保証の仕組み、実用事例、長所と短所を明らかにする。

## 目次

1. [モデル指向仕様言語](#1-モデル指向仕様言語)
   - Z記法
   - VDM
   - B-Method / Event-B
2. [時相論理ベース仕様言語](#2-時相論理ベース仕様言語)
   - TLA+
   - Alloy
3. [プロセス代数](#3-プロセス代数)
   - CSP
   - CCS
   - ペトリネット
4. [定理証明支援系](#4-定理証明支援系)
   - Coq / Rocq
   - Isabelle/HOL
   - Lean
   - Agda
5. [その他の重要な形式仕様言語](#5-その他の重要な形式仕様言語)
   - RAISE / RSL
   - Frama-C / ACSL
   - Dafny
   - SPIN / Promela
6. [形式手法の比較と選択基準](#6-形式手法の比較と選択基準)

---

## 1. モデル指向仕様言語

モデル指向仕様言語は、システムの状態と操作を数学的モデルとして記述する。これらは集合論や述語論理を基礎とし、抽象的なシステム記述に適している。

### 1.1 Z記法（Z Notation）

#### 理論的基盤
Z記法は公理的集合論、ラムダ計算、一階述語論理に基づく形式仕様言語である。すべてのZ記法の式は型付けされており、素朴集合論のパラドックスを回避している。

#### 表現能力
- **スキーマ記法**: Zの特徴的な要素であるスキーマボックスにより、大規模な仕様を階層的に構築できる
- **数学的ツールキット**: 標準化された数学関数と述語のカタログを含む
- **高レベル抽象化**: システム設計とテストの強固な基礎を提供

#### 保証の仕組み
- **型検査**: すべての式が型付けされることで、型エラーを防止
- **形式的証明**: 数学的記法により、プロパティの厳密な証明が可能
- **仕様の検証**: 設計フェーズでの欠陥の早期発見

#### 実用事例
- Altran UKがソフトウェアの高レベル仕様作成に使用
- データベースシステムの仕様記述
- 安全性が重要なシステムの仕様化

#### 長所
- **精密性と明確性**: 曖昧さがなく、数学的に厳密な記述が可能
- **階層的仕様**: 大規模な仕様を管理可能な形で構築できる
- **可読性**: スキーマボックスと記号により、構造が視覚的に把握しやすい
- **標準化**: ISO標準（2002年完成）により、仕様が確立されている

#### 短所
- **学習曲線**: 初心者には、ボックス、ギリシャ文字、記号の混在が威圧的
- **ツールサポート**: プログラミング言語ではないため、機械可読ではない
- **ASCII表現の困難**: 多くの非ASCII記号を使用するため、表現に工夫が必要
- **コード生成不可**: VDMやB-Methodと異なり、ソースコードの直接生成ができない

**参考文献**:
- [Z notation - Wikipedia](https://en.wikipedia.org/wiki/Z_notation)
- [Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)
- [The Z Notation: A Reference Manual](https://www.rose-hulman.edu/class/cs/cs415/zrm.pdf)

---

### 1.2 VDM（Vienna Development Method）

#### 理論的基盤
VDMは最も古くから確立されたモデル指向形式手法の一つで、データと機能の記述をサポートする仕様言語（VDM-SL）を中心とする。言語には形式的意味論があり、モデルのプロパティを高い保証レベルで証明できる。

#### 表現能力
- **モデル指向仕様**: データと操作を数学的モデルとして記述
- **抽象から具体へ**: 要求に近い抽象レベルから実装に近い具体レベルまで対応
- **モジュール化**: 大規模システムをサブシステムに分割して開発可能

#### 保証の仕組み
- **形式的意味論**: ISO標準（1996年）により定義された厳密な意味論
- **証明による検証**: モデルのプロパティを数学的に証明可能
- **コード生成**: 仕様からソースコードを直接生成可能

#### 実用事例
- IBMウィーン研究所で開発され、産業界で広く利用
- 通信プロトコルの形式化
- 分散システムの仕様記述

#### 長所
- **成熟したツール**: Overture Toolなど、充実したツールサポート
- **実装志向**: 仕様からコード生成が可能で、実装との距離が近い
- **標準化**: ISO標準により、産業界での採用が容易

#### 短所
- **学習コスト**: 形式手法の背景知識が必要
- **抽象化の限界**: モデルが問題領域を正しく抽象化しているかは別問題
- **ツール依存**: 効果的な使用にはツールチェーンの習得が必要

**参考文献**:
- [Vienna Development Method - Wikipedia](https://en.wikipedia.org/wiki/Vienna_Development_Method)
- [The Vienna Development Method](https://www.overturetool.org/method/)
- [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)

---

### 1.3 B-Method / Event-B

#### 理論的基盤
B-Methodは抽象機械記法（AMN）に基づく、ツールサポートされた形式手法である。1980年代にJean-Raymond Abrialによってフランスと英国で開発された。Event-BはB-Methodを基に発展し、システムレベルのモデリングと解析を目的とする。

#### 表現能力
- **抽象機械記法**: システムを抽象機械として記述
- **段階的詳細化（Refinement）**: 異なる抽象レベルでシステムを表現
- **イベント駆動**: Event-Bではイベントによるシステム動作の記述

#### 保証の仕組み
- **数学的証明**: 詳細化の各段階で一貫性を数学的に証明
- **Rodin Platform**: Eclipse ベースのオープンソースIDE、自動証明機能を提供
- **コード生成**: B仕様から実行可能コードを生成可能

#### 実用事例
- **パリ地下鉄**: 14号線と1号線の自動運転システム
- **Ariane 5ロケット**: 制御ソフトウェアの検証
- **鉄道セクター**: 安全性が重要なシステムで広く使用

#### 長所
- **産業実績**: 欧州の安全性が重要なシステムで多数の実績
- **強力なツール**: Rodinプラットフォームによる包括的サポート
- **証明の自動化**: 詳細化と証明の自動化により効率的な開発が可能

#### 短所
- **学習曲線**: 抽象機械記法の理解に時間がかかる
- **記法の複雑さ**: 初学者には記法が複雑に見える
- **適用範囲**: 主に安全性が重要な組み込みシステム向け

**参考文献**:
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [Event-B.org](https://www.event-b.org/)
- [An Introduction to the Event-B Modelling Method](https://www.southampton.ac.uk/~tsh2n14/publications/chapters/eventb-dbook13.pdf)

---

## 2. 時相論理ベース仕様言語

時相論理ベースの言語は、システムの時間的挙動を記述し、並行システムや分散システムの検証に適している。

### 2.1 TLA+（Temporal Logic of Actions）

#### 理論的基盤
TLA+はLeslie Lamportによって開発された形式仕様言語で、時相論理（Temporal Logic of Actions）に基づく。システムの動作を数学と論理の形式言語で記述し、特に並行システムと分散システムの設計に適している。

#### 表現能力
- **時相論理**: システムの時間的挙動を表現
- **状態遷移**: システムの可能な状態とその遷移を記述
- **並行性**: 並行システムと分散アルゴリズムの記述に優れる

#### 保証の仕組み
- **有限モデル検査**: TLCモデルチェッカーがすべての可能な実行パスを探索
- **安全性と活性**: 安全性プロパティ（悪いことが起きない）と活性プロパティ（良いことが起きる）の検証
- **反例生成**: プロパティ違反時に具体的な反例を提示

#### 実用事例
- **Amazon Web Services (AWS)**: DynamoDB、S3、EBS、分散ロックマネージャなどで使用
- **Microsoft**: Azure の一部システムで採用
- **重要な発見**: DynamoDBで35ステップのエラートレースを持つ微妙なバグを発見

#### 長所
- **産業実績**: AWSなど大手企業での実績が豊富
- **バグ発見能力**: 他の技術では発見できない微妙なバグを検出
- **学習可能性**: エンジニアが2-3週間で有用な結果を得られる
- **PlusCal**: プログラミング言語に似たPlusCalにより学習障壁を下げられる

#### 短所
- **抽象化レベル**: 細粒度のコードレベルの詳細を実用的にモデル化できない
- **状態空間爆発**: 実システムでは状態空間が非常に大きく、完全な探索が実用的でない場合がある
- **数学的思考**: 数学的に考える能力が前提条件
- **PlusCalの制限**: PlusCalはTLA+のすべての機能を持たず、複雑なモデルの構築に制限がある

**参考文献**:
- [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)
- [Use of Formal Methods at Amazon Web Services](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)
- [How Amazon Web Services Uses Formal Methods](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/)
- [TLA+ in Practice and Theory](https://pron.github.io/posts/tlaplus_part3)

---

### 2.2 Alloy

#### 理論的基盤
Alloyは一階述語論理と集合論に基づく宣言的仕様言語で、ソフトウェアシステムにおける複雑な構造的制約と振る舞いを表現する。軽量な形式手法として、マイクロモデルの作成と自動検証に焦点を当てる。

#### 表現能力
- **関係論理**: リレーショナルロジックに基づく構造のモデリング
- **宣言的記述**: システムの制約を宣言的に表現
- **時相拡張**: Alloy 6では可変状態、時相論理、改良されたビジュアライザを追加

#### 保証の仕組み
- **SATソルバベース**: Kodkodモデルファインダを使用し、ブール充足可能性問題に変換
- **充足可能性検査**: runコマンドで式の充足可能性を検査
- **反例検出**: checkコマンドで式の妥当性を検査し、反例を提示

#### 実用事例
- Miniscriptの形式仕様
- セキュリティプロトコルの検証
- ソフトウェア設計の早期検証

#### 長所
- **軽量**: 小規模なマイクロモデルに適しており、学習が比較的容易
- **高速フィードバック**: SATソルバによる自動検証で迅速なフィードバック
- **視覚化**: 改良されたビジュアライザによりモデルの理解が容易
- **最新版**: Alloy 6（2025年1月リリース）で大幅な機能向上

#### 短所
- **スケーラビリティ**: 大規模システムよりマイクロモデル向き
- **完全性の限界**: 有界モデル検査のため、すべての可能性を網羅できない
- **モデル検査の限界**: 典型的なAlloyモデルにはモデル検査が不向きなことがある

**参考文献**:
- [Alloy (specification language) - Wikipedia](https://en.wikipedia.org/wiki/Alloy_(specification_language))
- [Alloy Analyzer](https://alloytools.org/)
- [An overview of Alloy — Formal Software Design with Alloy 6](https://haslab.github.io/formal-software-design/overview/index.html)

---

## 3. プロセス代数

プロセス代数は並行システムの動作を代数的に記述する形式手法で、プロセス間の相互作用とメッセージパッシングを表現する。

### 3.1 CSP（Communicating Sequential Processes）

#### 理論的基盤
CSPはTony Hoareによって1978年に提唱されたプロセス代数で、メッセージパッシングによる並行システムの相互作用パターンを記述する形式言語である。観察可能な線形振る舞いの集合に基づく意味論を持つ。

#### 表現能力
- **プロセス間通信**: チャネルを介したメッセージパッシング
- **並行合成**: 並行に実行されるプロセスの合成
- **選択とガード**: プロセスの選択的実行

#### 保証の仕組み
- **詳細化検査**: FDR（Failures-Divergences Refinement）ツールによる自動検証
- **意味論モデル**: トレースモデル、安定失敗モデル、失敗・発散モデルの3つの主要モデル
- **デッドロック・ライブロック検出**: システムの行き詰まりを検出

#### 実用事例
- **国際宇宙ステーション**: 故障管理システムとアビオニクスインターフェース（約23,000行のコード）のモデル化
- **スマートカード認証局**: Praxis High Integrity Systemsが約100,000行のコードの検証に使用
- **Needham-Schroeder プロトコル**: Loweが未知の攻撃を発見し、修正プロトコルを開発

#### 長所
- **産業実績**: 安全性・信頼性が重要なシステムで多数の実績
- **強力なツール**: FDRによる並列詳細化検査、数十億状態の解析が可能
- **プロトコル検証**: 通信プロトコルとセキュリティプロトコルの検証に適している
- **欠陥率の低減**: テストだけでは発見困難なエラーの検出

#### 短所
- **学習曲線**: プロセス代数の概念理解が必要
- **抽象化**: 実装とモデルのギャップを埋める作業が必要
- **ツール習熟**: FDRなどのツールの効果的な使用には訓練が必要

**参考文献**:
- [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)
- [CSP: A Practical Process Algebra](https://www.cs.ox.ac.uk/files/12724/cspfdrstory.pdf)
- [Formalization and Verification of PaxosStore](https://www.mdpi.com/2079-9292/14/5/823)

---

### 3.2 CCS（Calculus of Communicating Systems）

#### 理論的基盤
CCSはRobin Milnerによって1980年頃に導入されたプロセス計算である。その動作は正確に2つの参加者間の不可分な通信をモデル化する。並行合成、動作間の選択、スコープ制限を記述する基本要素を含む。

#### 表現能力
- **プロセス計算**: 並行プロセスの代数的記述
- **通信**: 2者間の同期通信
- **並行合成と選択**: 並行実行と非決定的選択の記述

#### 保証の仕組み
- **ラベル付き遷移システム**: 操作的意味論として定義
- **双模倣（Bisimulation）**: プロセスの等価性の検証
- **質的正しさ**: デッドロックやライブロックなどのプロパティの評価

#### 実用事例
- 反応的システムの記述
- プロトコルの形式的検証
- 並行システムの理論的基礎研究

#### 長所
- **理論的基盤**: プロセス代数の基礎を築いた重要な研究
- **代数的推論**: プロセスを代数的に推論可能
- **等価性理論**: 双模倣による厳密な等価性の定義

#### 短所
- **産業採用**: CSPと比べて産業界での採用は限定的
- **ツールサポート**: ツールサポートがCSPほど成熟していない
- **実用性**: 理論研究に重点が置かれ、産業応用は少ない

**参考文献**:
- [Calculus of communicating systems - Wikipedia](https://en.wikipedia.org/wiki/Calculus_of_communicating_systems)
- [CCS, the Calculus of Communicating Systems](https://link.springer.com/chapter/10.1007/978-3-319-42900-7_11)
- [Process calculus - Wikipedia](https://en.wikipedia.org/wiki/Process_calculus)

---

### 3.3 ペトリネット（Petri Net）

#### 理論的基盤
ペトリネットはCarl Adam Petriによって開発された、分散システムの数学的モデリングのための形式手法である。グラフ理論的な表現により、並行性、同期、リソース共有を視覚的に記述できる。

#### 表現能力
- **場所とトランジション**: 場所（Place）がシステムの状態、トランジション（Transition）が状態遷移を表現
- **トークン**: 場所に配置されるトークンがシステムの動的状態を表す
- **時間拡張**: 時間ペトリネットにより実時間システムを記述可能

#### 保証の仕組み
- **不変式解析**: システムの不変性の検証
- **到達可能性解析**: 特定の状態への到達可能性の検証
- **デッドロック・活性解析**: デッドロックと活性プロパティの検証

#### 実用事例
- **ロボットシステム**: タスク記述言語の形式検証
- **サイバーフィジカルシステム**: FPGAへの実装を指向した設計と検証
- **プロトコル検証**: MACプロトコルなどの通信プロトコルの検証
- **マルチエージェントシステム**: 実時間マルチエージェントシステムの仕様と検証

#### 長所
- **直感的表現**: グラフ構造により視覚的に理解しやすい
- **解析力**: 不変式、到達可能性、デッドロック、活性の解析が可能
- **ツールサポート**: 多様な解析ツールとシミュレーションツール
- **幅広い応用**: 製造、プロトコル、組み込みシステムなど多様な分野で使用

#### 短所
- **状態空間爆発**: 複雑なシステムでは状態数が膨大になる
- **時間の扱い**: 基本的なペトリネットは時間を扱えず、拡張が必要
- **抽象化レベル**: 詳細な実装との距離がある

**参考文献**:
- [Formal Verification for Task Description Languages. A Petri Net Approach](https://www.mdpi.com/1424-8220/19/22/4965)
- [Design and Verification of Petri-Net-Based Cyber-Physical Systems](https://www.mdpi.com/1996-1073/16/1/67)
- [Petri Nets 2026](https://petrinets2026.informatik.uni-hamburg.de/)

---

## 4. 定理証明支援系

定理証明支援系は、数学的定理やプログラムの性質を対話的に証明するためのツールである。高い保証レベルを提供するが、専門的な知識と労力を要する。

### 4.1 Coq / Rocq

#### 理論的基盤
Rocq Prover（旧称Coq）は対話的定理証明支援系で、Calculus of Inductive Constructionsに基づく。プログラムと仕様を形式的に記述し、プログラムが仕様に適合することを証明できる。

#### 表現能力
- **依存型**: 非常に表現力の高い型システム
- **帰納的構造**: 帰納的データ型と帰納的証明
- **プログラム抽出**: 仕様から実行可能なプログラム（OCamlまたはHaskell）を自動抽出

#### 保証の仕組み
- **機械検証証明**: すべての証明ステップが機械的に検証される
- **関数的正しさ**: プログラムが仕様に厳密に従うことの数学的証明
- **バグの排除**: コンパイラに起因するバグの可能性を排除

#### 実用事例
- **CompCert**: 形式検証された最適化CコンパイラでACMソフトウェアシステム賞受賞（2021年）
- **Ethereum検証**: スマートコントラクトの信頼性とセキュリティの検証
- **四色定理とFeit-Thompson定理**: 大規模数学定理の機械検証
- **Verified Software Toolchain**: Cプログラムの検証フレームワーク

#### 長所
- **最高レベルの保証**: 機械検証により最高レベルの正しさ保証
- **CompCertの成功**: 産業レベルのコンパイラ検証の実績
- **豊富なライブラリ**: Mathematical Componentsなど充実したライブラリ
- **抽出機能**: 証明済みコードを実行可能プログラムに変換

#### 短所
- **急峻な学習曲線**: 依存型や証明戦術の習得に時間がかかる
- **専門知識の必要性**: プログラミング言語や形式手法の深い知識が必要
- **コミュニティの小ささ**: 小規模なコミュニティと高い学習曲線が参入障壁
- **労力**: 小さなコードの検証にも多大な労力が必要

#### 名称変更
2023年10月11日に開発チームがCoqをThe Rocq Proverに改名することを発表し、2025年3月にRocq 9.0のリリースで正式に改名された。

**参考文献**:
- [Rocq - Wikipedia](https://en.wikipedia.org/wiki/Rocq)
- [The Rocq Prover (formerly Coq)](https://rocq-prover.org/docs)
- [CompCert - Main page](https://compcert.org/)
- [Pinpointing the Learning Obstacles of an Interactive Theorem Prover](https://sarajuhosova.com/assets/files/2025-icpc.pdf)

---

### 4.2 Isabelle/HOL

#### 理論的基盤
Isabelleは汎用的な証明支援系で、数学的な式を形式言語で表現し、論理的計算でそれらの式を証明するツールを提供する。最も広く使われるオブジェクト論理はIsabelle/HOL（高階論理）である。

#### 表現能力
- **高階論理**: 強力な論理的表現力
- **汎用性**: 様々な論理体系（HOL、ZF集合論など）をサポート
- **自動証明**: Sledgehammerなどの強力な自動証明機能

#### 保証の仕組み
- **対話的証明**: ユーザーと対話しながら証明を構築
- **自動化**: 自動証明器との統合により効率的な証明開発
- **機械検証**: すべての証明ステップが機械的に検証される

#### 実用事例
- **seL4マイクロカーネル**: 汎用OSカーネルの世界初の完全な形式検証（2009年）
  - 8,700行のCコードと600行のアセンブラ
  - 抽象仕様からC実装までの完全な詳細化証明
- **Gödel の完全性定理**: 数学的定理の形式化
- **素数定理**: 重要な数学定理の機械検証
- **セキュリティプロトコル**: プロトコルの正しさの証明

#### 長所
- **使いやすさ**: Coqと比較して使いやすいとされる
- **強力な自動化**: Sledgehammerによる自動証明の支援
- **seL4の成功**: OSカーネルの完全検証という画期的な実績
- **豊富なライブラリ**: Archive of Formal Proofsに大量の形式化済み定理

#### 短所
- **学習曲線**: 定理証明の概念と高階論理の理解が必要
- **労力**: 大規模な証明には多大な労力が必要
- **専門性**: 効果的な使用には形式手法の専門知識が必要

**参考文献**:
- [Isabelle (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant))
- [Isabelle](https://isabelle.in.tum.de/)
- [seL4: Formal Verification of an OS Kernel](https://sel4.systems/Research/pdfs/comprehensive-formal-verification-os-microkernel.pdf)

---

### 4.3 Lean（特にLean 4）

#### 理論的基盤
Leanは依存型理論に基づく証明支援系兼プログラミング言語で、Leonardo de Mouraによって開発された。Lean 4は言語の大幅な改良版で、証明と実用的なプログラミングの両方をサポートする。

#### 表現能力
- **依存型**: 非常に表現力の高い型システム
- **メタプログラミング**: Leanで書かれたマクロとメタプログラム
- **型クラス**: 数学的構造の抽象化

#### 保証の仕組み
- **対話的証明**: ユーザーとの対話による証明構築
- **自動証明**: タクティクによる部分的自動化
- **型検査**: 厳密な型検査による正しさの保証

#### 実用事例
- **Cedar**: AWS Verified PermissionsとAWS Verified Accessで使用される認可言語の検証
- **暗号**: HaxツールチェーンによるRust暗号実装（SHA-3、ML-KEMなど）の検証
- **SampCert**: AWS Clean Rooms Differential Privacyサービスで使用される差分プライバシープリミティブ
- **AI定理証明**: DeepSeek-Prover-V2（2025年4月）などのAIモデルによる定理証明
- **LNSym**: Arm命令セマンティクスと暗号プロトコルのモデリング

#### 長所
- **産業採用**: AWSなど大手企業での実用事例が増加
- **モダンな言語**: Lean 4は実用的なプログラミング言語としても使用可能
- **AI統合**: AIによる定理証明の研究が活発（DeepSeek-Prover-V2、Aristotleなど）
- **活発なコミュニティ**: 数学とCS両方のコミュニティが活発
- **標準ライブラリ**: 2026年7月までにStd 1.0のリリース候補版を予定

#### 短所
- **新しい技術**: まだ発展途上の部分がある
- **学習曲線**: 依存型と証明の概念の習得が必要
- **ドキュメント**: 急速に進化しているため、ドキュメントが追いつかない場合がある

#### 受賞歴
2025年にACM SIGPLAN Programming Languages Software Awardを受賞。「数学、ハードウェア・ソフトウェア検証、AIへの重要な影響」が評価された。

**参考文献**:
- [Lean (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/Lean_(proof_assistant))
- [Lean Programming Language](https://lean-lang.org/)
- [How the Lean language brings math to coding](https://www.amazon.science/blog/how-the-lean-language-brings-math-to-coding-and-coding-to-math)
- [The Lean FRO Year 3 Roadmap](https://lean-lang.org/fro/roadmap/y3/)

---

### 4.4 Agda

#### 理論的基盤
Agdaは依存型関数型プログラミング言語および対話的定理証明支援系である。Martin-Löf型理論の変種、特に直観主義的型理論に基づく。

#### 表現能力
- **依存型**: ある型のオブジェクトで索引付けされた型の族
- **全域性**: プログラムは型Tの値で必ず終了する（ランタイムエラーが発生しない）
- **証明と計算**: 命題即型対応により、証明を計算として実行可能

#### 保証の仕組み
- **型による証明**: 命題即型対応（Curry-Howard対応）
- **全域性保証**: 非停止プログラムは明示的に要求しない限り書けない
- **メタ変数**: プログラム構築時にメタ変数を積極的に活用

#### 実用事例
- 数学的定理の構成的証明
- プログラムの形式検証
- 型理論の研究

#### 長所
- **関数型スタイル**: 証明が関数型プログラミングスタイルで記述される
- **全域性**: 実行時エラーのない保証
- **直感的型理論**: Martin-Löf型理論の直接的な実装

#### 短所
- **タクティクの欠如**: Coqのようなタクティク言語がない
- **学習曲線**: 依存型と型理論の理解が必要
- **産業採用**: 学術研究に重点があり、産業採用は限定的

**参考文献**:
- [Agda (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Agda_(programming_language))
- [What is Agda?](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html)
- [GitHub - agda/agda](https://github.com/agda/agda)

---

## 5. その他の重要な形式仕様言語

### 5.1 RAISE / RSL

#### 理論的基盤
RAISE（Rigorous Approach to Industrial Software Engineering）は形式仕様言語RSL（RAISE Specification Language）、関連する開発手法、サポートツールから構成される。VDMに触発され、モデル指向仕様、代数的仕様、CSPライクな並行性、モジュール概念を組み合わせている。

#### 表現能力
- **多様な仕様スタイル**: 公理的とモデルベース、適用的と命令的、逐次的と並行的
- **モジュラー開発**: 大規模システムをモジュール方式で開発
- **抽象から具体へ**: 要求に近い抽象から実装に近い具体まで

#### 保証の仕組み
- **形式的意味論**: 言語の厳密な意味論定義
- **証明による検証**: システムプロパティの数学的証明
- **ツールサポート**: RAISE ツールチェーンによるサポート

#### 実用事例
- ソフトウェアシステムの仕様記述
- プロトコルエンジニアリング
- マルチエージェントシステムの組織記述

#### 長所
- **包括性**: 様々な仕様スタイルをサポート
- **VDMの拡張**: VDMの強みを保ちつつ、代数的仕様とCSPを統合

#### 短所
- **採用の限定**: 他の形式手法と比べて採用が限定的
- **ツールの成熟度**: 他の主流形式手法と比べてツールサポートが限定的

**参考文献**:
- [RAISE | The RAISE specification language, method, and tools](https://raisetools.github.io/)
- [The RAISE Specification Language](https://raisetools.github.io/material/documentation/raise-language.pdf)
- [The Logic of the RAISE Specification Language](https://link.springer.com/chapter/10.1007/978-3-540-74107-7_7)

---

### 5.2 Frama-C / ACSL

#### 理論的基盤
Frama-CはCプログラムの相互運用可能なプログラム解析器のセットで、ACSL（ANSI/ISO C Specification Language）を用いて仕様を記述する。フランスのCEA-ListとInriaによって開発された。

#### 表現能力
- **関数契約**: 前提条件と事後条件の記述
- **ループ不変式**: ループの不変性の記述
- **アサーション**: プログラム中の任意の点でのプロパティ

#### 保証の仕組み
- **最弱事前条件（WP）**: Hoare論理に基づく演繹的検証
- **SMTソルバ**: Alt-Ergo、CVC5、Z3などにより自動証明（実世界のケーススタディで最大98%の検証条件を自動証明）
- **ランタイム検証（E-ACSL）**: 静的検証できないプロパティの実行時検証

#### 実用事例
- 安全性が重要な組み込みソフトウェアの検証
- Cコードの形式的検証
- 航空宇宙、原子力などの分野

#### 長所
- **実用性**: 既存のCコードに適用可能
- **自動化**: SMTソルバによる高度な自動証明
- **相互運用性**: 複数の解析プラグインの組み合わせ
- **実績**: 産業界での実用事例

#### 短所
- **C言語の制約**: C言語の複雑性とアンセーフな機能
- **アノテーションの負担**: 詳細なアノテーションの記述が必要
- **学習曲線**: ACSLとツールの習得に時間がかかる

**参考文献**:
- [Frama-C - Wikipedia](https://en.wikipedia.org/wiki/Frama-C)
- [Frama-C - Framework for Modular Analysis of C programs](https://www.frama-c.com/)
- [A gentle introduction to C code verification using the Frama-C platform](https://hal.science/hal-03625208v1/document)

---

### 5.3 Dafny

#### 理論的基盤
Dafnyは検証対応プログラミング言語で、仕様の記録をネイティブサポートし、静的プログラム検証器を備える。Microsoftの研究プロジェクトとして開発され、Boogieを中間言語、Z3を定理証明器として使用する。

#### 表現能力
- **仕様構文**: 事前条件、事後条件、フレーム仕様、停止性メトリック
- **ゴースト変数**: 検証専用の変数
- **集合と列**: 数学的データ型のサポート

#### 保証の仕組み
- **自動検証**: コーディング中にリアルタイムで検証
- **反例生成**: エラー時に反例を提示
- **Z3ソルバ**: 強力なSMTソルバによる自動証明

#### 実用事例
- 正しさが保証されたソフトウェアの開発
- アルゴリズムの正しさの検証
- 教育目的での形式検証の学習

#### 長所
- **統合された体験**: プログラミングと検証が統合されたワークフロー
- **自動化**: 高度な自動証明機能
- **多言語コンパイル**: C#、Java、JavaScript、Go、Pythonへのコンパイル
- **リアルタイムフィードバック**: エディタ統合による即座のフィードバック

#### 短所
- **学習曲線**: 仕様の記述方法の習得が必要
- **Z3依存**: 検証がZ3の能力に依存
- **産業採用**: まだ広く産業採用されていない

**参考文献**:
- [Dafny - Wikipedia](https://en.wikipedia.org/wiki/Dafny)
- [Dafny](https://dafny.org/)
- [GitHub - dafny-lang/dafny](https://github.com/dafny-lang/dafny)

---

### 5.4 SPIN / Promela

#### 理論的基盤
SPINはGerard J. HolzmannによってBell Labsで開発された、並行ソフトウェアモデルの正しさを厳密かつ自動的に検証する汎用ツールである。Promela（Process or Protocol Meta Language）は検証モデリング言語である。

#### 表現能力
- **プロセス**: 並行プロセスの動的生成
- **メッセージチャネル**: 同期（ランデブー）または非同期（バッファ付き）通信
- **非決定性**: システムの非決定的な振る舞いの記述

#### 保証の仕組み
- **網羅的検証**: すべての可能な実行パスの探索
- **LTL検証**: 線形時相論理で表現された正しさプロパティの検証
- **デッドロック検出**: デッドロック、非進行サイクルの検出
- **部分順序削減**: 効率的な検証のための最適化技術

#### 実用事例
- 通信プロトコルの検証
- 並行アルゴリズムの検証
- 分散システムの検証

#### 長所
- **実績**: 長い歴史と多数の実用実績（ACM System Software Award受賞）
- **網羅性**: 数学的確実性を持った検証
- **効率的探索**: 部分順序削減とBDD技術による最適化

#### 短所
- **状態空間爆発**: 複雑なシステムで状態数が膨大になる
- **抽象化**: 実装とモデルのギャップ
- **学習曲線**: Promelaとモデル検査の概念の理解が必要

**参考文献**:
- [SPIN model checker - Wikipedia](https://en.wikipedia.org/wiki/SPIN_model_checker)
- [Spin - Formal Verification](https://cse.msu.edu/~cse470/Public/Software/spin/whatispin.html)
- [GitHub - nimble-code/Spin](https://github.com/nimble-code/Spin)

---

## 6. 形式手法の比較と選択基準

### 6.1 形式手法のカテゴリ

形式手法は大きく以下のカテゴリに分類される:

1. **モデル検査（Model Checking）**
   - 代表例: TLA+、Alloy、SPIN
   - 特徴: 自動的、有限状態システム、網羅的探索
   - 適用: 並行システム、分散アルゴリズム、プロトコル

2. **定理証明（Theorem Proving）**
   - 代表例: Coq/Rocq、Isabelle/HOL、Lean、Agda
   - 特徴: 対話的、無限状態システム、高い保証レベル
   - 適用: コンパイラ、OSカーネル、暗号、数学

3. **演繹的検証（Deductive Verification）**
   - 代表例: Frama-C/ACSL、Dafny
   - 特徴: プログラム注釈、Hoare論理、SMTソルバ
   - 適用: 既存コードの検証、実用的ソフトウェア

### 6.2 選択基準

#### プロジェクトの特性による選択

**並行・分散システム**:
- TLA+: 産業実績が豊富、AWS、Microsoftでの採用
- CSP/FDR: プロトコル検証、セキュリティプロトコル
- SPIN/Promela: 通信プロトコル、組み込みシステム

**安全性が重要なシステム**:
- B-Method/Event-B: 鉄道、航空宇宙での実績
- Isabelle/HOL: seL4マイクロカーネルの完全検証
- Coq/Rocq: CompCertコンパイラの完全検証

**既存Cコードの検証**:
- Frama-C/ACSL: C言語特化、実用的なツールチェーン

**新規開発と検証の統合**:
- Dafny: 検証対応プログラミング、リアルタイムフィードバック
- Lean 4: 証明とプログラミングの統合、モダンな言語

#### 保証レベルと労力のトレードオフ

| 手法 | 保証レベル | 自動化 | 学習曲線 | 労力 |
|------|----------|--------|----------|------|
| モデル検査（TLA+、Alloy） | 中 | 高 | 中 | 中 |
| 演繹的検証（Frama-C、Dafny） | 中〜高 | 中〜高 | 中 | 中〜高 |
| 定理証明（Coq、Isabelle、Lean） | 最高 | 低〜中 | 高 | 高 |

### 6.3 形式手法の利点

1. **精密性と明確性**: 曖昧さのない厳密な仕様
2. **早期エラー検出**: 実装前の設計段階でのバグ発見
3. **品質向上**: 調査によると92%の品質改善と開発コスト・時間の削減
4. **高保証**: テストでは発見できない微妙なバグの検出

### 6.4 形式手法の課題

1. **学習曲線**: 数学的背景と専門知識の必要性
2. **労力**: 小規模なコードでも検証に多大な労力
3. **ツール習熟**: 効果的な使用にはツールの習得が必要
4. **抽象化の問題**: モデルが問題領域を正しく抽象化しているかは別問題
5. **コミュニティの小ささ**: 特に定理証明支援系では専門家コミュニティが小規模

### 6.5 ハイブリッドアプローチ

多くのプロジェクトがハイブリッドアプローチを採用:
- **モデル検査**: 迅速なイテレーションと設計の探索
- **定理証明**: 最重要コンポーネントの完全検証

例: Amazonは、オーロラデータベースのコミットプロトコルをPとTLA+の両方でモデル化し、検証と最適化を実現した。

### 6.6 産業界での採用傾向

- **TLA+**: Amazon AWS、Microsoft Azureでの積極的採用
- **Lean**: AWSのCedar認可言語、差分プライバシープリミティブの検証
- **B-Method**: 欧州の鉄道と航空宇宙産業
- **Frama-C**: 原子力、航空宇宙などの安全性が重要な分野
- **CompCert**: 安全性が重要な組み込みソフトウェア

---

## まとめ

形式仕様言語は、ソフトウェアシステムの正しさを数学的に保証するための強力なツールである。それぞれの言語は異なる理論的基盤、表現能力、保証の仕組みを持ち、特定の応用領域に適している。

**主要な知見**:

1. **多様性**: モデル指向、時相論理、プロセス代数、定理証明など、多様なアプローチが存在
2. **保証レベル**: モデル検査は自動的だが有界、定理証明は労力がかかるが最高レベルの保証
3. **産業採用**: TLA+（AWS）、B-Method（鉄道）、CompCert（組み込み）など実績が増加
4. **ツールの進化**: Alloy 6、Lean 4、Rocq 9.0など、ツールが継続的に進化
5. **AI統合**: Lean 4でのAI定理証明の研究が活発化

形式手法の選択は、プロジェクトの特性、要求される保証レベル、利用可能なリソース、チームの専門性に依存する。多くの場合、ハイブリッドアプローチ（モデル検査と定理証明の組み合わせ）が実用的な解決策となる。

---

## Sources

### Z Notation
- [Z notation - Wikipedia](https://en.wikipedia.org/wiki/Z_notation)
- [Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)
- [The Z Notation: A Reference Manual](https://www.rose-hulman.edu/class/cs/cs415/zrm.pdf)

### VDM
- [Vienna Development Method - Wikipedia](https://en.wikipedia.org/wiki/Vienna_Development_Method)
- [The Vienna Development Method](https://www.overturetool.org/method/)
- [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)

### B-Method / Event-B
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [Event-B.org](https://www.event-b.org/)
- [An Introduction to the Event-B Modelling Method](https://www.southampton.ac.uk/~tsh2n14/publications/chapters/eventb-dbook13.pdf)

### TLA+
- [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)
- [Use of Formal Methods at Amazon Web Services](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf)
- [How Amazon Web Services Uses Formal Methods](https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/)
- [TLA+ in Practice and Theory](https://pron.github.io/posts/tlaplus_part3)

### Alloy
- [Alloy (specification language) - Wikipedia](https://en.wikipedia.org/wiki/Alloy_(specification_language))
- [Alloy Analyzer](https://alloytools.org/)
- [Formal Software Design with Alloy 6](https://haslab.github.io/formal-software-design/overview/index.html)

### CSP
- [Communicating sequential processes - Wikipedia](https://en.wikipedia.org/wiki/Communicating_sequential_processes)
- [CSP: A Practical Process Algebra](https://www.cs.ox.ac.uk/files/12724/cspfdrstory.pdf)
- [Formalization and Verification of PaxosStore](https://www.mdpi.com/2079-9292/14/5/823)

### CCS
- [Calculus of communicating systems - Wikipedia](https://en.wikipedia.org/wiki/Calculus_of_communicating_systems)
- [CCS, the Calculus of Communicating Systems](https://link.springer.com/chapter/10.1007/978-3-319-42900-7_11)

### Petri Net
- [Formal Verification for Task Description Languages. A Petri Net Approach](https://www.mdpi.com/1424-8220/19/22/4965)
- [Design and Verification of Petri-Net-Based Cyber-Physical Systems](https://www.mdpi.com/1996-1073/16/1/67)
- [Petri Nets 2026](https://petrinets2026.informatik.uni-hamburg.de/)

### Coq / Rocq
- [Rocq - Wikipedia](https://en.wikipedia.org/wiki/Rocq)
- [The Rocq Prover](https://rocq-prover.org/docs)
- [CompCert](https://compcert.org/)
- [Pinpointing the Learning Obstacles of an Interactive Theorem Prover](https://sarajuhosova.com/assets/files/2025-icpc.pdf)

### Isabelle/HOL
- [Isabelle (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant))
- [Isabelle](https://isabelle.in.tum.de/)
- [seL4: Formal Verification of an OS Kernel](https://sel4.systems/Research/pdfs/comprehensive-formal-verification-os-microkernel.pdf)

### Lean
- [Lean (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/Lean_(proof_assistant))
- [Lean Programming Language](https://lean-lang.org/)
- [How the Lean language brings math to coding](https://www.amazon.science/blog/how-the-lean-language-brings-math-to-coding-and-coding-to-math)
- [The Lean FRO Year 3 Roadmap](https://lean-lang.org/fro/roadmap/y3/)

### Agda
- [Agda (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Agda_(programming_language))
- [What is Agda?](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html)
- [GitHub - agda/agda](https://github.com/agda/agda)

### RAISE / RSL
- [RAISE | The RAISE specification language, method, and tools](https://raisetools.github.io/)
- [The RAISE Specification Language](https://raisetools.github.io/material/documentation/raise-language.pdf)
- [The Logic of the RAISE Specification Language](https://link.springer.com/chapter/10.1007/978-3-540-74107-7_7)

### Frama-C / ACSL
- [Frama-C - Wikipedia](https://en.wikipedia.org/wiki/Frama-C)
- [Frama-C](https://www.frama-c.com/)
- [A gentle introduction to C code verification using Frama-C](https://hal.science/hal-03625208v1/document)

### Dafny
- [Dafny - Wikipedia](https://en.wikipedia.org/wiki/Dafny)
- [Dafny](https://dafny.org/)
- [GitHub - dafny-lang/dafny](https://github.com/dafny-lang/dafny)

### SPIN / Promela
- [SPIN model checker - Wikipedia](https://en.wikipedia.org/wiki/SPIN_model_checker)
- [Spin - Formal Verification](https://cse.msu.edu/~cse470/Public/Software/spin/whatispin.html)
- [GitHub - nimble-code/Spin](https://github.com/nimble-code/Spin)

### Comparison and Selection
- [How to Choose Between Model Checking and Theorem Proving](https://www.chainscorelabs.com/en/guides/guides-test-2026/formal-verification/how-to-choose-between-model-checking-and-theorem-proving)
- [Formal verification of bioinformatics software](https://academic.oup.com/bib/article/26/4/bbaf383/8221466)
- [Analysis of Three Formal Methods-Z, B and VDM](https://www.ijert.org/research/analysis-of-three-formal-methods-z-b-and-vdm-IJERTV1IS4227.pdf)
