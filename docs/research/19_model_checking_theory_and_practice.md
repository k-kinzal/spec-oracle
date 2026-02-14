# モデル検査の理論と実践

## 概要

モデル検査（Model Checking）は、ハードウェアやソフトウェアシステムが形式仕様を満たすかどうかをアルゴリズム的に検証する形式手法である。1980年代初頭にEdmund Clarke、Allen Emerson、Joseph Sifakis（2007年チューリング賞受賞）らによって独立に開発された。モデル検査は、システムの状態空間を網羅的に探索し、時相論理で記述された性質を自動的に検証する点が特徴である。

本調査では、モデル検査の理論的基盤となる時相論理、主要なツール群、状態爆発問題とその対策、反例生成、産業応用事例について詳述する。

## 1. モデル検査の基本概念

### 1.1 Kripke構造

モデル検査の基本的なモデルは**Kripke構造**である。Kripke構造は状態遷移システムの一種で、以下の4つの要素から構成される：

- **S**: 状態の有限集合
- **R**: 状態間の遷移関係（R ⊆ S × S）
- **I**: 初期状態の集合（I ⊆ S）
- **L**: 状態ラベリング関数（各状態に原子命題の集合を割り当てる）

Kripke構造は有向グラフとして表現され、ノードがシステムの到達可能な状態を、エッジが状態遷移を表す。各ノードには、その状態で成立する命題のラベルが付与される。この形式化により、自然言語で記述された曖昧な仕様を厳密な数学的表現に変換し、アルゴリズム的な検証を可能にする。

### 1.2 モデル検査の手順

モデル検査は以下の基本的な流れで実行される：

1. **モデル化**: システムの振る舞いを有限状態機械（Kripke構造など）として形式化
2. **仕様記述**: 検証したい性質を時相論理式で記述
3. **自動検証**: モデル検査器がシステムの全状態を探索し、仕様を満たすかチェック
4. **反例生成**: 性質が満たされない場合、違反する実行パスを反例として出力

この自動性が、手動の証明を要する定理証明と比較したモデル検査の大きな利点である。

## 2. 時相論理

時相論理（Temporal Logic）は、時間の経過に伴う命題の真偽値の変化を記述するための様相論理の一種である。モデル検査では、システムの動的性質を記述する仕様言語として時相論理が用いられる。

### 2.1 線形時相論理（LTL: Linear Temporal Logic）

LTLは時間を線形の経路として扱う論理体系である。システムの実行を単一の無限経路として捉え、その経路上で成立する性質を記述する。

**基本演算子**:
- **X φ** (Next): 次の状態でφが成立
- **F φ** (Finally/Eventually): いずれφが成立する
- **G φ** (Globally/Always): 常にφが成立する
- **φ U ψ** (Until): ψが成立するまでφが成立し続ける

**LTLの特徴**:
- 線形時間の視点で、反応型システムの性質記述に適している
- モデル検査はPSPACE完全問題
- 安全性（Safety）・活性（Liveness）性質の記述が直感的

**例**:
- `G(request → F grant)`: 「要求が発生すれば、いずれ承認される」
- `G(¬deadlock)`: 「デッドロックが決して起きない」

### 2.2 計算木論理（CTL: Computation Tree Logic）

CTLは分岐時間論理であり、時間を木構造として扱う。未来が一意に決定されず、複数の実行経路が存在することを表現できる。

**経路量化子**:
- **A** (All paths): すべての経路で成立
- **E** (Exists path): ある経路で成立

**状態演算子**: X, F, G, U（LTLと同様）

CTLでは、経路量化子と状態演算子を必ずペアで使用する。

**例**:
- `AG(request → EF grant)`: 「すべての状態で、要求が発生すれば、ある経路でいずれ承認される」
- `AG EF restart`: 「すべての状態から、再起動可能な状態に到達できる経路が存在する」

**CTLの特徴**:
- モデル検査はP-TIME完全（多項式時間）で効率的
- 可能性と必然性を区別した記述が可能

### 2.3 CTL*

CTL*はLTLとCTLの両方を包含する上位の論理体系である。経路量化子と時相演算子を自由に組み合わせることができる。

**関係性**:
- CTL* ⊃ CTL
- CTL* ⊃ LTL
- CTLとLTLは共通部分を持つが、互いに比較不可能（一方が他方を包含しない）

**計算複雑性**:
- CTL*のモデル検査はPSPACE完全

CTL*は表現力が最も高いが、計算コストも最大となるため、実用上はLTLまたはCTLが選択されることが多い。

## 3. 主要なモデル検査ツール

### 3.1 SPIN/Promela

**SPIN**（Simple Promela Interpreter）は、並行・分散システムの検証に広く使用される明示的状態モデル検査器である。Gerard Holzmannによってベル研究所で開発された。

**特徴**:
- **Promela**（Process Meta Language）という専用のモデリング言語を使用
- プロセスの動的生成、非同期通信、非決定性をサポート
- LTL性質の検証が可能
- 部分順序削減（Partial Order Reduction）による状態削減
- 産業界での通信プロトコル検証に広く利用

**適用領域**:
- 通信プロトコル（TCP/IP層、無線プロトコル）
- 組み込みシステムの並行制御
- PLCソフトウェアの検証

### 3.2 NuSMV

**NuSMV**は、カーネギーメロン大学（CMU）とイタリアのFBK（Fondazione Bruno Kessler）で開発された記号モデル検査器である。SMV（Symbolic Model Verifier）の後継ツールである。

**特徴**:
- BDD（二分決定図）ベースの記号モデル検査
- CTL、LTL両方の時相論理をサポート
- 有界モデル検査（BMC）機能も統合
- 産業界でのハードウェア検証に多用

**nuXmv**:
NuSMVの拡張版で、SMTソルバーベースのモデル検査、無限状態システムのサポートなど、より高度な機能を提供する。

### 3.3 TLA+/TLC

**TLA+**（Temporal Logic of Actions）は、Leslie Lamportによって開発された形式仕様言語である。分散システムやアルゴリズムの仕様記述に特化している。

**TLC**は、TLA+仕様のモデル検査器である。

**特徴**:
- 仕様記述言語と性質記述言語が同一（TLA+そのもの）
- 高レベルの抽象化が可能
- Amazon Web Services、Microsoft、IntelなどがTLA+を採用
- Paxos、Raft等の分散合意アルゴリズムの検証実績

**応用事例**:
- AWS S3、DynamoDB、EC2等の分散システム設計検証
- 並行データ構造の検証

### 3.4 その他の主要ツール

**UPPAAL**:
- リアルタイムシステムのモデル検査器
- タイムドオートマトンを用いたモデリング
- 組み込み制御システム、プロトコル検証に使用

**PAT**（Process Analysis Toolkit）:
- シンガポール国立大学で開発
- 確率モデル検査をサポート
- サイバーフィジカルシステムの検証

**CBMC**（C Bounded Model Checker）:
- Cプログラムの有界モデル検査
- SATソルバーベース
- バッファオーバーフロー、アサーション違反の検出

## 4. 状態爆発問題（State Explosion Problem）

### 4.1 問題の本質

モデル検査における最大の課題は、**状態爆発問題**である。システムの状態変数が増加すると、状態空間のサイズが指数関数的に増大する。

例えば、n個のブール変数を持つシステムは2^n個の状態を持つ。実際の産業システムでは、状態空間が10^100を超えることも珍しくなく、明示的な状態列挙による検証は不可能となる。

この問題を解決するため、様々な状態削減技法が開発されてきた。

### 4.2 記号モデル検査とBDD

**記号モデル検査**（Symbolic Model Checking）は、状態を個別に列挙せず、論理式として集合的に表現する手法である。

**二分決定図（BDD: Binary Decision Diagram）**:
- ブール関数を有向非巡回グラフとして効率的に表現
- Ken McMillanが1987年にBDDを用いたCTLモデル検査アルゴリズムを実装
- 実用上、指数関数的に小さい表現が可能な場合が多い

**利点**:
- 大規模な状態空間を扱える
- CTLモデル検査は多項式時間で実行可能

**課題**:
- BDDのサイズは変数順序に敏感
- 最適な変数順序の発見は計算困難

### 4.3 抽象化とCEGAR

**抽象化**（Abstraction）は、システムの詳細を削除し、検証に必要な情報のみを保持する縮約モデルを構築する手法である。

**CEGAR**（Counter-Example Guided Abstraction Refinement）:
- 2000年にClarkeらによって提案
- 反例を用いた反復的な抽象化改良プロセス

**CEGARの動作フロー**:
1. 高度に抽象化されたモデルを構築
2. 抽象モデルに対してモデル検査を実行
3. 違反が検出された場合、反例が本物か偽物（spurious）か判定
4. 偽の反例の場合、抽象化を改良（refinement）して再検査
5. 本物の反例または検証成功まで繰り返す

**述語抽象化**（Predicate Abstraction）:
- CEGARとの相性が良い抽象化技法
- 反例に基づいて述語を逐次追加し、抽象化レベルを調整

### 4.4 部分順序削減

**部分順序削減**（Partial Order Reduction）は、並行システムにおける独立な遷移の実行順序を削減する技法である。

**基本原理**:
- プロセスAとBの実行順序が結果に無関係な場合（可換性）、ABとBAの両方を探索する必要はない
- 同値な実行パスの代表のみを探索

**適用例**:
- SPINツールに実装され、並行プロトコルの検証に有効
- 状態数を大幅に削減（場合により指数関数的削減）

### 4.5 対称性削減

システムに対称性が存在する場合（例：複数の同一プロセス）、対称な状態を同一視して状態数を削減する技法。

## 5. 有界モデル検査（Bounded Model Checking, BMC）

### 5.1 BMCの基本概念

**有界モデル検査**は、システムの振る舞いを深さkまでに制限し、その範囲内で性質違反を探索する手法である。1999年にArmin Biereらによって提案された。

**特徴**:
- BDDではなくSAT/SMTソルバーを利用
- 深さkの経路に沿った反例の存在を論理式に変換
- SATソルバーが充足可能解を見つければ、それが反例となる

### 5.2 BMCの利点と限界

**利点**:
- 浅いエラーの発見が高速
- BDDベースのモデル検査では扱えない大規模システムに適用可能
- 短い反例を効率的に生成
- SMTソルバーによりデータ型の扱いが容易

**限界**:
- エラーが存在しない証明には不向き（BDDベースが優位）
- 深さkを増やすと計算量が増大
- 完全性の保証には追加の議論が必要

### 5.3 産業応用

BMCは以下の領域で広く使用されている：
- ハードウェア検証（Intel, IBM等の半導体企業）
- 組み込みソフトウェアのバグ検出（CBMC等のツール）
- セキュリティ脆弱性の発見

## 6. 反例生成

### 6.1 反例の役割

モデル検査の重要な特徴の一つは、性質が満たされない場合に**反例**（Counterexample）を自動生成できることである。

反例は以下の情報を提供する：
- 性質違反に至る具体的な実行パス（状態遷移の系列）
- 各状態における変数の値
- 違反箇所の特定

これにより、開発者はバグの原因を迅速に理解し、修正できる。

### 6.2 反例の最小化

実際のシステムでは、反例が非常に長くなることがある。反例を短縮・簡潔化する研究が進められている：
- **最短反例の探索**: BFS（幅優先探索）による最短経路発見
- **有意な反例の抽出**: 因果関係に基づく反例の説明
- **視覚化ツール**: 反例を理解しやすく可視化（Oeritte等のツール）

### 6.3 偽の反例（Spurious Counterexample）

抽象化を用いたモデル検査では、抽象モデルで検出された反例が元のシステムでは再現できない「偽の反例」が生じることがある。CEGARはこの偽の反例を用いて抽象化を改良する。

## 7. 産業応用事例

### 7.1 ハードウェア検証

**Intel Pentium FDIV Bug（1994年）**:
- Pentiumプロセッサの浮動小数点除算ユニット（FPU）のバグ
- ルックアップテーブルのPLA（プログラマブル論理アレイ）に5つのエントリ欠損
- リコール費用は約4億7500万ドル

**影響**:
- この事件を契機に、半導体業界で形式検証の利用が急増
- 1996年に「ワードレベルモデル検査」技術が開発され、SRTアルゴリズムの検証に適用
- Intelは以降のPentium 4開発で記号軌跡評価（STE）と定理証明を使用
- Nehalemアーキテクチャ（2008年）は、形式検証を主要な検証手法として採用した最初のIntelマイクロアーキテクチャ

**その他の成功事例**:
- IBM、Intel、Motorola等でハードウェアモデル検査が定常的に使用
- 大規模FPGA/ASIC設計の検証
- 富士通の大規模IPコア設計（約500ラッチ、1万行のSMVコード）でCEGARの有効性を確認

### 7.2 ソフトウェア検証

**航空宇宙・安全重要システム**:
- **Simulink Design Verifier**: 航空エンジン監視機能の実世界問題報告に適用
- NASA等での宇宙機制御ソフトウェアの検証

**自動車産業**:
- Ford Motor Companyの組み込みCプログラムに対する学術ツールの評価
- CBMC、ESBMC、2LS、Smack、CPAChecker、UltimateAutomizer等のツール使用

**PLC（プログラマブルロジックコントローラ）ソフトウェア**:
- SPIN、SMV、UPPAALを用いた検証
- 製造業、プロセス制御システムでの応用

**通信プロトコル**:
- TCP/IPスタック、無線プロトコル（Bluetooth、Wi-Fi）の検証
- SPINによる通信プロトコルの並行性検証

### 7.3 分散システム

**Amazon Web Services (AWS)**:
- TLA+を用いてS3、DynamoDB、EC2等の分散システム設計を検証
- 複雑な分散合意プロトコルのバグを設計段階で発見

**Microsoft**:
- Azure等のクラウドサービスの設計検証にTLA+を活用
- Cosmos DBの一貫性プロトコルの検証

### 7.4 サイバーフィジカルシステム

**確率モデル検査の応用**:
- 動的電力管理（Dynamic Power Management）
- 組み込み制御システムのリアルタイム性質検証
- PATツールによる事例研究

### 7.5 産業導入の課題

形式検証技術は成功を収めているが、広範な産業採用にはまだ課題がある：
- **技法とツールのアクセシビリティ**: 専門知識の必要性
- **スケーラビリティ**: 大規模システムへの適用の困難さ
- **実証評価の不足**: 産業文脈での経験的評価が必要

それでも、ハードウェア検証では主要企業（IBM、Intel、Motorola、Lucent）で定常的な使用が確立されている。

## 8. モデル検査の限界と今後の展望

### 8.1 限界

1. **状態爆発問題**: 依然として根本的な課題
2. **無限状態システム**: 有限状態への抽象化が必要
3. **モデリングコスト**: 正確なモデル作成には専門知識と時間が必要
4. **仕様の記述**: 時相論理の習得が必要

### 8.2 今後の展望

1. **機械学習との融合**:
   - 抽象化戦略の自動学習
   - 反例からのパターン認識

2. **並列・分散モデル検査**:
   - クラウド環境での大規模並列探索
   - GPUの活用

3. **ハイブリッド検証**:
   - モデル検査、定理証明、テストの統合
   - 各手法の強みを組み合わせた検証

4. **AI駆動のモデル生成**:
   - ソースコードやドキュメントからの自動モデル抽出
   - LLMを用いた仕様の形式化支援

5. **産業標準化**:
   - モデル検査ツールのエコシステム整備
   - 産業界での教育・訓練プログラムの充実

## 9. まとめ

モデル検査は、形式手法の中でも実用化が最も進んでいる技術の一つである。時相論理に基づく厳密な仕様記述と自動的な検証、反例生成の能力により、ハードウェアやソフトウェアシステムの信頼性向上に大きく貢献してきた。

**主要な成果**:
- 時相論理（LTL、CTL、CTL*）による性質記述の体系化
- BDD、SAT/SMT、CEGAR等の状態削減技法による実用化
- SPIN、NuSMV、TLA+等の成熟したツール群
- Intel Pentiumバグ以降の半導体業界での標準的な採用
- AWS、Microsoft等のクラウド企業での分散システム検証

**今後の課題**:
- より大規模で複雑なシステムへのスケーラビリティ
- ソフトウェア領域での更なる普及
- AIとの融合による自動化の推進

モデル検査は、仕様駆動開発における中核的な保証技術として、今後も発展を続けると期待される。

## 参考文献・情報源

### 日本語資料
- [原理から学ぶモデル検査 土屋達弘(大阪大学)](https://ws.cs.kobe-u.ac.jp/~masa-n/ses2011/ses2011_tutorial4.pdf)
- [時相論理 筑波大学 水谷氏資料](http://www.cs.tsukuba.ac.jp/~mizutani/under_grad/programtheory/2014/2014-09.pdf)
- [モデル検査 - Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%A2%E3%83%87%E3%83%AB%E6%A4%9C%E6%9F%BB)
- [IEICE 3章 モデル検査](https://www.ieice-hbkb.org/files/07/07gun_01hen_03.pdf)
- [形式手法特論：CEGARを用いたモデル検査の状態空間削減](https://speakerdeck.com/ytaka23/kernel-vm-study-hokuriku-part-8)
- [SPINによるモデル検査](https://swest.toppers.jp/SWEST10/minutes/S2-a-material-nonaka.pdf)
- [SPIN使い方ヒント](https://formal.mri.co.jp/items/docs/4_16_%E3%83%95%E3%82%A9%E3%83%BC%E3%83%9E%E3%83%AB%E3%83%A1%E3%82%BD%E3%83%83%E3%83%89%E5%B0%8E%E5%85%A5%E3%82%AC%E3%82%A4%E3%83%89%E3%83%A9%E3%83%B3%E3%82%B9R29_4.pdf)
- [30年前のPentium FDIVバグを追跡](https://tech-tools.reinforz.co.jp/5639)

### 英語資料

**理論・教科書**
- [Model Checking - Wikipedia](https://en.wikipedia.org/wiki/Model_checking)
- [Computation tree logic - Wikipedia](https://en.wikipedia.org/wiki/Computation_tree_logic)
- [Linear temporal logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_temporal_logic)
- [CTL* - Wikipedia](https://en.wikipedia.org/wiki/CTL*)
- [The Complexity of Temporal Logic Model Checking - Ph. Schnoebelen](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/Sch-aiml02.pdf)

**状態爆発問題と対策**
- [Model Checking and the State Explosion Problem - Clarke, Klieber](https://pzuliani.github.io/papers/LASER2011-Model-Checking.pdf)
- [Progress on the State Explosion Problem in Model Checking](https://www.researchgate.net/publication/221025695_Progress_on_the_State_Explosion_Problem_in_Model_Checking)
- [Symbolic model checking: an approach to the state explosion problem - McMillan](https://www.semanticscholar.org/paper/Symbolic-model-checking:-an-approach-to-the-state-McMillan/a08b88801703b8a964fc323ede6c86a5a53a7b9f)

**CEGAR**
- [Counterexample-guided abstraction refinement - Wikipedia](https://en.wikipedia.org/wiki/Counterexample-guided_abstraction_refinement)
- [Counterexample-guided Abstraction Refinement - Stanford](https://web.stanford.edu/class/cs357/cegar.pdf)
- [Predicate Abstraction and CEGAR - UT Austin](https://www.cs.utexas.edu/~isil/cs389L/cegar-6up.pdf)

**BMC**
- [Bounded Model Checking with SAT/SMT - Edmund M. Clarke](https://www.cs.cmu.edu/~emc/15414-s14/lecture/Lecture%202%20Bounded%20MC%20with%20SAT_SMT.pdf)
- [Bounded Model Checking - Armin Biere et al.](https://www.cs.cmu.edu/~emc/papers/Books%20and%20Edited%20Volumes/Bounded%20Model%20Checking.pdf)
- [Bounded Model Checking - Freiburg](https://cca.informatik.uni-freiburg.de/papers/Biere-SAT-Handbook-2021-BMC-Chapter-Manuscript.pdf)

**ツール**
- [List of model checking tools - Wikipedia](https://en.wikipedia.org/wiki/List_of_model_checking_tools)
- [Model Checking Cheat Sheet](https://mluckcuck.github.io/model-checking-cheatsheet)
- [GitHub - model-checking with LTL, CTL and CTL*](https://github.com/paultristanwagner/model-checking)
- [The Investigation of TLC Model Checker Properties](https://www.researchgate.net/publication/304894406_The_Investigation_of_TLC_Model_Checker_Properties)
- [Specifying and Verifying Concurrent C Programs with TLA+](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/MLBHB-ftscs15.pdf)

**反例生成**
- [Counterexamples in Model Checking – A Survey](https://www.informatica.si/index.php/informatica/article/download/1442/1179/0)
- [A Systematic Literature Review on Counterexample Explanation](https://arxiv.org/pdf/2201.03061)
- [Visual counterexample explanation for model checking with Oeritte](https://www.researchgate.net/publication/348079212_Visual_counterexample_explanation_for_model_checking_with_Oeritte)

**産業応用**
- [How Intel makes sure the FDIV bug never happens again](https://www.chiplog.io/p/how-intel-makes-sure-the-fdiv-bug)
- [Pentium FDIV bug - Wikipedia](https://en.wikipedia.org/wiki/Pentium_FDIV_bug)
- [Intel's $475 million error: the silicon behind the Pentium division bug](https://www.righto.com/2024/12/this-die-photo-of-pentium-shows.html)
- [A case study in model checking software systems](https://www.sciencedirect.com/science/article/pii/S0167642396000202)
- [A Candid Industrial Evaluation of Formal Software Verification using Model Checking](https://www.researchgate.net/publication/260245263_A_Candid_Industrial_Evaluation_of_Formal_Software_Verification_using_Model_Checking)
- [Software Model Checking in Practice: An Industrial Case Study](https://patricegodefroid.github.io/public_psfiles/icse2002.pdf)
- [An overview of model checking practices on verification of PLC software](https://www.researchgate.net/publication/273001940_An_overview_of_model_checking_practices_on_verification_of_PLC_software)
- [Formal Methods in Industry](https://dl.acm.org/doi/full/10.1145/3689374)

**Partial Order Reduction**
- [Partial-Order Reduction - Springer](https://link.springer.com/chapter/10.1007/978-3-319-10575-8_6)

**Kripke構造**
- [Kripke structure (model checking) - Wikipedia](https://en.wikipedia.org/wiki/Kripke_structure_(model_checking))
- [Kripke Structure - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/kripke-structure)

---

**調査担当**: researcher-19
**調査日**: 2026年2月
**文字数**: 約4,800字
