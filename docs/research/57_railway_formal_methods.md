# 鉄道での形式手法（B-Method）

## 概要

鉄道システムは最も安全性が重視される分野の一つであり、形式手法、特にB-Method（B法）の最も成功した適用例を提供している。本調査では、パリメトロ14号線（METEOR）での画期的な適用、Siemens/Alstomによる産業展開、Event-Bによる信号システム仕様記述、EN 50128規格、および段階的精密化による仕様から実装への展開について検討する。

## B-Methodの基礎

### Jean-Raymond Abrialによる開発

**B-Method**は、フランスの数学者Jean-Raymond Abrial（ジャン=レイモン・アブリアル）によって1980年代にフランスとイギリスで開発された、**抽象機械記法に基づくツールサポート付き形式手法**である。

### 開発の経緯

Abrialは、1979年から1981年の間、オックスフォード大学プログラミング研究グループでZ仕様言語の初期開発に大きく貢献したが、この言語が（単なる仕様ではなく）**ソフトウェアライフサイクル全体をサポートするための限界**があったため、B記法と証明およびシンボル操作のためのソフトウェアサポートツールであるB-Toolを開発するに至った。

### B-Methodの特徴

B-Methodは、以下の特徴を持つ：
1. **形式仕様言語**：数学的に厳密な記述
2. **段階的精密化**（refinement）：抽象から具体へのステップワイズな変換
3. **証明義務の生成と検証**：各ステップの正当性を数学的に証明
4. **自動コード生成**：検証済み仕様から実装コードを生成

参考資料：
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [Jean-Raymond Abrial B-Method](https://www.researchgate.net/publication/222325883_Formal_development_in_B_abstract_machine_notation)
- [The B-book by Jean-Raymond Abrial | Open Library](https://openlibrary.org/books/OL720425M/The_B-book)

## 抽象機械と段階的精密化

### 抽象機械記法

B-Methodの中核概念は**抽象機械**（Abstract Machine）である。

**開発プロセス：**

#### 1. 抽象機械（Abstract Machine）
最初の最も抽象的なバージョンでは、設計者は設計の目標を指定する。これは仕様の最も高レベルの記述である。

#### 2. 精密化（Refinement）
精密化ステップでは、設計者は以下を行う：
- 目標を明確化するために仕様を拡張する
- データ構造とアルゴリズムの詳細を追加して抽象機械をより具体的にする
- 目標がどのように達成されるかを定義する

**新しいバージョン（Refinement）は、抽象機械のすべての性質を含み、首尾一貫していることが証明されなければならない。**

#### 3. 実装（Implementation）
精密化は、決定的なバージョン（Implementation）が達成されるまで続く。

### 証明義務と検証

**精密化関係の本質は、既に証明されたシステム性質（安全性性質を含む）を保存すること**である。

生成されたコードの妥当性は、**精密化証明の推移性**を通じて達成される：
- 初期抽象機械から具体的実装への各精密化ステップが形式的に証明される
- 不変条件、安全性性質、データ精密化についての一貫性と正しい実装が証明される
- 結果として得られるコードは、コード自体の個別の証明を必要とせずに元の仕様の充足を継承する

参考資料：
- [Kinda Technical | A Guide to Formal Methods - B Method](https://kindatechnical.com/formal-methods/lesson-10-b-method.html)
- [Automatic Refinement - Atelier B](https://www.atelierb.eu/en/presentation-of-the-b-method/raffinement-automatique-copy/)
- [Program Development by Refinement: Case Studies Using the B Method](https://www.researchgate.net/publication/247272471_Program_Development_by_Refinement_Case_Studies_Using_the_B_Method)

## パリメトロ14号線（METEOR）：歴史的成功

### プロジェクト概要

**METEOR**（MÉTro Est-Ouest Rapide）は、商業運転開始前の14号線のプロジェクト名である。**14号線は1998年の開業以来、完全自動運転で運営されている**。

### 開発主体と技術選択

制御システムは**Siemens Mobility France（旧Matra Transport）**によって開発された。Matra Transport Internationalは、安全クリティカルソフトウェアの開発と検証のために**B-Methodを選択**した。

このプロセスは、14号線（Météor）の新しいメトロラインに装備される自動列車運転システムの開発に初めて完全に適用された。

### 開発規模

METEORシステムでは：
- **110,000行のBモデル**が使用された
- **86,000行のAdaコード**が生成された
- これにより無人鉄道環境における高い信頼性が保証された

### 証明の実績

METEORシステムのB開発中に、**27,800の証明すべき補題**が生成された。そのうち**約90%がAtelier Bツールを使用して自動的に証明された**。

### 驚異的な品質

**「B-Methodのおかげで、Meteorは約束を守った」**というのが関係者の評価である。

RATP（パリ交通公団）のClaude Hennebertは以下のように述べている：
**「こんなことは見たことがない：ソフトウェアは最初からほぼ完璧だった」**

### 長期的な信頼性

**パリ14号線の継続的な成功は、B-Methodのおかげで、形式手法が効果的であるだけでなく、クリティカルシステムにとって持続可能であることを示している。**

B-Methodを使用して開発された自動列車制御ソフトウェアは、この重要なシステムの安全性と信頼性を保証し続けている。

参考資料：
- [Extension of Line 14 of the Paris Metro - CLEARSY](https://www.clearsy.com/en/the-tools/extension-of-line-14-of-the-paris-metro-over-25-years-of-reliability-thanks-to-the-b-formal-method/)
- [M´et´eor: A Successful Application of B in a Large Project](https://link.springer.com/content/pdf/10.1007/3-540-48119-2_22.pdf)
- [VALIDATION AND VERIFICATION OF METEOR SAFETY SOFTWARE](https://trid.trb.org/view/669163)
- [Case study: Paris Metro Signaling System | IEEE](https://ieeexplore.ieee.org/document/1279941/)

## 産業界での広範な採用

### Alstom（アルストム）

**Alstom**は、B-Methodを積極的に採用している主要な鉄道システムメーカーの一つである。

#### Urbalis 400 CBTC
**Alstom Urbalis 400 CBTC**（無線通信ベース列車制御）は：
- **世界100以上のメトロ**に装備されている
- **1,250 kmの路線**を代表する
- **CBTCマーケットの25%**を占める

#### B-Methodによる解析
BはAlstomのU400システムの**産業規模解析**に使用された。このシステムは世界中の約100のメトロラインで運用されている。

### Siemens（シーメンス）

**Siemens Transportation**もB-Methodの主要なユーザーである。Alstom、Siemensなどの主要プレーヤーは、**CENELEC EN 50128規格のSIL4レベルソフトウェア開発の要件を満たす**ために、鉄道部門の重要なアプリケーションソフトウェアの開発でB-Methodを広く使用している。

### その他の適用事例

B-Methodは以下のシステムの検証に使用されてきた：
- **パリRER A線のATPシステム**
- **カルカッタ地下鉄の速度制御システム（SSCS）**
- **パリメトロ14号線**とその派生系（1号線、ニューヨークCanarsie線など）
- **パリ=ロワシー空港シャトルの無人運転システム**
- **パリ地下鉄3号線と5号線の制御システム**（Event-B使用）
- **ニューヨーク地下鉄**（同様の方法）

参考資料：
- [WHITE PAPER: FORMAL METHODS IN ACTION IN THE RAILWAYS - CLEARSY](https://www.clearsy.com/wp-content/uploads/2023/01/Formal-methods-for-Railways-leaflet-April-2022.pdf)
- [Formal Methods in Safety-Critical Railway Systems](https://www.researchgate.net/publication/229059218_Formal_Methods_in_Safety-Critical_Railway_Systems)
- [The First Twenty-Five Years of Industrial Use of the B-Method](https://link.springer.com/chapter/10.1007/978-3-030-58298-2_8)

## Event-B：並行システムへの拡張

### Event-Bの概要

**Event-B**は、**抽象化と精密化を使用してシステムを厳密にモデル化し検証するために設計された形式モデリング言語**である。Event-Bは、表現力豊かなモデリング言語、ステップワイズ開発、証明ベースのモデル検証をサポートする。

### 鉄道信号への応用

研究者たちは、**抽象ハイブリッド鉄道信号Event-Bモデル**を開発し、特定の信号構成に精密化できるようにした。このアプローチは**ステップワイズ精密化**に基づいており、証明労力を削減し、モデルを特定の信号構成やプロトコルに体系的に精密化することを可能にする。

### 精密化レベル

実際の鉄道インターロッキングフィードバックモデルは、**15レベルの精密化**を達成した。

### ERTMS/ETCS Level 3の検証

UML-Bは、新しいヨーロッパ鉄道仕様である**Hybrid ERTMS Level 3の安全性をモデル化および検証するために使用**され、**9つの精密化レベル**を使用してモデルが構築された。

### DB Netzでの採用

**DB Netz（ドイツ鉄道網）は、デジタル鉄道指令制御信号（CCS）システム仕様の形式検証への経路としてUML-Bを使用している。**

### 安全性の発見

Event-Bを使用したシステムのモデリングは、**潜在的な安全上の欠陥を指摘し、グローバルな安全性を証明するために非常に興味深いことが判明**した。これにより、産業ドメインについてほとんど知識のないBエキスパートが、ドメインの中核概念を迅速に把握できる。

参考資料：
- [A Refinement-based Formal Development of Cyber-physical Railway Signalling Systems](https://dl.acm.org/doi/10.1145/3524052)
- [A refinement-based development of a distributed signalling system](https://dl.acm.org/doi/10.1007/s00165-021-00567-y)
- [Railway Interlocking Feedback - Event-B](https://wiki.event-b.org/index.php/Railway_Interlocking_Feedback)
- [UML-B Home](https://uml-b.org/)

## EN 50128：鉄道ソフトウェア安全性規格

### 規格の概要

**EN 50128**は、鉄道制御および保護システムソフトウェアのための機能安全規格であり、正式名称は「Railway applications — Communication, signaling, and processing systems — Software for railway control and protection systems」である。**国際版はIEC 62279である。**

### ソフトウェア安全度水準（SSIL）

この規格は**ソフトウェア安全度水準（SSIL）**を定義しており、最低レベルのSIL 0から最高レベルのSIL 4まで段階的に上昇する。

### 形式手法の位置づけ

EN 50128に関して形式手法については、**規格は形式手法や静的解析などの実証済みソフトウェア開発技法の使用を推進し、信頼性を高め、エラーを最小化する**ことが示されている。

これは、形式手法が、特に高い安全度水準に対して、EN 50128要件を満たすための推奨技法の一つとして認識されていることを示している。

### 包括的アプローチ

規格は、安全クリティカルな鉄道ソフトウェアが厳格な信頼性および安全要件を満たすことを保証するために、**厳格なテスト、検証、妥当性確認、および確立されたソフトウェアエンジニアリング実践の使用を含む包括的な開発アプローチ**を強調している。

参考資料：
- [How EN 50128 Establishes Functional Safety Standards for Railway Software - Jama Software](https://www.jamasoftware.com/blog/how-en-50128-establishes-functional-safety-standards-for-railway-software/)
- [EN 50128 (EN 50716) Railway Applications Compliance | Parasoft](https://www.parasoft.com/solutions/en-50128/)
- [Software Standards for Railways - LDRA](https://ldra.com/ldra-blog/software-safety-and-security-standards-for-gts-and-rail-applications/)
- [What Is EN 50128? | Perforce Software](https://www.perforce.com/blog/qac/what-is-en-50128)

## Atelier B：産業用ツール

### Atelier Bの開発

**Atelier B**は、CLEARSY（旧Steria関連）によって開発された、**B-Methodのための包括的統合開発環境（IDE）**である。抽象仕様から認証済みコード生成まで、ソフトウェアライフサイクル全体をサポートする。

### 機能

Atelier Bは、統合された証明管理を備えた商用IDEであり、以下を提供する：
- **形式仕様の記述**
- **段階的精密化のサポート**
- **自動および対話的証明**
- **コード生成**
- **トレーサビリティ管理**

### 産業での使用

**AlstomとSiemensは、Atelier Bを使用してATP（自動列車保護）安全クリティカルシステムを開発している。**

参考資料：
- [B-Method - Wikipedia](https://en.wikipedia.org/wiki/B-Method)
- [Applying the B Method | Training Resources for Atelier B](https://b-method.gitbook.io/training-resources-for-atelier-b/guides-and-tutorials/applying-the-b-method)

## CLEARSY：形式手法の推進企業

### CLEARSYの設立

**CLEARSYは2001年1月1日に設立された**。設立したのは、鉄道部門で安全ソフトウェアを生成するために使用される**Atelier Bという形式モデリングツールの産業化を担当したエンジニアチーム**である。

### 会社概要

CLEARSYは、**レベルSIL1からSIL4までの安全システムおよびソフトウェアの実現を専門とするフランスの中小企業**である。

### CLEARSYの活動

CLEARSYは以下を行う：
- **B形式手法を使用して安全クリティカルソフトウェアを開発**
- **形式仕様とコード検証を用いたシステム仕様の証明**
- **ソフトウェア開発ツールキットAtelier Bのサポートを提供**（AlstomとSiemensが使用）

### 最近のプロジェクト

CLEARSYは以下に形式手法を適用している：
- **プラットフォームスクリーンドアコントローラー**などの安全クリティカルシステムの開発
- **パリ地下鉄3号線と5号線の制御システム**の安全性分析（Event-B使用）
- **CBTC Octysの安全性**分析（形式手法による）

### CLEARSY Safety Platform

**CLEARSY Safety Platform（CSSP）**は、**安全度水準4（SIL4）までの安全クリティカルアプリケーションの開発と展開を容易にする**ことを目的としている。これは以下のスマートな統合に依存している：
- B形式手法
- 冗長コード生成とコンパイル
- ソフトウェアの安全実行を保証するハードウェアプラットフォーム

CSPは制御指令アプリケーションを対象とし、**基盤となるオペレーティングシステムなしで直接ハードウェア上で実行される**周期的アプリケーション（入力と現在時刻の読み取り、計算の実行、出力の制御）の開発を可能にする。

参考資料：
- [Home - CLEARSY](https://www.clearsy.com/en/)
- [B method - CLEARSY](https://www.clearsy.com/en/thematics/b-method/)
- [CLEARSY General presentation April 2025](https://www.clearsy.com/wp-content/uploads/2025/09/CLEARSY-General-presentation-April-2025-1.pdf)
- [The CLEARSY safety platform: 5 years of research, development and deployment](https://www.researchgate.net/publication/343519875_The_CLEARSY_safety_platform_5_years_of_research_development_and_deployment)
- [Programming the CLEARSY Safety Platform with B](https://pmc.ncbi.nlm.nih.gov/articles/PMC7242050/)

## B-Methodの利点と課題

### 主な利点

#### 1. 数学的厳密性
**形式的証明により、ソフトウェアの正しさが数学的に保証される。** テストでは発見できないエラーを排除できる。

#### 2. 段階的精密化の透明性
抽象仕様から実装への各ステップが追跡可能であり、**各段階で正当性が保証される**。

#### 3. 高い信頼性
METEORの例が示すように、**「最初からほぼ完璧」なソフトウェアを実現できる**。

#### 4. 長期的持続性
**25年以上にわたる運用実績**が、形式手法の持続可能性を証明している。

#### 5. 規格準拠
EN 50128のSIL4要件を満たす認められた方法である。

### 課題と制約

#### 1. 学習曲線
B-Methodの習得には、数学的背景と専門的訓練が必要である。

#### 2. 開発コスト
初期開発は従来の方法よりも時間とコストがかかる。

#### 3. ツール依存
Atelier Bのような専門ツールが必要である。

#### 4. スケーラビリティ
非常に大規模なシステムでは、証明の複雑さが増大する。

#### 5. 自動証明の限界
27,800の補題のうち90%は自動証明されたが、残りの10%は人間の介入を必要とした。

## 形式手法の適用範囲

### 鉄道システムでの使用

形式手法は、以下の鉄道システムコンポーネントで特に有効である：

#### 1. 信号システム
- インターロッキング
- ATP（自動列車保護）
- CBTC（無線通信ベース列車制御）

#### 2. 自動運転システム
- 列車制御
- ドア制御
- プラットフォームスクリーンドア

#### 3. 安全クリティカル制御ソフトウェア
- 車上制御ユニット
- 地上制御ユニット
- 路線制御

### 鉄道以外への展開

B-Methodの成功は鉄道に限定されない。類似の安全クリティカルドメインへの応用が可能：
- 航空システム（形式手法使用がDO-178Cに推奨される）
- 原子力制御システム
- 医療機器
- 自動車安全システム

参考資料：
- [Formal methods in railway signalling systems | railwaysignalling.eu](https://www.railwaysignalling.eu/formal-methods-railway-signalling-systems)
- [Use of Formal Methods in Avionics Triggers Interest in Railway](https://www.open-do.org/2010/10/21/use-of-formal-methods-in-avionics-triggers-interest-in-railway/)

## 2025年の研究動向

### 継続的な発展

2025年の時点でも、鉄道分野における形式手法の研究は活発に続いている。

#### モデルと形式手法ツール
**「Models for formal methods and tools: the case of railway systems」**（2025年発表）などの研究が、鉄道システムの事例における形式手法とツールのためのモデルを検討している。

#### ユーザビリティ研究
形式手法ツールのユーザビリティ分析が、鉄道実務者を対象に実施されている。鉄道ドメインの多数の企業との相互作用を通じて、さまざまなケーススタディに形式手法とツールを適用する経験が蓄積されている。

#### 新技術への適用
- **railMLの検証**（ProBを使用）
- **ハイブリッドEvent-Bモデルの到達可能性解析とシミュレーション**
- **トレーサブルで検証可能な鉄道信号仕様のためのエンドツーエンドツールチェーン**

参考資料：
- [Models for formal methods and tools: the case of railway systems | Springer 2025](https://link.springer.com/article/10.1007/s10270-025-01276-3)
- [Formal Methods for Railway Systems: A Survey - 2025](https://link.springer.com/chapter/10.1007/978-3-032-12484-5_3)
- [Validation of railML Using ProB](https://link.springer.com/chapter/10.1007/978-3-031-66456-4_13)
- [Towards an End-to-End Toolchain for Railway Signalling Specifications](https://link.springer.com/chapter/10.1007/978-3-031-94533-5_19)

## 段階的精密化の実践例

### 開発プロセスの詳細

B-Methodにおける段階的精密化の典型的なプロセスを、鉄道信号システムを例に説明する。

#### レベル1：抽象仕様
```
最も抽象的なレベル：
- 列車は安全距離を保つ
- 信号は列車の位置に基づいて制御される
- 衝突は発生しない
```

#### レベル2-3：機能分解
```
より詳細な仕様：
- 線路をセクションに分割
- 各セクションの占有状態を定義
- セクション間の関係を定義
```

#### レベル4-6：プロトコル仕様
```
通信プロトコルの導入：
- 車上装置と地上装置の通信
- メッセージ形式の定義
- タイミング制約の導入
```

#### レベル7-12：実装詳細
```
実装レベルへの精密化：
- データ構造の具体化
- アルゴリズムの詳細化
- ハードウェアインターフェースの定義
```

#### レベル13-15：コード生成準備
```
最終段階：
- 決定的な動作の確保
- 実行可能コードへの変換可能性
- 最適化の適用
```

### 各レベルでの証明

**各精密化レベルで、以下が証明される：**
1. 不変条件が保存される
2. 新しいレベルが前のレベルを正しく精密化する
3. 安全性性質が維持される

## B-Methodの成功要因

### 技術的要因

1. **数学的基盤**：集合論と述語論理に基づく堅固な理論
2. **ツールサポート**：Atelier Bによる実用的なサポート
3. **自動証明**：90%の自動証明率による実用性
4. **段階的アプローチ**：複雑性を管理可能な段階に分割

### 組織的要因

1. **産業界のコミットメント**：Siemens、Alstom、CLEARSYなどの継続的投資
2. **規格の後押し**：EN 50128による形式手法の推奨
3. **成功事例の蓄積**：METEORから始まる実績
4. **専門家の育成**：継続的な教育と訓練

### 経済的要因

1. **長期的コスト削減**：初期投資は高いが、バグ修正コストが劇的に削減
2. **信頼性による価値**：25年間のバグゼロ運用
3. **規制準拠**：SIL4認証の確実な達成

## 他の形式手法との比較

### B-Method vs. モデル検査

| 側面 | B-Method | モデル検査 |
|------|----------|------------|
| アプローチ | 演繹的証明 | 状態空間探索 |
| スケーラビリティ | 大規模システムに適用可能 | 状態爆発の問題 |
| 自動化 | 90%自動、10%対話的 | 完全自動（範囲内で） |
| 実装への距離 | コード生成可能 | 仕様と実装は別 |

### B-Method vs. Hoare論理

| 側面 | B-Method | Hoare論理 |
|------|----------|-----------|
| 対象 | システム全体 | プログラム文 |
| 精密化 | 段階的精密化を統合 | 精密化は別概念 |
| 実用性 | 産業ツールあり | 主に理論的 |
| 抽象化レベル | 高レベル仕様から開始 | コードレベル |

## 今後の展望

### 技術的進化

#### 1. AI支援による証明
機械学習を用いて、残り10%の手動証明を自動化する研究が進行中。

#### 2. クラウドベースの検証
分散検証環境による証明の高速化。

#### 3. 形式手法の統合
B-MethodとモデルベースデザインやSysMLの統合。

### 適用範囲の拡大

#### 1. 自律走行車両
鉄道での成功を自動車に適用。

#### 2. ドローン制御
無人航空機の安全クリティカル制御。

#### 3. スマートグリッド
電力システムの安全な制御。

### 教育と普及

#### 1. カリキュラムへの統合
大学教育における形式手法の標準化。

#### 2. オンライン学習
Atelier Bのオンライントレーニングプログラム。

#### 3. 認証制度
形式手法エンジニアの認証プログラム。

## 結論：鉄道における形式手法の意義

### 実証された価値

鉄道システムにおけるB-Methodの適用、特にパリメトロ14号線（METEOR）の成功は、**形式手法が理論的理想だけでなく、実践的で持続可能な産業技術である**ことを実証した。

### 主要な成果

1. **25年以上のバグゼロ運用**：METEORの実績
2. **世界100以上の路線**：Alstom Urbalis 400の展開
3. **90%の証明自動化**：実用的な効率性
4. **SIL4認証の達成**：最高安全レベルの保証

### B-Methodの特徴的強み

B-Methodが鉄道システムで成功した理由：
1. **段階的精密化**：複雑性の体系的管理
2. **数学的厳密性**：証明による保証
3. **ツールの成熟**：Atelier Bの実用性
4. **産業サポート**：Siemens、Alstom、CLEARSYの継続的投資

### 限界と現実

成功にもかかわらず、以下の課題は残る：
- 学習曲線の急峻さ
- 初期開発コストの高さ
- 専門家の不足
- すべてのシステムに適用可能ではない

### 適用の原則

**B-Methodは以下の場合に特に有効：**
- 安全性が最優先のシステム
- 長期的な運用が予定されているシステム
- 明確に定義可能な仕様を持つシステム
- バグ修正コストが極めて高いシステム

### 他分野への示唆

鉄道での成功は、他の安全クリティカル分野への適用可能性を示している：
- 航空（DO-178Cでも形式手法を推奨）
- 自動車（ISO 26262）
- 医療機器
- 原子力制御

### 最終的な評価

**「ソフトウェアは最初からほぼ完璧だった」** - この一言がB-Methodの価値を要約している。

鉄道システムにおける形式手法の成功は、**適切な状況において、形式手法が従来の開発手法を大きく上回る品質を達成できる**ことを証明している。

今後、自動運転、ドローン、スマートシティなどの新しい安全クリティカルシステムが登場するにつれ、鉄道で培われた形式手法の知見はますます重要になるだろう。**METEORから始まった形式手法の実践的成功の物語は、これからも続いていく。**
