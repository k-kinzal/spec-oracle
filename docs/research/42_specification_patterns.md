# 仕様パターン（Specification Patterns）

## 調査目的

本調査では、仕様パターン（Specification Patterns）について調査する。特に、Dwyer/Avrunin/Corbettの仕様パターンシステム、応答パターン（Response）、存在パターン（Existence）、普遍パターン（Universality）、先行パターン（Precedence）等、パターンと時相論理の対応、パターンベースの仕様記述の実用性、仕様パターンカタログについて詳述する。

## 1. 仕様パターンの起源と動機

### 1.1 歴史的背景

**開発者**：
Matthew B. Dwyer、George S. Avrunin、James C. Corbett

**発表**：
1998年3月、第2回 Workshop on Formal Methods in Software Practice（FMSP '98）において「Property Specification Patterns for Finite-state Verification」を発表。

### 1.2 動機と問題意識

**形式手法の採用障壁**：
形式手法を実務で採用する上での主要な課題は、実務者が仕様プロセス、記法、戦略に不慣れであることである。

**具体的な課題**：
1. **専門知識の必要性**：
   - 時相論理（LTL、CTLなど）の理解が必要
   - 非専門家にとって形式仕様言語は難解

2. **記述の難しさ**：
   - 要求を形式仕様に翻訳する労力と専門知識
   - 検証可能な性質への要件の形式化

3. **ツールの使用障壁**：
   - モデル検査ツール（SPIN、SMVなど）が対応する性質言語を非専門家が使いこなすのは困難

### 1.3 仕様パターンの目的

**パターンベースのアプローチ**：
仕様パターンシステムは、非形式的な要求を有限状態検証のための形式仕様に翻訳することを容易にする。

**主要な目標**：
1. **学習支援**：アナリストと開発者が形式言語で要求と仕様を表現するための訓練と指導
2. **時間短縮**：仕様作成に必要な時間を短縮
3. **理解可能性向上**：共通のよく知られた設計パターンを参照することで、仕様をより理解しやすくする
4. **再利用性**：典型的な要求の形式化を再利用可能なパターンとして提供

**実証結果**：
経験から、非専門家はパターンベースのアプローチを使用して形式仕様を書くことを迅速に学習できることが示されている。

## 2. 仕様パターンシステムの構造

### 2.1 調査に基づく設計

**方法論**：
Dwyerらは、有限状態検証ツール（SPINやSMVなど）が対応する仕様形式主義を人々がどのように使用するかの調査を実施した。

**成果**：
多数の典型的な仕様を分析して、要件と仕様における典型的な繰り返し出現する形式構造を抽出し、パターンを特定した。

### 2.2 パターンの二つの側面

仕様パターンは、振る舞いの2つの側面を特徴付ける：

1. **発生（Occurrence）**：イベントや条件の出現
2. **順序（Order）**：イベントや条件の順序

### 2.3 パターンの分類

#### 2.3.1 発生パターン（Occurrence Patterns）

**普遍性（Universality）**：
- 定義：すべての実行点で性質Pが真である
- 形式：Universality(P)
- 意味：「Pは常に真である」

**不在（Absence）**：
- 定義：実行のどの点でも性質Pが真にならない
- 形式：Absence(P)
- 意味：「Pは決して真にならない」

**存在（Existence）**：
- 定義：実行のある点で性質Pが真である
- 形式：Existence(P)
- 意味：「Pはいつか真になる」

**有界存在（Bounded Existence）**：
- 定義：性質Pが真になる回数に制約がある
- 形式：BoundedExistence(P, k)
- 意味：「Pは最大k回真になる」

#### 2.3.2 順序パターン（Order Patterns）

**先行（Precedence）**：
- 定義：Pが真になる場合、その前にQが真になっていなければならない
- 形式：Precedence(P, Q)
- 意味：「原因Qがそれぞれの結果Pに先行する」

**応答（Response）**：
- 定義：Pが真になる場合、その後でQが真になる
- 形式：Response(P, Q)
- 意味：「原因Pの後に結果Qが続く」

**先行の連鎖（Chain of Precedence）**：
- 定義：複数の性質の先行関係の連鎖
- 複雑な因果関係の表現

**応答の連鎖（Chain of Response）**：
- 定義：複数の性質の応答関係の連鎖
- 複雑な反応シーケンスの表現

### 2.4 ResponseとPrecedenceの違い

**重要な非等価性**：
ResponseとPrecedenceは等価ではない。

**Precedence**：
- 各結果の前に原因が存在することを要求
- 原因が結果なしに発生することは許容

**Response**：
- 各原因の後に結果が発生することを要求
- 結果が原因なしに発生することは許容

**例**：
```
Response(P, Q): P → ◇Q
  Pが真なら、将来のある時点でQが真になる
  （Qが原因なしに真になることは許容される）

Precedence(P, Q): P → (Q Since true)
  Pが真なら、過去のある時点でQが真であった
  （Qが結果なしに真になることは許容される）
```

## 3. スコープと時間的文脈

### 3.1 スコープの概念

仕様パターンは、性質が適用される実行の範囲（スコープ）を明示的に指定できる。

**スコープの種類**：

1. **大域（Global）**：
   - 実行全体にわたって性質が適用される
   - 形式：Global P

2. **Q前（Before Q）**：
   - 実行の開始からQが真になる最初の時点まで
   - 形式：Before Q, P

3. **Q後（After Q）**：
   - Qが真になった後から実行の終わりまで
   - 形式：After Q, P

4. **Q〜R間（Between Q and R）**：
   - Qが真になってからRが真になるまでの間
   - 形式：Between Q and R, P

5. **Q〜Rの後（After Q until R）**：
   - Qが真になった後、Rが真になるまで（Rは必須でない）
   - 形式：After Q until R, P

### 3.2 スコープの形式的定義

**LTL（Linear Temporal Logic）での表現例**：

```
Global: □P
Before Q: (¬Q) W (Q ∧ P)
After Q: □(Q → □P)
Between Q and R: □((Q ∧ ¬R ∧ ◇R) → (P U R))
After Q until R: □(Q → ((P W R) ∨ □P))
```

### 3.3 スコープの実用的意義

**柔軟性の向上**：
スコープを明示することで、性質が適用される文脈を正確に制御できる。

**例**：
- 「システム初期化後、リソースは常に解放される」
  - After Initialization, Always(ResourceReleased)
- 「ログイン〜ログアウト間、セッションは有効である」
  - Between Login and Logout, Always(SessionValid)

## 4. 時相論理との対応

### 4.1 LTL（Linear Temporal Logic）への写像

**基本演算子**：
- □（Box）：常に（Always）
- ◇（Diamond）：いつか（Eventually）
- X（Next）：次の状態で
- U（Until）：〜まで
- W（Weak Until）：〜まで（到達しない場合も許容）

**パターンのLTL表現例**：

```
Universality(P): □P
Existence(P): ◇P
Absence(P): □¬P
Response(P, Q): □(P → ◇Q)
Precedence(Q, P): □(P → (Q Since true))
```

### 4.2 CTL（Computational Tree Logic）への写像

**パスクオンティファイア**：
- A（All paths）：すべてのパス上で
- E（Exists path）：あるパス上で

**基本演算子**：
- AG：すべてのパス上で常に
- EG：あるパス上で常に
- AF：すべてのパス上でいつか
- EF：あるパス上でいつか
- AX：すべての次状態で
- EX：ある次状態で

**パターンのCTL表現例**：

```
Universality(P): AG P
Existence(P): EF P
Absence(P): AG ¬P
Response(P, Q): AG(P → AF Q)
```

### 4.3 論理間の表現可能性

**表現力の違い**：
すべてのパターンがすべての論理に翻訳できるわけではない。

**例**：
- 「可能な有界不変性（Possible Bounded Invariance）パターン」はLTLやCTLでは表現できない
- より表現力の高い論理（CTL*、μ-calculusなど）が必要な場合がある

**実用的考慮**：
パターンシステムは、各論理の表現力に応じて翻訳可能なパターンのサブセットを提供する。

## 5. リアルタイム仕様パターン

### 5.1 拡張の動機

**限界**：
Dwyerらの元のパターン（1999年）は定性的な時相性質に焦点を当てており、定量的な時間制約を直接表現できなかった。

**需要**：
リアルタイムシステムでは、「イベントAの後、3秒以内にイベントBが発生する」といった定量的制約が重要。

### 5.2 Konrad & Chengの拡張

**提案**：
Konrad and Cheng（2005年）が、定量的時間制約を含むリアルタイム仕様パターンを提案。

**特徴**：
- 時間境界の明示的指定
- タイミング制約の柔軟な表現
- TCTL（Timed CTL）やTLTL（Timed LTL）への写像

**例**：
```
TimedResponse(P, Q, [a, b]):
  Pが真になったら、a時間単位後からb時間単位後までの間にQが真になる
```

### 5.3 TILCO-Xによる時間パターンの組織化

**TILCO-X**：
リアルタイム仕様パターンを時相論理で表現し、組織化するためのフレームワーク。

**利点**：
- パターンの体系的分類
- 複雑な時間制約の合成
- ツールサポートによる自動翻訳

### 5.4 UPPAALとの統合

**UPPAAL**：
時間オートマトンのモデル検査ツール。

**リアルタイムパターンカタログ**：
リアルタイムシステム検証のためのUPPAAL向け性質仕様パターンカタログが開発された。

**特徴**：
- パターンベースの性質指定（時相論理を使用せずに）
- オブザーバオートマトンへの自動翻訳
- 検証式の自動生成

**実用的利点**：
実務者はパターンベースの方法で性質を指定でき、対応するオブザーバオートマトンと検証式を自動生成できる。

## 6. パターンカタログとリポジトリ

### 6.1 仕様パターンリポジトリ

**目的**：
並行・反応システムの仕様において一般的に出現するパターンを収集。

**構成**：
- パターンの説明
- よく理解されたシステム振る舞いの概念を、共通の形式仕様言語における正確な記述に写像する方法の図解
- 複数の形式主義（LTL、CTL、RTCTL、XMLなど）での表現

**アクセス**：
オンラインカタログとして公開（https://matthewbdwyer.github.io/psp/patterns/）

### 6.2 パターンの構成要素

各パターンは以下の情報を含む：

1. **名前と意図**：パターンの目的の簡潔な記述
2. **動機**：パターンが有用な状況の説明
3. **構造**：パターンの構文構造
4. **例**：具体的な使用例
5. **関連パターン**：他のパターンとの関係
6. **形式化**：
   - LTL、CTL、その他の論理での正確な定義
   - スコープごとの変種
7. **注意事項**：パターン使用時の注意点

### 6.3 パターン間の関係

**階層構造**：
- 単純なパターンから複雑なパターンへの階層
- パターンの合成による複雑な性質の構築

**組み合わせ**：
複数のパターンを論理演算子（∧、∨、¬など）で組み合わせることで、より複雑な要求を表現可能。

**例**：
```
(Response(P, Q) ∧ Precedence(Q, R)) の Before S スコープ
  →「Sが真になる前、PならばQが続き、Qの前にはRが存在する」
```

## 7. 実用性とツールサポート

### 7.1 パターンベース仕様言語

**PROPOLS**：
Property Pattern-based Specification Language

**特徴**：
- Dwyerらの性質パターンシステムに基づく
- 理解しやすく使いやすい
- 形式的基盤を持つ
- パターンの論理的合成により複雑な要求に対応

**拡張性**：
複雑な要求を扱うために、パターンの論理的合成をサポート。

### 7.2 自動翻訳ツール

**機能**：
1. パターンベースの仕様を時相論理式に自動変換
2. オブザーバオートマトンの自動生成
3. モデル検査ツール（SPIN、SMV、UPPAALなど）向けの検証式生成

**利点**：
- 非専門家でも形式検証を利用可能
- 翻訳ミスのリスク低減
- 検証プロセスの効率化

### 7.3 視覚的仕様言語

**動機**：
テキストベースのパターン言語でも、非専門家にとっては障壁となる場合がある。

**アプローチ**：
- グラフィカルなパターン選択インターフェース
- ビジュアルプログラミング環境
- ドラッグ&ドロップによるパターン組み合わせ

**評価**：
実際のモデル検査経験に基づく視覚的性質仕様言語の評価が行われている（2024年の研究）。

### 7.4 サービス合成への応用

**問題**：
Webサービス合成におけるサービス間の相互作用の検証。

**解決策**：
パターンベースの性質仕様と検証をサービス合成に適用。

**利点**：
- サービスの振る舞い制約の形式化
- 合成されたサービスの自動検証
- サービス契約の明確化

## 8. 実用経験と学習曲線

### 8.1 学習の容易さ

**実証データ**：
経験から、非専門家はパターンベースのアプローチを使用して形式仕様を書くことを迅速に学習できることが示されている。

**要因**：
1. **既知の概念への写像**：パターンは共通のシステム振る舞いに対応
2. **抽象化レベル**：時相論理の詳細から隔離
3. **具体例の提供**：各パターンに理解を助ける例が付属

### 8.2 産業での採用

**課題**：
モデル検査技術の産業での採用を制限する問題の一つは、非専門家が検証ツールが対応する性質言語を使用して要求を表現する能力である。

**パターンによる解決**：
- 専門知識の民主化
- 形式手法への参入障壁の低減
- 組織内での形式検証の普及促進

**成功事例**：
- 航空宇宙産業での使用
- 組み込みシステム開発
- クリティカルシステムの検証

### 8.3 仕様時間の短縮

**効果**：
パターンを使用することで、仕様作成に必要な時間が大幅に短縮される。

**理由**：
1. **再利用**：よくあるパターンを一から記述する必要がない
2. **エラーの減少**：検証済みのパターンを使用することで、仕様の誤りが減る
3. **レビューの容易さ**：パターンベースの仕様は理解しやすく、レビューが効率的

## 9. パターンの限界と拡張

### 9.1 表現力の限界

**カバーできない性質**：
すべての性質がパターンで表現できるわけではない。

**対処法**：
1. **カスタムパターンの追加**：組織固有のパターンをカタログに追加
2. **低レベル論理への退化**：必要に応じて直接時相論理を使用
3. **パターンの合成**：複数パターンの組み合わせで複雑な性質を表現

### 9.2 ドメイン特化パターン

**需要**：
特定のドメイン（リアルタイム、セキュリティ、分散システムなど）に特化したパターンの需要。

**アプローチ**：
- ドメイン特化パターンライブラリの開発
- 既存パターンのドメイン特化拡張
- ドメインエキスパートとの協働によるパターン抽出

**例**：
- **セキュリティパターン**：機密性、完全性、可用性の性質
- **リアルタイムパターン**：タイミング制約、周期性
- **分散システムパターン**：因果順序、一貫性、合意

### 9.3 確率的パターン

**動機**：
確率的システム（通信プロトコル、ランダム化アルゴリズムなど）の仕様。

**拡張**：
確率的時相論理（PCTL、ProbLTLなど）へのパターンの拡張。

**例**：
```
ProbabilisticResponse(P, Q, p):
  Pが真になったら、確率p以上でQがいつか真になる
```

## 10. パターンと他の仕様技術の関係

### 10.1 シナリオベース仕様

**統合**：
パターンとシナリオベースの仕様（MSC、UMLシーケンス図など）の統合。

**利点**：
- シナリオから自動的にパターンを抽出
- パターンを使ったシナリオの検証

### 10.2 ゴール指向要求工学

**関係**：
ゴール（目標）を達成するための手段としての性質をパターンで表現。

**KAOS**：
KAOS（Knowledge Acquisition in autOmated Specification）フレームワークでは、ゴールを時相論理で形式化し、パターンと組み合わせることができる。

### 10.3 契約プログラミング

**事前条件・事後条件との対応**：
- Precedenceパターン ≈ 事前条件
- Responseパターン ≈ 事後条件
- Universalityパターン ≈ 不変条件

**Design by Contract**：
Eiffelなどの契約プログラミング言語の契約をパターンで表現し、モデル検査で検証。

## 11. まとめと展望

### 11.1 仕様パターンの貢献

**形式手法の実用化**：
仕様パターンは、形式手法を非専門家に accessible にする上で重要な役割を果たしてきた。

**主要な貢献**：
1. **学習曲線の緩和**：時相論理の詳細を隠蔽
2. **再利用性の向上**：共通の性質を再利用可能な形で提供
3. **コミュニケーション改善**：パターン名による性質の簡潔な伝達
4. **エラー削減**：検証済みパターンの使用による仕様誤りの削減
5. **ツールサポート**：自動翻訳ツールによる検証プロセスの効率化

### 11.2 現在の課題

**カバレッジ**：
現在のパターンカタログは多くの一般的な性質をカバーしているが、すべてではない。

**ドメイン特化**：
より多くのドメイン特化パターンの開発が必要。

**複雑性の管理**：
パターンの合成による複雑な性質の表現は、依然として課題。

**ツールの統合**：
既存の開発ツールチェーンとの統合の改善。

### 11.3 今後の方向性

**AI/MLとの統合**：
機械学習による以下の可能性：
- ソースコードやドキュメントから自動的なパターン推薦
- 自然言語要求からパターンへの自動変換
- 新しいパターンの自動発見

**ビッグデータ解析**：
大規模なコードリポジトリから新しいパターンをマイニング。

**形式合成**：
パターンから実装を自動合成する技術の発展。

**量子計算への拡張**：
量子システムの性質を表現するための量子仕様パターン。

### 11.4 結論

仕様パターンは、Dwyer、Avrunin、Corbettによって1998年に導入されて以来、形式検証の分野において重要なツールとなっている。パターンベースのアプローチにより、非専門家でも形式仕様を書くことができるようになり、形式手法の産業応用が促進された。

リアルタイム制約の追加、ドメイン特化パターンの開発、視覚的仕様言語の統合など、継続的な拡張により、パターンの適用範囲は広がり続けている。自動翻訳ツールのサポートにより、パターンベースの仕様から時相論理式やオブザーバオートマトンを生成することができ、モデル検査ツールとのシームレスな統合が実現している。

今後、AI/MLとの統合、新しいドメインへの拡張、そしてより高度な合成技術の発展により、仕様パターンの重要性はさらに増すと考えられる。形式手法の普及と実用化において、仕様パターンは中心的な役割を果たし続けるであろう。

## 参考文献

### 仕様パターンの基礎文献

- [Patterns in property specifications for finite-state verification - Semantic Scholar](https://www.semanticscholar.org/paper/Patterns-in-property-specifications-for-Dwyer-Avrunin/413baeab46e0056849585cac687a86bf9fe00b54)
- [A Specification Pattern System - Dwyer et al.](https://people.cs.ksu.edu/~dwyer/spec-patterns.ORIGINAL)
- [Property specification patterns for finite-state verification - FMSP '98](https://dl.acm.org/doi/10.1145/298595.298598)
- [Property Specification Patterns for Finite-State Verification - ResearchGate](https://www.researchgate.net/publication/2593589_Property_Specification_Patterns_for_Finite-State_Verification)
- [Patterns in property specifications for finite-state verification - ICSE '99](https://dl.acm.org/doi/10.1145/302405.302672)

### リアルタイム仕様パターン

- [Expressing and organizing real-time specification patterns via temporal logics - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0164121208001763)
- [Real-time specification patterns - ICSE 2005](https://dl.acm.org/doi/10.1145/1062455.1062526)
- [Real-Time Specification Patterns and Tools - HAL](https://hal.science/hal-00782649/document)
- [Specification patterns for time-related properties - Gruhn & Laue](https://files01.core.ac.uk/download/pdf/226137591.pdf)
- [Patterns for Timed Property Specifications - ResearchGate](https://www.researchgate.net/publication/222308319_Patterns_for_Timed_Property_Specifications)

### パターンカタログとツール

- [Property Specification Patterns - Online Repository](https://matthewbdwyer.github.io/psp/patterns/)
- [Specification Patterns Relationships - Wiki](http://ps-patterns.wikidot.com/)
- [Precedence Property Pattern](https://matthewbdwyer.github.io/psp/patterns/precedence.html)
- [A property specification pattern catalog for real-time system verification with UPPAAL - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0950584922002099)

### 実用性と応用

- [Pattern Based Property Specification and Verification for Service Composition - Springer](https://link.springer.com/chapter/10.1007/11912873_18)
- [Evaluation of visual property specification languages based on practical model-checking experience - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0164121224001985)
- [A Property Specification Tool for Generating Formal... - PDF](https://www.cs.utep.edu/isalamah/publications/C21.pdf)
- [Generating Linear Temporal Logic Formulas for Pattern-Based Specifications - PDF](https://www.cs.utep.edu/isalamah/publications/C28.pdf)

### 時相論理との対応

- [Linear temporal logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_temporal_logic)
- [Computation tree logic - Wikipedia](https://en.wikipedia.org/wiki/Computation_tree_logic)
- [CTL* - Wikipedia](https://en.wikipedia.org/wiki/CTL*)
- [Specification and Verification using Temporal Logics - Inria](https://inria.hal.science/hal-00776601v1/document)

---

**調査実施日**: 2026-02-14
**調査者**: researcher-06
