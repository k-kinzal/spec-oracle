# シナリオ仕様と普遍制約：存在要求との違いと検証方法

## 要約

本調査では、シナリオベースの仕様における「存在要求（existential properties）」と「普遍制約（universal properties）」の根本的な違い、および「シナリオは仕様か？」という根源的問いについて、形式手法とソフトウェア工学の歴史的研究を包括的に調査した。主な発見は以下の通り：

1. **シナリオは仕様ではなく、仕様を構築・検証するための手段である**
2. **存在要求と普遍制約は本質的に異なる論理的性質である**（∃ vs ∀）
3. **シナリオは主に存在要求を表現するが、Live Sequence Charts（LSC）などの拡張により普遍制約も表現可能**
4. **E2Eテストやシナリオテストは原理的に普遍制約を完全には保証できない**（有限の実行しか検証できない）
5. **普遍制約の保証にはモデル検査や定理証明などの形式手法が必要**

## 1. 根源的問い：「シナリオは仕様か？」

### 1.1 学術的コンセンサス

ソフトウェア工学の研究において、シナリオと仕様の関係については明確なコンセンサスが存在する：

**シナリオ自体は仕様ではなく、仕様を開発・検証するためのツールである**

文献[[Supporting Scenario-Based Requirements Engineering](https://research.cs.vt.edu/ns/cs5724papers/1.motivatingreuse.tpgap.sutcliffe.scenarios.pdf)]によれば：

> "Rather than being specifications themselves, whereas an abstract model can go unquestioned, unless rigorous automated reasoning is used via formal methods, the detail in scenarios naturally challenges assumptions in models."

シナリオは以下の目的で使用される：
- 要求の具体化と明確化
- ステークホルダー間のコミュニケーション
- 抽象的な仕様の妥当性検証
- 隠れた要求や制約の発見

### 1.2 シナリオと仕様の相補的関係

研究[[Scenario-Based Requirements Engineering](https://www.researchgate.net/publication/4035245_Scenario-Based_Requirements_Engineering)]では、シナリオベースの要求工学において2種類のシナリオが使用されることが示されている：

1. **構造モデル（Structure Models）**: システムコンテキストの構造
2. **使用スクリプト（Usage Scripts）**: システム使用の具体的な流れ

これらは仕様そのものではなく、形式的仕様を構築するための素材として機能する。

### 1.3 シナリオの限界：空虚な充足可能性

文献[[Learning from Vacuously Satisfiable Scenario-Based Specifications](https://www.researchgate.net/publication/262399011_Learning_from_Vacuously_Satisfiable_Scenario-Based_Specifications)]が指摘する重要な問題：

**シナリオは「空虚に満たされる（vacuously satisfiable）」可能性がある**

これは、シナリオのトリガー条件（前提条件）が決して発生しないシステムでも、そのシナリオを技術的には「満たしている」と見なされる問題である。

例：
- シナリオ: 「ユーザーがログインしたら、ホーム画面を表示する」
- 実装: ログイン機能が存在しない
- 結果: トリガーが発生しないため、技術的には満たされている（空虚な充足）

この問題は、シナリオだけでは完全な仕様にならないことを示している。

## 2. 存在要求と普遍制約の根本的な違い

### 2.1 論理的定義

**存在要求（Existential Properties）**: ∃
- 「少なくとも1つの実行パスが存在し、その中で性質Pが成立する」
- 形式的には: ∃σ ∈ Executions. P(σ)
- 可能性（possibility）を表現

**普遍制約（Universal Properties）**: ∀
- 「すべての実行パスにおいて性質Pが成立する」
- 形式的には: ∀σ ∈ Executions. P(σ)
- 必然性（necessity）を表現

### 2.2 ソフトウェア工学における解釈

研究[[Temporal Logic for Scenario-Based Specifications](https://link.springer.com/chapter/10.1007/978-3-540-31980-1_29)]によれば：

**存在的シナリオ（Existential Scenarios）**:
- 「このような振る舞いが可能でなければならない」
- Use Cases、Message Sequence Charts（MSC）の標準的解釈
- システムが「できること」を記述

**普遍的シナリオ（Universal Scenarios）**:
- 「すべての実行においてこの性質が成立しなければならない」
- 安全性制約（Safety Properties）、禁止シナリオ
- システムが「してはいけないこと」を記述

### 2.3 Safety Properties と Liveness Properties

時相論理における標準的な分類[[Model Checking for Linear Temporal Logic](https://ntrs.nasa.gov/api/citations/19910003795/downloads/19910003795.pdf), [Computation tree logic](https://en.wikipedia.org/wiki/Computation_tree_logic)]：

**Safety Properties（安全性）**:
- 「悪いことは決して起こらない」（∀）
- 例: 「デッドロックは発生しない」「不正な状態には遷移しない」
- 反例は有限の実行で示せる

**Liveness Properties（活性）**:
- 「良いことはいつか起こる」（∀∃）
- 例: 「リクエストは必ず処理される」「終了状態に到達する」
- 反例は無限の実行が必要

**重要**: どちらも普遍量化（∀）を含むため、有限のテストでは完全に保証できない。

## 3. シナリオ表記法の進化：存在から普遍へ

### 3.1 Message Sequence Charts (MSC)

[[Message sequence chart](https://en.wikipedia.org/wiki/Message_sequence_chart)]

- ITU-T標準（Z.120）
- 主に**存在的解釈**: 「このような相互作用が可能である」
- 限界: 表現力が弱い、形式的意味論が貧弱
- 部分順序関係（partial ordering）のみをモデル化

### 3.2 Live Sequence Charts (LSC)

[[Live Sequence Charts](https://www.researchgate.net/publication/225384432_Live_Sequence_Charts)]

Damm and Harel（1999）により提案された革新的拡張：

**2つのモダリティ（様相）**:
1. **Existential LSC（存在的）**: 「可能な振る舞い」（dashed lines）
2. **Universal LSC（普遍的）**: 「必須の振る舞い」（solid lines）

**2つの温度（temperature）**:
1. **Cold（冷たい）**: 可能性（may）
2. **Hot（熱い）**: 必然性（must）

この区別により、LSCは以下を表現可能：
- 必須シナリオ（mandatory scenarios）
- 可能シナリオ（possible scenarios）
- 禁止シナリオ（forbidden scenarios）

### 3.3 Play-In と Play-Out

[[LSCs: Breathing Life into Message Sequence Charts](https://link.springer.com/article/10.1023/A:1011227529550)]

Harel and Marelly（2003）が開発した方法論：

**Play-In**:
- GUI操作から直接LSCを生成
- ユーザーが「例」を示すことで仕様を構築
- 存在要求の自然な表現方法

**Play-Out**:
- LSC仕様から実行を生成
- Universal部分（must）: システムが必ず実行
- Existential部分（may）: 成功的完了を監視

この方法論は、存在要求と普遍制約の両方をサポートする。

### 3.4 Use Case Maps (UCM)

[[Use Case Maps as a property specification language](https://link.springer.com/article/10.1007/s10270-007-0076-6)]

- ITU-T User Requirements Notation（URN）の一部
- 因果関係を高レベルで記述
- 振る舞いと構造を明示的にリンク
- 主に存在要求を表現するが、性質仕様言語としても使用可能

## 4. 検証方法の根本的限界

### 4.1 シナリオテストの限界

**原理的限界**:
- シナリオテストは**有限個の実行パス**のみを検証
- 存在要求の検証: ✓ 可能（1つでも成功すれば証明）
- 普遍制約の検証: ✗ 不可能（すべてのパスを検証できない）

数学的に:
- テスト実行集合: T ⊂ Executions（有限部分集合）
- ∃σ ∈ Executions. P(σ) は T で反証可能
- ∀σ ∈ Executions. P(σ) は T では証明不可能

### 4.2 E2Eテストと普遍制約

[[End-to-End (E2E) Testing and Evaluation of High-Assurance Systems](https://link.springer.com/10.1007/978-1-84628-288-1_24)]

**E2Eテストが提供できるもの**:
- 特定のユーザーシナリオの動作確認（存在要求）
- 既知のバグパターンの回帰テスト
- 統合レベルでの振る舞い検証

**E2Eテストが提供できないもの**:
- すべての可能な実行における性質の保証（普遍制約）
- 網羅的な安全性の証明
- 未知の入力組み合わせに対する保証

### 4.3 Property-Based Testing (PBT)

[[Property-based testing](https://www.seas.upenn.edu/~cis1940/fall16/lectures/10-testing.html)]

QuickCheckなどのPBTフレームワーク：

**アプローチ**:
- 普遍性質（universal properties）を記述
- ランダム生成データで多数のテストケースを自動生成
- 形式: `∀x. precondition(x) ⟹ property(x)`

**限界**:
- 依然として有限のテスト実行
- 「反例を見つけられなかった」≠「性質が成立する」
- 統計的信頼性の向上に留まる

**利点**:
- シナリオベーステストより広範な入力空間を探索
- 普遍制約の違反を発見する能力が高い
- ただし証明ではなく高信頼度のテスト

### 4.4 Fuzzing

[[Fuzz4All: Universal Fuzzing with Large Language Models](https://dl.acm.com/doi/10.1145/3597503.3639121)]

最新のファジング技術（2024）:

**特徴**:
- LLMを活用した入力生成
- 多様で現実的な入力の生成
- GCC, Clang, Z3などで98個のバグを発見

**性質ベースファジング**:
- 不変条件（invariants）の検証
- 状態間制約の考慮
- より効果的なテストケース生成

**限界**:
- やはり有限のテスト実行
- 普遍制約の完全な証明は不可能
- ただし網羅性はPBTより高い傾向

## 5. 普遍制約の検証方法

### 5.1 モデル検査（Model Checking）

[[Model checking](https://en.wikipedia.org/wiki/Model_checking)]

**原理**:
- システムの有限状態モデルを構築
- すべての状態と遷移を網羅的に探索
- 時相論理式（LTL, CTL）で性質を記述

**時相論理**:

**Linear Temporal Logic (LTL)**:
- 線形時間：1つの実行パス上で推論
- オペレータ: X（next）, G（globally）, F（finally）, U（until）
- 形式: 線形トレースの性質

**Computation Tree Logic (CTL)**:
- 分岐時間：実行木全体で推論
- パス量化子: A（all paths）, E（exists a path）
- 状態量化子と組み合わせ: AG, EF, AF, EG

**利点**:
- 普遍制約の**完全な証明**が可能
- 反例が自動生成される
- 安全性とライブネスの両方を検証

**限界**:
- 状態爆発問題
- 有限状態モデルのみ
- 実装とモデルの一致性（refinement）が必要

### 5.2 定理証明（Theorem Proving）

無限状態システムや複雑な性質に対して：
- 数学的証明を構築
- Coq, Isabelle/HOLなどの証明支援系
- 完全な保証だが人手が必要

### 5.3 ハイブリッドアプローチ

[[Synthesis from scenario-based specifications](https://www.sciencedirect.com/science/article/pii/S0022000011000870)]

**シナリオから形式仕様へ**:
1. LSCなどのシナリオ仕様を記述
2. 時相論理（CTL*など）に変換
3. モデル検査または合成を実行

**実現可能性（Realizability）**:
- シナリオ要求を満たすコントローラが存在するか判定
- 存在する場合、自動的に生成

このアプローチにより：
- シナリオの直感性
- 形式手法の厳密性
の両方を得られる

## 6. ゴール指向要求工学との関係

### 6.1 KAOS

[[KAOS (software development)](https://en.wikipedia.org/wiki/KAOS_(software_development))]
[[Goal-Oriented Requirements Engineering: An Overview of the Current Research](https://www.cs.utoronto.ca/~alexei/pub/Lapouchnian-Depth.pdf)]

**ゴールの性質**:
- ゴール = 望ましいシステム性質（desired system properties）
- AND/OR分解による精緻化
- ドメイン性質との区別

**シナリオとの関係**:
- シナリオはゴール発見に使用される
- ゴールカバレッジ: ゴールがシナリオをカバーする条件を定義
- 障害（obstacles）分析にシナリオを活用

**存在 vs 普遍**:
- ゴール自体は普遍性質として記述されることが多い
- シナリオは存在的例として機能
- 両者の組み合わせで完全性を追求

### 6.2 i* Framework

[[The i* Framework for Goal-Oriented Modeling](https://link.springer.com/chapter/10.1007/978-3-319-39417-6_22)]

**意図的モデリング（Intentional Modeling）**:
- WHY（なぜ）, WHO（誰が）, HOW（どのように）の次元
- 戦略的依存関係（Strategic Dependency）と戦略的理論（Strategic Rationale）
- アクター、ゴール、タスク、リソース

**シナリオの位置づけ**:
- ゴール発見の潜在的ソース
- 意図的概念を補完する具体例

## 7. BDD (Behavior-Driven Development)

[[Behaviour-Driven Development | Cucumber](https://cucumber.io/docs/bdd/)]

### 7.1 Gherkin言語

**構造**:
```gherkin
Scenario: ユーザーがログインする
  Given ユーザーが登録済みである
  When ログインフォームに正しい認証情報を入力する
  And 「ログイン」ボタンをクリックする
  Then ホーム画面が表示される
```

### 7.2 BDDシナリオの性質

**存在的性質**:
- 各シナリオは1つの実行パスを記述
- Given-When-Then は具体的な例
- テストとして実行される

**普遍制約の欠如**:
- BDDシナリオは普遍量化を表現しない
- 複数のシナリオで「すべての場合」をカバーしようとするが完全ではない
- 組み合わせ爆発の問題

### 7.3 Living Documentation

[[Behaviour-Driven Development | Cucumber](https://cucumber.io/docs/bdd/)]

BDDの利点:
- シナリオが常に最新のドキュメントになる
- 実行可能な仕様
- ステークホルダーとの共通言語

限界:
- あくまで存在要求の検証
- 普遍制約は別の手法が必要

## 8. 実世界における普遍制約の保証戦略

### 8.1 階層的アプローチ

**レイヤーごとの戦略**:

1. **単体テストレベル**:
   - Property-Based Testing（PBT）
   - 関数レベルの不変条件検証
   - 比較的小さな状態空間

2. **統合テストレベル**:
   - コンポーネント間の契約（Contract Testing）
   - 型システムによる静的保証
   - インターフェース仕様

3. **E2Eレベル**:
   - シナリオテスト（存在要求）
   - Fuzzing（網羅的探索）
   - Chaos Engineering（堅牢性）

4. **形式検証レベル**:
   - モデル検査（重要な部分）
   - 定理証明（クリティカルな性質）

### 8.2 現実的ハイブリッド戦略

**段階的厳密化**:

```
低保証 ━━━━━━━━━━━━━━━━━━━━━━━> 高保証
シナリオ → PBT → Fuzzing → モデル検査 → 定理証明
テスト                              形式検証
───────────────────────────────────────
 存在要求        混合         普遍制約
```

**重要度に応じた適用**:
- クリティカルな安全性制約: 形式検証
- 重要なビジネスロジック: PBT + Fuzzing
- 一般的な機能: シナリオテスト + 回帰テスト

### 8.3 型システムと静的解析

**型システムによる普遍保証**:
- 「型安全性」は普遍制約
- すべての実行で型エラーが発生しない
- 静的検証により完全に保証

**静的解析ツール**:
- Null安全性
- データ競合の検出
- リソースリークの防止

これらは限定的だが実用的な普遍制約の保証。

## 9. 「シナリオ主体だと弱い」の本質

### 9.1 論理的根拠

シナリオベースのアプローチが普遍制約に対して「弱い」理由：

1. **表現の限界**:
   - シナリオは具体例（存在）
   - 普遍性は抽象的性質

2. **検証の限界**:
   - 有限のシナリオ実行
   - 無限の可能な実行パス

3. **網羅性の問題**:
   - どれだけシナリオを書いても完全性の保証なし
   - 組み合わせ爆発

4. **空虚な充足**:
   - トリガー条件の検証が不十分
   - 実際には制約していない可能性

### 9.2 補完的アプローチ

**シナリオと性質の組み合わせ**:

[[Property-Driven Scenario Integration](https://ieeexplore.ieee.org/document/5368100/)]

- シナリオを性質に違反しない形で統合
- 性質が統合プロセスを導く
- シナリオが性質の具体例を提供

**完全性への道**:

[[Towards a Completeness Argumentation for Scenario Concepts](https://arxiv.org/html/2404.01934v1)]

- トップダウン分解と シナリオベース の統合
- 機能的抽象化で完全なカバレッジ
- シナリオで不明瞭な記述を明確化

## 10. 結論と実践的示唆

### 10.1 根源的問いへの答え

**「シナリオは仕様か？」**

**答え: No、ただし重要な役割を持つ**

シナリオは：
- 仕様を構築するためのツール
- 仕様を検証するための手段
- ステークホルダーとのコミュニケーション媒体
- 仕様そのものではない

### 10.2 存在要求 vs 普遍制約

| 観点 | 存在要求（∃） | 普遍制約（∀） |
|------|--------------|--------------|
| 意味 | 少なくとも1つのパスで成立 | すべてのパスで成立 |
| シナリオでの表現 | 自然（標準的MSC, Use Cases） | 困難（LSCで可能） |
| テストでの検証 | 可能（1例で証明） | 不可能（完全には） |
| 形式検証での検証 | 容易 | 可能だが複雑 |
| 実用的重要性 | 機能の存在確認 | 安全性・堅牢性 |

### 10.3 「普遍制約は検証不可能では？」への答え

**部分的にYes、戦略的にNo**

- **テストでは不可能**: E2E、シナリオテスト、PBT、Fuzzingすべて有限
- **形式手法では可能**: モデル検査、定理証明で完全な保証
- **実践的アプローチ**: 階層的・ハイブリッド戦略

### 10.4 実践的推奨事項

1. **シナリオの役割を理解する**:
   - 存在要求の検証
   - コミュニケーションツール
   - 完全な仕様ではない

2. **普遍制約には別アプローチ**:
   - 重要な性質は形式手法
   - 型システムの活用
   - 静的解析ツール

3. **階層的保証戦略**:
   - レイヤーごとに適切な手法
   - クリティカリティに応じた投資

4. **補完的使用**:
   - シナリオ + 性質仕様
   - 具体例 + 抽象的制約
   - テスト + 形式検証

### 10.5 研究フロンティア

**現在進行中の研究方向**:

1. **LLMベースの検証**:
   - Fuzz4All（2024）のような自動テスト生成
   - より広範な入力空間の探索

2. **シナリオ合成**:
   - 時相論理からシナリオを自動生成
   - 実現可能性の自動判定

3. **ハイブリッド検証**:
   - テストとモデル検査の統合
   - 統計的モデル検査

4. **実用的形式手法**:
   - 軽量な形式手法（Lightweight Formal Methods）
   - ツールの使いやすさ向上

## 参考文献

### シナリオベース要求工学
- [Supporting Scenario-Based Requirements Engineering](https://research.cs.vt.edu/ns/cs5724papers/1.motivatingreuse.tpgap.sutcliffe.scenarios.pdf)
- [Scenario-Based Requirements Engineering](https://www.researchgate.net/publication/4035245_Scenario-Based_Requirements_Engineering)
- [Scenario-based requirements engineering](https://ieeexplore.ieee.org/document/1232776/)
- [Learning from Vacuously Satisfiable Scenario-Based Specifications](https://www.researchgate.net/publication/262399011_Learning_from_Vacuously_Satisfiable_Scenario-Based_Specifications)

### シナリオ表記法
- [Message sequence chart - Wikipedia](https://en.wikipedia.org/wiki/Message_sequence_chart)
- [Message Sequence Charts (MSC)](https://portal.etsi.org/CTI/ApproachToTesting/SpecLanguages/MSC.htm)
- [Live Sequence Charts](https://www.researchgate.net/publication/225384432_Live_Sequence_Charts)
- [LSCs: Breathing Life into Message Sequence Charts](https://link.springer.com/article/10.1023/A:1011227529550)
- [Live sequence charts - WeizmannWiki](https://wiki.weizmann.ac.il/playgo/index.php/Live_sequence_charts)
- [Use Case Maps as a property specification language](https://link.springer.com/article/10.1007/s10270-007-0076-6)

### 形式手法とモデル検査
- [Model checking - Wikipedia](https://en.wikipedia.org/wiki/Model_checking)
- [Computation tree logic - Wikipedia](https://en.wikipedia.org/wiki/Computation_tree_logic)
- [Model Checking for Linear Temporal Logic](https://ntrs.nasa.gov/api/citations/19910003795/downloads/19910003795.pdf)
- [Temporal Logic for Scenario-Based Specifications](https://link.springer.com/chapter/10.1007/978-3-540-31980-1_29)
- [Synthesis from scenario-based specifications](https://www.sciencedirect.com/science/article/pii/S0022000011000870)

### テスティング手法
- [Property-based testing](https://www.seas.upenn.edu/~cis1940/fall16/lectures/10-testing.html)
- [Property-based Testing With QuickCheck](https://typeable.io/blog/2021-08-09-pbt.html)
- [End-to-End (E2E) Testing and Evaluation of High-Assurance Systems](https://link.springer.com/10.1007/978-1-84628-288-1_24)
- [Fuzz4All: Universal Fuzzing with Large Language Models](https://dl.acm.com/doi/10.1145/3597503.3639121)

### ゴール指向要求工学
- [KAOS (software development) - Wikipedia](https://en.wikipedia.org/wiki/KAOS_(software_development))
- [Goal-Oriented Requirements Engineering: An Overview of the Current Research](https://www.cs.utoronto.ca/~alexei/pub/Lapouchnian-Depth.pdf)
- [The i* Framework for Goal-Oriented Modeling](https://link.springer.com/chapter/10.1007/978-3-319-39417-6_22)

### BDD
- [Behaviour-Driven Development | Cucumber](https://cucumber.io/docs/bdd/)
- [Behavior-driven development - Wikipedia](https://en.wikipedia.org/wiki/Behavior-driven_development)
- [Gherkin, BDD, & Cucumber: Behaviour Driven Development Guide](https://testquality.com/gherkin-bdd-cucumber-guide-to-behavior-driven-development/)

### 統合と完全性
- [Property-Driven Scenario Integration](https://ieeexplore.ieee.org/document/5368100/)
- [Towards a Completeness Argumentation for Scenario Concepts](https://arxiv.org/html/2404.01934v1)
- [Integrating Top-Down and Scenario-Based Methods for Constructing Software Specifications](https://ieeexplore.ieee.org/document/4601533/)

---

**調査者**: researcher-09
**調査日**: 2026-02-14
**ステータス**: 完了
