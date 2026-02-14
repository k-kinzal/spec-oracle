# 仕様の進化と適応（Specification Evolution）

## 1. はじめに

ソフトウェアは継続的に変化し進化する。その過程で、仕様もまた変化し適応しなければならない。本調査では、仕様の進化と適応に関する理論と実践を包括的に調査する。

---

## 2. 仕様の変更・成長パターン

### 2.1 進化パターンの分類

仕様の進化には、観察可能なパターンが存在する。

**共進化パターン（Co-evolution Patterns）**:
> 要求仕様とアーキテクチャ設計のような、絡み合った成果物のペア間で共進化（または変更パターン）を観察できる。

**進化スタイル（Evolution Styles）**:
- 一度仕様化され、多数回適用できる第一級エンティティとして定義される
- 仕様進化の管理における再利用性を促進

参考文献:
- [Evolution styles: change patterns for Software Evolution](https://www.researchgate.net/publication/238743879_Evolution_styles_change_patterns_for_Software_Evolution)
- [Change patterns | Software and Systems Modeling](https://link.springer.com/article/10.1007/s10270-012-0276-6)

### 2.2 ソフトウェア進化のプロセス

**基本的な活動**:
1. **変更分析**: 変更の影響とコストの評価
2. **リリース計画**: 変更のスケジューリング
3. **システム実装**: 変更の実施
4. **リリース**: 顧客へのシステム提供

**変更管理の段階**:
- 仕様定義: ソフトウェア仕様を定義し、将来の潜在的変更を特定
- 影響評価: 変更がシステムにどの程度影響を与えるか、実装コストの評価

参考文献:
- [Software Evolution - GeeksforGeeks](https://www.geeksforgeeks.org/software-engineering/software-engineering-software-evolution/)
- [Software Change Management: Best Practices & Tools for 2026](https://www.superblocks.com/blog/software-change-management)

### 2.3 パターン駆動の変更管理

**継続的な自動パターン識別**:
- アーキテクチャ変更ログからの進化パターンの自動識別
- パターンライブラリによるパターン仕様とインスタンス化のサポート
- 仕様進化管理におけるより体系的で再利用可能なアプローチ

参考文献:
- [Pat-Evol: Pattern-Driven Reuse in Architecture-Based Evolution](https://ercim-news.ercim.eu/en88/special/pat-evol-pattern-driven-reuse-in-architecture-based-evolution-for-service-software)

---

## 3. 仕様の腐敗（Specification Decay）

### 3.1 ソフトウェア老化とは

**ソフトウェア老化（Software Aging）**:
> ソフトウェアが一定時間連続して実行された後、または周辺システムの継続的な変更により、失敗またはシステム障害を引き起こす傾向。

**原因**:
1. 古いソフトウェアが変化するニーズや技術プラットフォームに適応できないこと
2. ソフトウェアパッチがさらなるエラーを導入する傾向

参考文献:
- [Software aging - Wikipedia](https://en.wikipedia.org/wiki/Software_aging)
- [Software Aging - David Lorge Parnas](https://www.cs.drexel.edu/~yc349/CS451/RequiredReadings/SoftwareAging.pdf)

### 3.2 老化による腐敗（Aging Decay）

**定義**:
> 新しい機能/要求、技術、または環境への更新と適応の失敗による、ソフトウェアの段階的劣化。

**結果**:
- ソフトウェアが時代遅れになり、関連性が低下
- 現行標準との非互換性
- 保守または現代技術との統合が非効率に

参考文献:
- [Why and How Software Systems decay](https://towardsdatascience.com/why-and-how-software-systems-decay-fa7ec83c4ff3/)
- [Detection, Classification and Prevalence of Self-Admitted Aging Debt](https://arxiv.org/html/2504.17428v1)

### 3.3 進化による腐敗

**エントロピーの増加**:

Lehmanのソフトウェア進化の法則では、複雑なソフトウェアシステムは周囲の環境との関連性を維持するために継続的な修正が必要であり、エントロピーを減らすための特定の作業が行われない限り、そのような修正はシステムのエントロピーを増加させると述べている。

**進化プロセスの影響**:
> 多くのソフトウェアは新しい要求を満たし、バグを修正するために継続的な変更が必要である。これはプログラムの本質的に進化プロセスを作り出し、元のエンジニアリング設計から逸脱させる。

参考文献:
- [Programs, Life Cycles, and Laws of Software Evolution](https://users.ece.utexas.edu/~perry/education/SE-Intro/lehman.pdf)
- [Architectural Decay during Continuous Software Evolution](https://link.springer.com/chapter/10.1007/978-3-642-10619-4_15)

### 3.4 コード寿命の分析

**研究結果**:
- コード行は耐久性があり、寿命の中央値は約2.4年
- 若いコード行は修正または削除される可能性が高い
- ワイブル分布に従い、関連するハザード率は時間とともに減少

参考文献:
- [Software evolution: the lifetime of fine-grained elements](https://peerj.com/articles/cs-372.pdf)

---

## 4. 自己適応システムの仕様

### 4.1 MAPE-Kループ

**概要**:

MAPE-K（Monitor-Analyze-Plan-Execute over a shared Knowledge）フィードバックループは、自律的および自己適応システムのための最も影響力のある参照制御モデルである。

**構成要素**:
- **Monitor（監視）**: システムと環境の監視
- **Analyze（分析）**: 適応の必要性の特定
- **Plan（計画）**: 適応戦略の策定
- **Execute（実行）**: 適応の実施
- **Knowledge（知識）**: 共有知識ベース

参考文献:
- [Modeling and Analyzing MAPE-K Feedback Loops for Self-Adaptation](https://ieeexplore.ieee.org/document/7194653/)
- [MAPE-K reference model for self-adaptive systems](https://www.researchgate.net/figure/MAPE-K-reference-model-for-self-adaptive-systems-from-102_fig2_266646263)

### 4.2 自己適応の必然性

**ロボティクスにおける重要性**:
> 自律ロボットが外部制御なしに長期間にわたって現実世界の環境で動作できるようになるためには、自律ロボットがコンテキストを監視し、認識された変化に対して動作を自己適応できることが必須である。

参考文献:
- [On Managing Knowledge for MAPE-K Loops in Self-Adaptive Robotics](https://www.mdpi.com/2076-3417/12/17/8583)

---

## 5. @runtime models（ランタイムモデル）

### 5.1 概念

**ランタイムモデルの役割**:

自己適応ソフトウェアのためのランタイムモデル（MORISIA）は、フィードバックループで自己適応を可能にするために使用されるモデルの役割を調査し、外部アプローチ、MAPE-K、ランタイムモデルの概念に従うモデル駆動フレームワークを生み出す。

**モデルの種類**:
1. **Reflection Models（反映モデル）**: 適応可能なソフトウェアとその環境を反映
2. **Monitoring Models（監視モデル）**: システムレベルの観測を反映モデルの抽象レベルにマッピング
3. **Evaluation Models（評価モデル）**: 反映モデルに対する制約を定義し、適応の必要性を識別

参考文献:
- [Models at Runtime for Self-Adaptive Software | MDELab](https://www.hpi.uni-potsdam.de/giese/public/mdelab/mdelab-projects/software-engineering-for-self-adaptive-systems/morisia/)
- [Using Models at Runtime to Address Assurance for Self-Adaptive Systems](https://arxiv.org/pdf/1505.00903)

### 5.2 因果接続

**ランタイムモデルの特徴**:
- 実行中のシステムと因果的に接続されたモデル
- 異なる機能的および非機能的関心に関して実行中のシステムを反映
- システムの環境を反映
- 適応ステップ（監視、分析、計画、実行）を仕様化

参考文献:
- [Runtime Software Architectural Models for Adaptation, Recovery and Evolution](https://ceur-ws.org/Vol-2019/mrt_3.pdf)

---

## 6. 動的仕様変更

### 6.1 動的適応の階層

**動的適応の特徴付け**:
> 動的適応は、具体的なアプリケーションにおける可変性に対処するメタレベル能力として特徴付けられる。その論理はアプリケーション論理とは異なり、ランタイムモデルの管理と適応論理に従ったシステム動作の制御を担当する適応メカニズムを通じて実装される。

**アーキテクチャの階層化**:
1. **基本システム層**: アプリケーション論理を実装
2. **適応メカニズム層**: 適応論理を実装

この分離により、関心事の明確な境界を定めることで、体系的な能力モデリングと効果的な複雑性制御が可能になる。

参考文献:
- [Dynamic Adaptation - an overview | ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/dynamic-adaptation)

### 6.2 動的進化の種類

**ソフトウェアアーキテクチャにおける進化可能性の分類**:

1. **動的再構成（Dynamic Reconfiguration）**:
   - アーキテクチャ要素インスタンスとそのリンクを動的に作成または破棄
   - 実行時に構成を変更

2. **動的アーキテクチャ型進化（Dynamic Architectural Type Evolution）**:
   - 実行時に仕様全体を完全に変更
   - 新しいアーキテクチャ要素タイプと接続を導入
   - アーキテクチャ要素の型と実行中のインスタンスを修正

参考文献:
- [Managing Dynamic Evolution of Architectural Types](https://link.springer.com/chapter/10.1007/978-3-540-88030-1_22)

### 6.3 ランタイム適合性の維持

**課題**:
> 要求、環境、システム間の適合関係を実行時に維持するには、システムが変更を検出し、可能な限りスムーズかつ迅速に適応する必要がある。要求または環境コンテキストが予測不可能に進化する場合、これは困難になる可能性がある。

参考文献:
- [Software Reconfiguration Patterns for Dynamic Evolution of Software](https://cse.msu.edu/~chengb/CSE891/Techniques/AdaptationPatternsGomaa/SoftwareReconfigurationPatterns.pdf)

---

## 7. 仕様の不変部分と可変部分の分離

### 7.1 バリアント設計の概念

**バリアント構成**:

バリアント構成は、モデル階層全体のバリアント選択の組み合わせを表し、バリアント制御変数とその値のセットを含む。これを使用して、モデル階層内の特定のバリアントをアクティブ化できる。

参考文献:
- [Variant Configurations - MATLAB & Simulink](https://www.mathworks.com/help/simulink/var/variant-config-overview.html)
- [Variant Design - an overview | ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/variant-design)

### 7.2 製品ライン工学における分離

**ソフトウェアプロダクトライン（SPL）**:

ソフトウェアアダプテーションは、実行中に動作を変更する必要があるソフトウェアシステムに対処する。ソフトウェアプロダクトライン（SPL）エンジニアリングは、動的ソフトウェア適応のための体系的な計画と設計の手段を提供する。

**動的適応のための段階**:
1. 要求分析
2. 設計
3. **ターゲットシステム再構成**: 実行可能なターゲットシステムを、あるプロダクトラインメンバーのランタイム構成から新しいランタイム構成へ動的に変更

参考文献:
- [Software Reconfiguration Patterns for Dynamic Evolution of Software](https://cse.msu.edu/~chengb/CSE891/Techniques/AdaptationPatternsGomaa/SoftwareReconfigurationPatterns.pdf)

---

## 8. 仕様駆動の適応

### 8.1 仕様駆動適応とフィードバックループ

**モデリング言語のサポート**:
> モデリング言語は、メガモデルをモジュール化することにより、個々の適応ステップと完全なフィードバックループの仕様をサポートする。フィードバックループと適応ステップは、ランタイムモデルに作用するモデル操作のフローによる高いレベルの抽象化でモデル化される。

参考文献:
- [A Language for Feedback Loops in Self-Adaptive Systems](https://arxiv.org/pdf/1805.08678)

### 8.2 Requirements@Runtime

**実行時の要求仕様**:

ランタイム検証は、管理されたシステムが時相論理プロパティとして形式化された要求を満たしていることをチェックするためにフィードバックループで使用できる。

**要求の動的適応**:
- システムの進化または環境、管理されたシステム、要求自体の不確実性により、要求が変更される可能性がある
- ランタイム検証によって調査されるプロパティは、変化する要求を表すために動的に適応する必要がある
- 要求満足度に関する知識を保持しながら適応

参考文献:
- [Runtime Verification of Self-Adaptive Systems with Changing Requirements](https://arxiv.org/abs/2303.16530)

### 8.3 要求駆動の適応

**フィードバックループの第一級市民化**:

適応のための要求を表す新しい要素により、フィードバックループが要求仕様の第一級市民になる。適切な機械可読表現により、フィードバックループの汎用機能を実装し、実行時に要求について推論するフレームワークへの入力として機能できる。

参考文献:
- [Requirements-Driven Dynamic Adaptation](https://core.ac.uk/search?q=Requirements-Driven+Dynamic+Adaptation+to+Mitigate+Runtime+Uncertainties+for+Self-Adaptive+Systems.)

---

## 9. 進化的アーキテクチャと仕様

### 9.1 進化的アーキテクチャの原則

**ソフトウェア適応のパターン**:

ソフトウェアアダプテーションは、実行中に動作を変更する必要があるソフトウェアシステムに対処する。動的適応のためには、第3段階が必要：**ターゲットシステム再構成**。この段階では、実行可能なターゲットシステムが、あるプロダクトラインメンバーのターゲットシステムランタイム構成から新しいターゲットシステムランタイム構成へ動的に変更される。

参考文献:
- [Software Reconfiguration Patterns for Dynamic Evolution of Software](https://cse.msu.edu/~chengb/CSE891/Techniques/AdaptationPatternsGomaa/SoftwareReconfigurationPatterns.pdf)

### 9.2 アーキテクチャベースの進化

**パターン駆動の再利用**:

Pat-Evolは、アーキテクチャベースの進化のためのパターン駆動の再利用を提供する。サービスソフトウェアの進化において、アーキテクチャ変更ログからの継続的な自動パターン識別とパターンライブラリのサポートが重要である。

参考文献:
- [Pat-Evol: Pattern-Driven Reuse in Architecture-Based Evolution](https://ercim-news.ercim.eu/en88/special/pat-evol-pattern-driven-reuse-in-architecture-based-evolution-for-service-software)

### 9.3 進化におけるトレードオフ

**柔軟性と安定性のバランス**:

進化的アーキテクチャは、以下のバランスを取る必要がある：
- 変更への柔軟性
- コア機能の安定性
- パフォーマンスと保守性
- 短期的利益と長期的健全性

---

## 10. spec-oracleプロジェクトへの示唆

### 10.1 仕様進化の必然性

**重要な洞察**:

仕様は静的な成果物ではなく、ソフトウェアとともに進化する生きた文書である。spec-oracleプロジェクトにおいて、この進化をどのように管理するかが重要な課題である。

### 10.2 不変部分と可変部分の識別

**実践的アプローチ**:

1. **コア制約（不変部分）**: システムの本質的な性質を定義
2. **適応可能な制約（可変部分）**: 環境や要求の変化に応じて調整可能

この分離により、仕様の一部を固定しつつ、他の部分を柔軟に適応させることができる。

### 10.3 MAPE-Kループの応用

**自己適応的仕様管理**:

spec-oracleにMAP E-Kループを適用することで、仕様自体が自己適応的になる可能性がある：
- **Monitor**: 実装と仕様の乖離を監視
- **Analyze**: 乖離の原因と影響を分析
- **Plan**: 仕様または実装の調整計画
- **Execute**: 調整の実施
- **Knowledge**: 過去の適応パターンの蓄積

### 10.4 腐敗への対処

**仕様腐敗の防止策**:

1. **継続的な同期**: 実装と仕様の定期的な整合性チェック
2. **進化パターンの記録**: 変更の履歴とパターンの文書化
3. **エントロピー削減**: 定期的なリファクタリングと簡素化
4. **自動化ツール**: 変更の影響分析と伝播の自動化

---

## 11. 結論

### 11.1 主要な発見

仕様の進化と適応に関する調査から、以下の重要な知見が得られた：

1. **進化は避けられない**: ソフトウェアは変化し、仕様も変化しなければならない
2. **腐敗のメカニズム**: 老化、エントロピー増加、適応の失敗による腐敗
3. **自己適応システム**: MAPE-Kループによる体系的な適応管理
4. **ランタイムモデル**: 実行時の動的な仕様変更を可能にする
5. **不変と可変の分離**: 進化可能な仕様設計の鍵
6. **パターン駆動**: 再利用可能な進化パターンによる効率化

### 11.2 新しいソフトウェアエンジニアリングへの貢献

仕様進化の理論と実践は、新しいソフトウェアエンジニアリングに以下を提供する：

- **適応性**: 変化する要求と環境への対応
- **保守性**: エントロピーを管理し、腐敗を防ぐ
- **自律性**: 自己適応システムによる自動化
- **体系性**: パターンとフレームワークによる管理
- **実用性**: ランタイムモデルと動的適応の活用

### 11.3 未来への展望

仕様進化の研究は、以下の方向に進展している：

1. **AIとの統合**: 機械学習による進化パターンの自動学習
2. **予測的適応**: 変化を予測し、先行的に適応
3. **自己最適化**: 継続的な改善と最適化
4. **エコシステム全体の進化**: 単一システムを超えた進化管理

**最終的な洞察**:

仕様の進化と適応は、ソフトウェアエンジニアリングの中心的課題である。静的な「完璧な仕様」を目指すのではなく、**継続的に進化し適応する「生きた仕様」**を目指すべきである。spec-oracleプロジェクトは、この新しいパラダイムの実現に貢献する可能性を持つ。

---

## 参考文献

### 進化パターンと変更管理
- [Evolution styles: change patterns for Software Evolution](https://www.researchgate.net/publication/238743879_Evolution_styles_change_patterns_for_Software_Evolution)
- [Change patterns | Software and Systems Modeling](https://link.springer.com/article/10.1007/s10270-012-0276-6)
- [Software Evolution - GeeksforGeeks](https://www.geeksforgeeks.org/software-engineering/software-engineering-software-evolution/)
- [Software Change Management: Best Practices & Tools for 2026](https://www.superblocks.com/blog/software-change-management)
- [Pat-Evol: Pattern-Driven Reuse in Architecture-Based Evolution](https://ercim-news.ercim.eu/en88/special/pat-evol-pattern-driven-reuse-in-architecture-based-evolution-for-service-software)

### ソフトウェア老化と腐敗
- [Software aging - Wikipedia](https://en.wikipedia.org/wiki/Software_aging)
- [Software Aging - David Lorge Parnas](https://www.cs.drexel.edu/~yc349/CS451/RequiredReadings/SoftwareAging.pdf)
- [Why and How Software Systems decay](https://towardsdatascience.com/why-and-how-software-systems-decay-fa7ec83c4ff3/)
- [Detection, Classification and Prevalence of Self-Admitted Aging Debt](https://arxiv.org/html/2504.17428v1)
- [Programs, Life Cycles, and Laws of Software Evolution](https://users.ece.utexas.edu/~perry/education/SE-Intro/lehman.pdf)
- [Architectural Decay during Continuous Software Evolution](https://link.springer.com/chapter/10.1007/978-3-642-10619-4_15)
- [Software evolution: the lifetime of fine-grained elements](https://peerj.com/articles/cs-372.pdf)

### 自己適応システムとMAP E-K
- [Modeling and Analyzing MAPE-K Feedback Loops for Self-Adaptation](https://ieeexplore.ieee.org/document/7194653/)
- [MAPE-K reference model for self-adaptive systems](https://www.researchgate.net/figure/MAPE-K-reference-model-for-self-adaptive-systems-from-102_fig2_266646263)
- [On Managing Knowledge for MAPE-K Loops in Self-Adaptive Robotics](https://www.mdpi.com/2076-3417/12/17/8583)
- [Analysis of MAPE-K Loop in Self-adaptive Systems](https://link.springer.com/chapter/10.1007/978-3-031-26507-5_11)
- [MAPE-K Formal Templates to Rigorously Design Behaviors](https://dl.acm.org/doi/10.1145/2724719)

### ランタイムモデル
- [Models at Runtime for Self-Adaptive Software | MDELab](https://www.hpi.uni-potsdam.de/giese/public/mdelab/mdelab-projects/software-engineering-for-self-adaptive-systems/morisia/)
- [Using Models at Runtime to Address Assurance for Self-Adaptive Systems](https://arxiv.org/pdf/1505.00903)
- [Runtime Software Architectural Models for Adaptation, Recovery and Evolution](https://ceur-ws.org/Vol-2019/mrt_3.pdf)
- [Models@run.time](https://hpi.de/en/giese/research/projects/modelsruntime.html)

### 動的適応と進化
- [Dynamic Adaptation - an overview | ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/dynamic-adaptation)
- [Managing Dynamic Evolution of Architectural Types](https://link.springer.com/chapter/10.1007/978-3-540-88030-1_22)
- [Software Reconfiguration Patterns for Dynamic Evolution of Software](https://cse.msu.edu/~chengb/CSE891/Techniques/AdaptationPatternsGomaa/SoftwareReconfigurationPatterns.pdf)
- [Runtime Adaptation of Applications Through Dynamic Recomposition](https://link.springer.com/chapter/10.1007/978-3-540-31967-2_9)

### バリアント設計
- [Variant Configurations - MATLAB & Simulink](https://www.mathworks.com/help/simulink/var/variant-config-overview.html)
- [Variant Design - an overview | ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/variant-design)

### 仕様駆動適応
- [A Language for Feedback Loops in Self-Adaptive Systems](https://arxiv.org/pdf/1805.08678)
- [Runtime Verification of Self-Adaptive Systems with Changing Requirements](https://arxiv.org/abs/2303.16530)
- [Run-time model evaluation for requirements model-driven self-adaptation](https://www.academia.edu/53876917/Run_time_model_evaluation_for_requirements_model_driven_self_adaptation)
- [Requirements-Driven Dynamic Adaptation](https://core.ac.uk/search?q=Requirements-Driven+Dynamic+Adaptation+to+Mitigate+Runtime+Uncertainties+for+Self-Adaptive+Systems.)

---

**調査完了日**: 2026年2月14日
**調査者**: researcher-10
**プロジェクト**: spec-oracle
