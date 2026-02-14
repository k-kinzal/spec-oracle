# IEC 61508（機能安全）と仕様

## 概要

[IEC 61508](https://en.wikipedia.org/wiki/IEC_61508)は、国際電気標準会議（IEC）が発行した国際標準であり、電気・電子・プログラマブル電子（E/E/PE）安全関連システムの機能安全に関する方法を規定する。正式名称は「Functional Safety of Electrical/Electronic/Programmable Electronic Safety-related Systems（電気・電子・プログラマブル電子安全関連システムの機能安全）」である。IEC 61508は、すべての産業に適用可能な基本的な機能安全規格である。

## 機能安全の定義

IEC 61508は機能安全を次のように定義している：「EUC（Equipment Under Control：制御対象機器）およびEUC制御システムに関する全体的安全の一部であり、E/E/PE安全関連システム、他の技術の安全関連システム、および外部リスク低減設備の正しい機能に依存するもの」

つまり、機能安全とは、システムまたはその構成要素が正しく機能することによって達成される安全である。

## 安全度水準（SIL）

### SILの概要

[SIL（Safety Integrity Level：安全度水準）](https://en.wikipedia.org/wiki/Safety_integrity_level)は4段階に分類される：SIL1、SIL2、SIL3、SIL4。各SILレベルでリスクの大きさが異なり、SIL 4が最も高いリスク低減を提供し、SIL 1が最も低いリスク低減を提供する。

SILは、安全機能によって提供される相対的なリスク低減レベルである。SIL評価は、ハザードの頻度と深刻度に相関する。これらは、安全を維持および達成するために必要な性能、および故障の確率を決定する。

### SIL決定プロセス

[IEC 61508はリスクベースの標準](https://www.tuvsud.com/en-us/services/functional-safety/iec-61508)であり、危険な運用状況のリスクを定性的に評価し、体系的故障を回避または制御し、ランダムハードウェア故障を検出または制御、あるいはその影響を緩和するための安全対策を定義する。

機能安全を確保するには、EUC（制御対象機器）のハザード分析とリスク評価が必要である。ハザード分析は、製品、プロセス、またはアプリケーションによって生じる可能性のあるすべてのハザードを特定する。これにより、安全規格の安全機能要求が決定される。

### SILの要求カテゴリ

[IECのIEC 61508規格](https://www.perforce.com/blog/qac/what-iec-61508-safety-integrity-levels-sils)は、2つの広範なカテゴリにグループ化された要求を使用してSILを定義している：
- **ハードウェア安全完全性**
- **体系的安全完全性**

デバイスまたはシステムが特定のSILを達成するには、両方のカテゴリの要求を満たす必要がある。

## 仕様の厳密さとSIL

### SILレベルごとの要求手法

IEC 61508では、SILレベルが高くなるほど、仕様記述と検証の厳密さが増す。特にIEC 61508-3（ソフトウェア要求）には、SILレベルに応じて使用すべき設計・コーディング標準、分析・テスト技法を詳述した9つの表がある。

### 半形式・形式手法の推奨

**形式手法の推奨**:
IEC 61508では、[SIL 4機能に対して形式手法が「高度に推奨」](https://www.formalmind.com/blog/if-you-need-comply-iso-26262-iec-61508-or-similar-standards-you-may-need-work-more-formal/)されている。これは、より高い安全完全性レベルには、より厳密な検証と妥当性確認のアプローチが必要であるという標準の認識を反映している。

**半形式手法の推奨**:
[IEC 61508規格](https://www.exida.com/Blog/Software-Modeling-and-Functional-Safety-Part-2)は、特定のSILレベルに関して「半形式手法」の使用、コンピュータ支援の仕様と設計ツール、設計標準、性能モデリング、モデルベースのテストケース生成、モデルベースのテスト、静的モデリング、動的モデリングに関する要件を持っている。

これらの要件は、UMLなどのモデリング表記法と、その使用を可能にするツールの使用を通じて、完全または部分的に満たすことができる。

**重要な実装上の注意**:
モデリング表記法とツールが有能な人員によって適切に使用されない場合、不明確で、保守不可能で、テスト不可能で、不完全で、および/または不正確なモデルが安全上の問題を引き起こす可能性がある。モデルの様々な部分がどのようなタイプの情報、どのレベルの情報を取り込む必要があるかを決定し、その情報を明確かつ完全な方法で表現することが重要である。

## V字モデルと仕様の階層

### V字モデルの概要

[V字モデル](https://blog.saphira.ai/making-iec-61508-practical-a-step-by-step-v-model-for-industrial-systems/)は、プロセスの各ステップが次のステップに追跡可能である必要性を示しており、ライフサイクル中の検証の矢印と、その終わりでの妥当性確認ステップによって暗示されている。

### 仕様階層構造

V字モデルは、各仕様活動（Vの左側）が対応する検証・妥当性確認活動（Vの右側）を持つように開発を組織化する：

1. **概念と範囲** → 意図された使用に対する妥当性確認
2. **ハザードとリスク分析 / SIL目標** → 安全機能とその完全性の妥当性確認
3. **安全要求仕様（SRS）** → SRSに対するシステム検証
4. **システムとアーキテクチャ設計** → サブシステム/インターフェースの統合テスト
5. **詳細なHW/SW設計** → ユニットとモジュールの検証

### 主要な要求

目的には、ソフトウェア安全機能の機能安全要求の導出、ソフトウェアの体系的能力、および必要な安全機能の実装が含まれる。

双方向トレーサビリティが明示的な目的として規定されており、これにより、すべてのアウトライン要求（機能安全要求を含む）が完全に対処されていること、すべての詳細要求がアウトライン要求に追跡できること、余剰の不要なコードがないことを確保するのに役立つ。

## 安全要求仕様書（SRS）

### SRSの目的と重要性

[SRS（Safety Requirements Specification：安全要求仕様書）](https://insights.tuv.com/jpblog/fshints6)は、リスク分析・評価を通じて決定した安全機能およびSIL（安全度水準）に関する具体的な要求を取りまとめ、実際の設計・開発の基礎となる文書である。

SRSは機能安全プロジェクトにおいて極めて重要な文書であり、その品質はプロジェクト全体の成功を大きく左右する。

### SRSの記述要件

**基本構成**:
[SRSの書き出し](http://controlsystemlab.com/index.php/fs-series-07/)は、このシステムは何であるかの説明で、名称や用途、システム全体の一部であるかなどの紹介から始める必要がある。そして以下を記述する：

- 目標安全レベル
- 適合させる安全規格
- 動作モード
- 使用環境
- 使用電源
- 制限事項

**記述品質の要件**:
SRSを作成する上で大切なことは、「設計者以外の人々が理解できるかどうか」である。そのためには、以下が求められる：

- 文章の完全性
- 論理性
- 理解容易性
- 可読性
- 図や表の多用

**安全機能の定義**:
安全機能の定義とは、センサー（S）、演算部（L）、アクチュエータ（A）それぞれがどのように動作するべきなのかを定義する。またそれらの機能が働くための全体条件や環境条件、達成すべき安全完全性のレベルなども、SRSを構成する要素である。

### SRSの位置付け

[SRSはIEC 61508安全ライフサイクルモデルのE/E/PESのフェーズ9](https://indico.ess.eu/event/973/attachments/7616/10806/ESS-0238059_-_IEC_61508_Safety_Requirements_Specification_Document_for_PSS0.pdf)に含まれ、IEC 61508 Ed 2 Part 2 clause 7.2.3にSRSの内容に関するガイダンスが提供されている。

文書構造は、会社の手順および特定のアプリケーション分野の作業慣行を考慮に入れることができる。

## IEC 61508の構造

[IEC 61508は7つのパート](https://www.byhon.it/structure-of-iec-61508/)から構成される：

- **Part 1（一般要求）**: 安全ライフサイクルの各フェーズに関連する活動、文書化、管理、妥当性確認を定義
- **Part 2（E/E/PEシステムの要求）**: 安全要求の仕様をどのように定義するか、および製品の設計と実装中に実行すべき活動を規定
- **Part 3（ソフトウェア要求）**: Part 2と同様の要求をソフトウェアに適用
- **Part 4（定義と略語）**: 標準で使用される用語の定義と略語を提供
- **Part 5（SIL決定方法の例）**: E/E/PE安全システムのSILレベル計算方法を提供
- **Part 6（Part 2と3の適用ガイドライン）**: 主に定量的分析のガイドラインを提供
- **Part 7（技法と測定の概要）**: 安全工学とソフトウェアで使用される技法の説明を提供

## IEC 61508派生規格

IEC 61508を基にした産業別の派生規格が多数存在する。

### ISO 26262（自動車）

[ISO 26262](https://en.wikipedia.org/wiki/ISO_26262)は、自動車の電気・電子システム向けの機能安全規格IEC 61508の適応版である。ISO 26262仕様は2011年に正式にリリースされ、E/Eシステムの汎用機能安全規格IEC 61508の適応版として発表された。

**主な相違点**:

**範囲と適用**:
ISO 26262は自動車産業に特化して調整されているのに対し、IEC 61508はより広範な範囲を持つ。IEC 61508は、自動車、プロセス、機械など幅広い産業に適用可能なより一般的な規格である。

**安全度レベルの評価**:
規格間の最も重要な違いの1つは、安全評価システムに関係している。[自動車ではSILの代わりにASIL](https://www.leadventgrp.com/blog/iso-26262-vs-iec-61508-a-comparative-analysis)（Automotive Safety Integrity Level：自動車安全完全性レベル）が、達成すべき安全への信頼度の尺度として使用される。ASILは単に自動車安全完全性レベルの略である。自動車関係者は4つのレベルを保持したが、SIL 1〜4の代わりにA、B、C、Dと呼んでいる。

ISO 26262はIEC 61508の用語「安全故障割合（Safe failure fraction：SFF）」を使用しない。代わりに、単一点故障指標と潜在故障指標という用語が使用される。

**リスク評価の方法**:
ISO 26262は、ハザードへの暴露、傷害の深刻度、制御可能性を表で組み合わせてASILレベルを導くリスクグラフの使用を規定している。

**IEC 61508との関係**:
ISO 26262はIEC 61508の適応版であるが、IEC 61508への準拠を主張していない。他のほとんどの産業別適応版とは異なり、ISO 26262はIEC 61508を規範的参照として列挙していない。

### IEC 62304（医療機器ソフトウェア）

[IEC 62304](https://en.wikipedia.org/wiki/IEC_62304)は、国際電気標準会議が発行した国際標準であり、医療ソフトウェアおよび医療機器内のソフトウェアの開発におけるライフサイクル要求を規定している。

**IEC 61508との関係**:
IEC 62304は、[IEC 61508から派生したセクター固有の機能安全規格](https://www.perforce.com/blog/qac/what-iec-62304)である。より具体的には、医療機器ソフトウェア工学における既存のベストプラクティスと、鉄道産業、プロセス産業、土木機械製造などの多様なセクターでの産業別解釈の基礎として使用されてきた、より汎用的な機能安全規格IEC 61508が推奨する機能安全原則の融合である。

この規格は、良好なソフトウェア開発方法、技法、ツールの情報源として、包括的な機能安全規格であるIEC 61508を参照している。

**主な相違点**:
IEC 62304には、IEC 61508のリリース前に医療機器産業で確立された用語とベストプラクティスが含まれている。例えば、「SIL」ではなく「クラス」の使用は、FDAの分類システムと整合している。

### EN 50128（鉄道ソフトウェア）

[EN 50128](https://ldra.com/ldra-blog/software-safety-and-security-standards-for-gts-and-rail-applications/)は、鉄道アプリケーション（軌道側と列車側の両方）向けの安全関連ソフトウェアの開発に関する欧州規格である。

**IEC 61508との関係**:
EN 50128は[IEC 61508から派生](https://www.jamasoftware.com/blog/how-en-50128-establishes-functional-safety-standards-for-railway-software/)しており、鉄道のための技術委員会CENELEC TC 9Xによって準備された。より具体的には、EN 50128はIEC 61508の専門化であり、通信、信号、処理システムを含む鉄道制御および保護システムソフトウェアの安全完全性の要求を満たすために、鉄道アプリケーション（軌道側と列車側の両方）のソフトウェア（アプリケーションプログラミング、オペレーティングシステム、サポートツール、ファームウェアを含む）を提供する方法を規定する欧州規格である。

**国際版**:
この規格の国際版はIEC 62279であり、EN 50128と同一である。

**最近の動向**:
EN 50128は[EN 50716:2023](https://ldra.com/en-5012x/)に取って代わられた。これは、鉄道制御および保護システムのソフトウェア（EN 50128）と車上ソフトウェア（EN 50657）に関する安全規格を統合し、サイバーセキュリティを組み込んでいる。

### その他の派生規格

IEC 61508から派生した規格は、[信頼性と安全性に要求がある](https://www.iar.com/embedded-development-tools/functional-safety)あらゆる種類の産業（プロセス産業、鉄道、ビルディングオートメーションなど）で現在使用されている：

- **ISO 25119**: 農業機械
- **IEC 61511**: プロセス産業安全計装システム
- **ISO 13849**: 機械の安全関連部分
- **DO-178C**: 航空宇宙ソフトウェア

## ハザード分析とリスク評価

### 安全関連システムの仕様記述プロセス

[システム安全](https://en.wikipedia.org/wiki/System_safety)は、エンジニアがリスク管理戦略を開発するためにシステムベースのアプローチを使用することを求める安全工学の概念である。従来の安全戦略は、過去のシステム事故を引き起こした条件を回避するためにシステムを修正することに焦点を当てているのに対し、システム安全分析は、事故が発生する前にハザードを積極的に特定および分析することに焦点を当てている。

### 主要な定義

**ハザード**:
計画外または望ましくない事象につながる、または寄与する可能性のある条件、事象、または状況。

**リスク**:
事象の深刻度と事象の可能性の観点から、望ましくない事象の影響の表現。

### プロセスと方法論

このプロセス全体を通じて、[ハザードが特定され、リスクが分析、評価、優先順位付けされ、結果が意思決定のために文書化](https://uspas.fnal.gov/materials/12UTA/08_hazard_assessment.pdf)される。SSA（System Safety Assessment：システム安全評価）の目標は、リスクを積極的に特定し、次にエンジニアリングまたは行動方法を通じてリスクを排除または制御することにより、安全な作業環境を確保することである。

**軍事航空産業の実践**:
軍事航空産業では、安全クリティカルな機能が特定され、[ハードウェア、ソフトウェア、人間システム統合の全体的な設計アーキテクチャが徹底的に分析](https://safety.army.mil/Portals/0/Documents/ON-DUTY/ARMYSYSTEMS/TOOLSREFERENCESLITERATURE/Standard/sys_safety_v_charts.pdf)され、明示的な安全要求が導出され、実証されたハザード分析プロセス中に規定される。包括的なハザード分析を実施し、ハザードに寄与または引き起こす可能性のある信頼できる欠陥、故障条件、寄与要因、因果要因を決定することは、システムエンジニアリングプロセスの本質的な部分である。明示的な安全要求は、客観的な安全証拠と、デューデリジェンスを示す十分な安全文書化によって導出、開発、実装、検証されなければならない。

### 分析ツール

**定性的リスク分析ツール**:
- HAZOP（Hazard and Operability Analysis：ハザード・操作性分析）
- What-if/チェックリスト分析
- FMEA（Failure Modes and Effects Analysis：故障モードと影響分析）

**単純なリスク分析ツール**:
- FMECA（Failure Modes, Effects, and Criticality Analysis：故障モード・影響・致命度分析）
- LOPA（Layer of Protection Analysis：保護層分析）

**詳細な定量的リスク分析ツール**:
- フォルトツリー（Fault Tree）
- イベントツリー（Event Tree）

## 安全ライフサイクル

IEC 61508は、設計エラーと欠落を発見して排除するためのベストプラクティスに基づいた、安全ライフサイクルと呼ばれる工学プロセスを定義している。特定の技法により、ライフサイクル全体を通じてミスとエラーが回避されることを保証する。

初期概念、リスク分析、仕様、設計、インストール、保守、廃棄に至るまでのどこかで導入されたエラーは、最も信頼性の高い保護をも損なう可能性がある。[IEC 61508は、ライフサイクルの各フェーズで使用すべき技法を規定](https://www.mhlw.go.jp/file/06-Seisakujouhou-11200000-Roudoukijunkyoku/0000117706.pdf)している。

### SIL決定基準

特定のSILレベルには、3つの要因によって影響を受ける独自の要求がある：
1. 定量的信頼性要求
2. アーキテクチャ上の制約
3. 体系的安全完全性

## 仕様記述における実践的課題

### モデリングの適切な使用

IEC 61508-3の要求を満たすためにモデリング表記法とツールを使用する場合、適切な実装が重要である。不適切に使用された場合、以下の問題が生じる可能性がある：

- 不明確なモデル
- 保守不可能なモデル
- テスト不可能なモデル
- 不完全なモデル
- 不正確なモデル

これらはすべて安全上の問題につながる可能性がある。

### 仕様の完全性と理解容易性のバランス

SRSの作成において、技術的完全性と理解容易性のバランスを取ることが重要である。形式手法や半形式手法を使用することで仕様の精度は向上するが、すべての関係者（設計者、検証者、認証機関など）が理解できる形で記述する必要がある。

## 考察

### 機能安全と仕様の厳密さ

IEC 61508は、安全クリティカルシステムにおける仕様の重要性を明確に認識している。SILレベルが上がるにつれて、仕様記述と検証の厳密さを段階的に高めることを要求している点は、リスクと開発コストのバランスを取る実用的なアプローチである。

**SIL 4で形式手法が高度に推奨される理由**:
最高レベルの安全性が要求されるシステムでは、曖昧性のない数学的に厳密な仕様が必要である。しかし、すべてのSILレベルで形式手法を要求しないことで、実用性と厳密性のバランスを保っている。

### V字モデルの意義

V字モデルは、仕様の階層性とトレーサビリティの重要性を視覚化している：

1. **階層的な仕様**: 概念レベルから詳細設計まで、段階的に詳細化
2. **双方向トレーサビリティ**: すべての要求が実装に追跡でき、すべての実装が要求に追跡できる
3. **検証と妥当性確認の対称性**: 各仕様段階に対応するテスト段階が存在

これは、仕様駆動開発の理想的なモデルの一つである。

### 派生規格の多様性

IEC 61508から派生した産業別規格（ISO 26262、IEC 62304、EN 50128等）の存在は、以下を示している：

**産業固有の要求**:
各産業には固有のハザード、リスク特性、開発プラクティスが存在する。IEC 61508という共通の基盤の上に、産業固有の要求を追加することで、より実用的な規格となる。

**用語の差異**:
- 自動車：ASIL（A, B, C, D）
- 医療機器：クラス
- 一般産業：SIL（1, 2, 3, 4）

この用語の違いは、各産業の歴史的背景と既存のプラクティスを反映している。

### SRSの重要性

安全要求仕様書（SRS）は、機能安全プロジェクトの中心的な文書である。SRSが「設計者以外の人々が理解できる」ことを重視している点は重要である：

**ステークホルダーの多様性**:
SRSの読者には、設計者、実装者、テスター、認証機関、保守担当者など、多様なバックグラウンドを持つ人々が含まれる。

**完全性と理解容易性の両立**:
形式的な厳密さと理解容易性は、しばしばトレードオフの関係にある。図表の活用、段階的な詳細化、適切な抽象化レベルの選択などにより、このバランスを取る必要がある。

### ハザード分析の中心性

IEC 61508がリスクベースの標準であることは、以下を意味する：

**仕様の出発点**:
仕様は、抽象的な機能記述から始まるのではなく、具体的なハザード分析から始まる。何が危険か、どの程度危険か、どのように制御するかが、仕様の内容を決定する。

**定量的な目標設定**:
SILは定量的な故障確率目標を持つ。これにより、仕様が満たすべき客観的な基準が明確になる。

### 形式手法の段階的適用

IEC 61508の形式手法への段階的なアプローチは、実用的である：

- **SIL 1-2**: 半形式手法、モデリング
- **SIL 3**: より厳密な半形式手法
- **SIL 4**: 形式手法が高度に推奨

この段階的アプローチは、コストと効果のバランスを取りつつ、必要な安全性を確保する。

## 結論

IEC 61508は、機能安全における仕様の役割を包括的に定義している国際標準である。その主要な特徴は：

1. **リスクベースのアプローチ**: ハザード分析から仕様を導出
2. **段階的な厳密さ**: SILレベルに応じて仕様の厳密さを調整
3. **ライフサイクル全体の管理**: 概念から廃棄まで、各段階での仕様と検証
4. **双方向トレーサビリティ**: 要求から実装、実装から要求への完全な追跡可能性
5. **形式手法の適切な使用**: 最高レベル（SIL 4）で形式手法を推奨

IEC 61508とその派生規格は、産業界における安全クリティカルシステムの開発において、仕様がどうあるべきかの実践的な指針を提供している。完全な形式化を目指すのではなく、リスクレベルに応じた適切な厳密さを要求することで、実用性と安全性のバランスを実現している。

これは、仕様理論の実世界への適用の好例であり、理論的理想と実践的制約の間の現実的なバランスを示している。

## 参考文献

### IEC 61508関連
- [IEC 61508 - Wikipedia](https://en.wikipedia.org/wiki/IEC_61508)
- [IEC 61508 Functional Safety Standard | TÜV SÜD](https://www.tuvsud.com/en-us/services/functional-safety/iec-61508)
- [What Is IEC 61508? Determining Safety Integrity Levels (SILs) | Perforce Software](https://www.perforce.com/blog/qac/what-iec-61508-safety-integrity-levels-sils)
- [What Is IEC 61508? IEC 61508 Standard Guide - LDRA](https://ldra.com/iec-61508/)
- [Overview of IEC 61508 & Functional Safety](https://assets.iec.ch/public/acos/IEC%2061508%20&%20Functional%20Safety-2022.pdf)
- [Structure of IEC 61508 - BYHON](https://www.byhon.it/structure-of-iec-61508/)

### SIL関連
- [Safety integrity level - Wikipedia](https://en.wikipedia.org/wiki/Safety_integrity_level)
- [What is SIL according to IEC 61508 standard](https://h-on.it/functional-safety-iec-61508/)
- [Safety Integrity Level (SIL) - 61508/61511 - Emerson](https://www.emerson.com/documents/automation/technical-white-paper-safety-integrity-level-sil-en-71898.pdf)

### V字モデルと仕様階層
- [Making IEC 61508 Practical: A Step-by-Step V-Model for Industrial Systems](https://blog.saphira.ai/making-iec-61508-practical-a-step-by-step-v-model-for-industrial-systems/)

### 形式手法と半形式手法
- [If you need to comply with ISO 26262, IEC 61508 or similar standards - Formal Mind](https://www.formalmind.com/blog/if-you-need-comply-iso-26262-iec-61508-or-similar-standards-you-may-need-work-more-formal/)
- [Software Modeling and Functional Safety - IEC 61508 | exida](https://www.exida.com/Blog/Software-Modeling-and-Functional-Safety-Part-2)

### 派生規格

#### ISO 26262（自動車）
- [ISO 26262 - Wikipedia](https://en.wikipedia.org/wiki/ISO_26262)
- [ISO 26262 vs. IEC 61508: Which Functional Safety Standard is Right for You? - Leadvent Group](https://www.leadventgrp.com/blog/iso-26262-vs-iec-61508-a-comparative-analysis)
- [What is ISO 26262 Functional Safety Standard? | Synopsys](https://www.synopsys.com/glossary/what-is-iso-26262.html)

#### IEC 62304（医療機器）
- [IEC 62304 - Wikipedia](https://en.wikipedia.org/wiki/IEC_62304)
- [What Is IEC 62304? - Perforce Software](https://www.perforce.com/blog/qac/what-iec-62304)
- [IEC 62304 - LDRA](https://ldra.com/iec-62304/)

#### EN 50128（鉄道）
- [Software Standards for Railways - LDRA](https://ldra.com/ldra-blog/software-safety-and-security-standards-for-gts-and-rail-applications/)
- [How EN 50128 Establishes Functional Safety Standards for Railway Software](https://www.jamasoftware.com/blog/how-en-50128-establishes-functional-safety-standards-for-railway-software/)

### ハザード分析とリスク評価
- [Hazard analysis - Wikipedia](https://en.wikipedia.org/wiki/Hazard_analysis)
- [System safety - Wikipedia](https://en.wikipedia.org/wiki/System_safety)
- [System Safety - SEBoK](https://sebokwiki.org/wiki/System_Safety)

### 日本語資料
- [機能安全を ご存じですか!? - 厚生労働省](https://www.mhlw.go.jp/file/06-Seisakujouhou-11200000-Roudoukijunkyoku/0000117706.pdf)
- [JEMIMA 機能安全規格の技術解説](https://www.jemima.or.jp/activities/file/func_safety_201311.pdf)
- [教えます。認証検査で最も重要な2つの文書 - TÜV](https://insights.tuv.com/jpblog/fshints6)
- [プラント設備エンジニア向け機能安全 - CSL 制御システム研究所](http://controlsystemlab.com/index.php/fs-series-07/)
- [機能安全活用テキスト - 厚生労働省](https://www.mhlw.go.jp/file/06-Seisakujouhou-11200000-Roudoukijunkyoku/0000151401.pdf)
- [IEC 61508、IEC 62304、ISO 26262 および EN 50128 の各規格へのモデルの準拠性のチェック - MATLAB](https://jp.mathworks.com/help/slcheck/ug/model-checks-for-iec-61508-iso-26262-and-en-50128-compliance.html)
