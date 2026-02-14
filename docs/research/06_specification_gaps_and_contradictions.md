# 仕様の漏れと矛盾の検出

## 1. 導入：仕様における完全性と一貫性の重要性

ソフトウェア開発において、仕様の品質は最終的な製品の品質を大きく左右する。仕様における「漏れ（incompleteness）」と「矛盾（inconsistency）」は、実装の誤りやシステムの予期しない動作を引き起こす主要な原因となる。本調査では、これらの問題の分類、検出手法、および形式手法による対処方法について詳細に検討する。

形式手法は、ソフトウェアおよびハードウェアシステムの仕様記述、開発、検証のための数学ベースの技術である。形式仕様記述言語により、システム仕様を一定の規則に従って厳密に記述することで、解釈が一意に定まり、論理的な矛盾が存在しないことが保証される。

## 2. 仕様の漏れ（Incompleteness）の分類

仕様の漏れには複数の次元が存在し、それぞれが異なる性質の問題を引き起こす。

### 2.1 漏れの二つの側面

会話の中で議論された通り、仕様の漏れには本質的に異なる2つのタイプが存在する：

#### **漏れA：未規定（Underspecification）**
仕様が特定の状況や入力に対して何も決めていない状態。仕様の記述が部分的（partial）であり、全ての可能なケースをカバーしていない。これは**仕様の部分性（partiality）**の問題である。

形式的には、部分関数（partial function）として表現できる。部分関数とは、取りうる引数の一部に対してしか返り値が定義されていない関数である。対照的に、全域関数（total function）は、全ての引数に対して返り値が（正しい型で）定義されている。

**具体例：**
- 条件分岐の漏れ（missing cases）：`if x > 0 then A else if x < 0 then B` （x=0の場合が未定義）
- 定義域の制限：除算関数で除数がゼロの場合の扱いが未定義
- エッジケースの未考慮：境界値での動作が仕様に記述されていない

#### **漏れB：カバレッジ不足（Coverage Gap）**
仕様が意図した領域を完全にカバーしていない。つまり、システムが到達可能な状態や実行可能なシナリオのうち、仕様が言及していない部分が存在する状態。これは**仕様のカバレッジ（coverage）**の問題である。

**具体例：**
- 要求仕様のカバレッジギャップ：すべての機能要件がテストケースでカバーされていない
- ユースケースの漏れ：想定される利用シナリオが仕様に含まれていない
- 統合時の相互作用が考慮されていない

### 2.2 仕様の完全性における概念整理

**仕様カバレッジ（Specification Coverage）と完全性（Totality）**

仕様カバレッジとは、仕様書（要件）に対するテスト比を表す指標である。これは機能保証が求められる場面で重要となる。注目すべきは、コードカバレッジ100%を達成しても、機能カバレッジが達成されているとは限らないという点である。

仕様の完全性には複数の観点がある：
- **定義域の完全性（Domain Completeness）**：すべての入力に対して仕様が定義されているか
- **カバレッジの完全性（Coverage Completeness）**：すべての要求される機能や振る舞いが仕様に含まれているか
- **形式的完全性（Formal Completeness）**：論理システムとしての完全性（すべての真である命題が証明可能か）

### 2.3 形式仕様における完全性の表現

形式仕様言語では、部分関数を全域関数に変える方法は主に2つある：

1. **入力型を狭める**：有効な入力のみを受け付ける型を定義する（例：`NonZeroInt`型の導入）
2. **出力型を広げる**：エラーケースを含む代数的データ型を使用する（例：`Result<T, Error>`型）

近代的な関数型プログラミング言語（Coqを含む）では、単純型付きラムダ計算が中心概念となっており、関数をtotalにしてdiscriminated union（直和型）を積極的に使うことで、ドメインロジックの大部分が型システムに表現される。

## 3. 仕様の矛盾（Inconsistency）の分類と検出

### 3.1 矛盾の種類

仕様における矛盾は、複数の要求や制約が同時に満たされない状況を指す。

#### **直接的矛盾（Direct Contradiction）**
- 同じ状況に対して異なる動作を要求する
- 例：「xが正の時、yは増加する」と「xが正の時、yは減少する」

#### **間接的矛盾（Indirect Contradiction）**
- 論理的推論により導き出される矛盾
- 例：A→B、B→C、A∧¬Cといった制約の組み合わせ

#### **型の矛盾（Type Inconsistency）**
- 同じ変数に複数の型を割り当てる
- 形式仕様記述言語により検出可能

#### **一貫性の欠如（Incoherence）**
- 異なる機能間で仕様が衝突する
- 個々の機能で必要と考えられる仕様をすべて実現しようとすると、異なる機能のいくつかの仕様間で衝突する状態が生じる

### 3.2 矛盾検出の最新技術：ALICE

ALICE（Automated Logic for Identifying Contradictions in Engineering）は、制御された自然言語で表現された形式要求に特化した、新しい自動矛盾検出システムである。形式論理と大規模言語モデル（LLM）、特にGPT-3を統合することで、要求文書内の矛盾を識別・分類する画期的なシステムとなっている。

#### **ALICEの方法論**

ALICEの方法論は、拡張された矛盾の分類法に基づいており、矛盾の有無とタイプを確認するための**7つの重要な質問**に対処する決定木モデルを採用している。この手法は、形式論理の機能と大規模言語モデルの能力を組み合わせ、2つの要求間の矛盾を自動的に検出・解決する。

#### **性能評価**

比較研究において、ALICEの性能はLLMのみのアプローチを大きく上回り、**全矛盾の60%を検出**した。より具体的には、このハイブリッド手法は**精度99%、再現率60%**を達成し、実世界の複雑な要求データセットを処理する効果を実証している。

#### **検出メカニズム**

ALICEは3段階のプロセスを使用する：
1. 条件文と擬似文法要素の識別
2. 形式論理による一貫性チェック
3. LLMによるニュアンスのある矛盾検出

このアプローチは、形式手法とAIの統合により、要求工学における矛盾検出の新しい地平を開いている。

### 3.3 従来の矛盾検出技術

#### **SCR（Software Cost Reduction）表記法による一貫性検証**

SCR表記法は、リアルタイム組込みシステムの要求を仕様化するための形式手法であり、表形式の記法に基づいている。

**一貫性チェックの特性：**
- **ドメインカバレッジ（Domain Coverage）**：すべての入力ケースがカバーされているか
- **型の正しさ（Type Correctness）**：型の一貫性が保たれているか
- **決定性（Determinism）**：同じ入力に対して常に同じ出力が定義されているか
- **循環定義の検出（Circular Definition Detection）**：定義が循環していないか

一貫性検証により、型エラー、非決定性、欠落ケース、循環定義などのエラーを自動的に検出できる。

#### **形式的基盤**

SCR記法に形式意味論を提供し、一貫性検証の基盤とするため、形式要求モデルはソフトウェアシステムを有限状態オートマトンとして表現する。このオートマトンは、監視対象の環境量の変化に応じて外部から見える出力を生成する。

#### **サポートツール**

SCRツールセットには以下が含まれる：
- 仕様を構築するためのエディタ
- 形式要求モデルとの一貫性をテストする一貫性チェッカー
- 仕様を記号的に実行するシミュレータ
- 仕様が選択されたアプリケーション特性を満たすか検証する検証器

## 4. 形式検証における健全性と完全性

### 4.1 論理システムの基本特性

形式検証において、**健全性（soundness）**と**完全性（completeness）**は証明システムの基本的な特性である。

#### **健全性（Soundness）**

証明システムが健全であるとは、証明可能なものはすべて実際に真であることを意味する。より形式的には：

```
もし φ₁, …, φₙ ⊢ ψ ならば φ₁, …, φₙ ⊨ ψ
```

健全性は、論理システムを望ましいものとみなす最初の理由を提供する。証明システムが健全であれば、無効な引数の導出が存在しない。

#### **完全性（Completeness）**

証明システムが完全であるとは、真であるものはすべて証明可能であることを意味する。完全性の特性は、すべての妥当性（validity）が証明可能であることを意味する。

健全性と完全性を合わせると、すべての、そして妥当性のみが証明可能であることが保証される。

### 4.2 ゲーデルの限界定理

重要な制限として、ゲーデルの結果は、自然数をエンコードできる論理システムに対して、健全かつ完全な証明システムは存在しないことを示した。これは、十分に表現力のある形式検証と定理証明における基本的な限界を強調している。

一階述語論理の完全性は、ゲーデルによって最初に明示的に確立されたが、主要な結果のいくつかはSkolemの以前の研究に含まれていた。

### 4.3 検証における応用

健全性と完全性は、プログラム解析において同じコインの両面として使用され、すべてのエラーを捕捉することと誤検出を避けることとのバランスを取る。

**トレードオフ：**
- 健全性を重視すると、すべての真のエラーを検出できるが、誤検出（false positive）が増える可能性がある
- 完全性を重視すると、報告されるエラーはすべて真のエラーだが、一部のエラーを見逃す（false negative）可能性がある

## 5. 検証における空虚な真（Vacuous Truth）の問題

### 5.1 空虚な真の概念

数学と論理学において、空虚な真（vacuous truth）とは、前提条件が満たされないために真となる条件文や全称文のことである。例えば、「部屋にあるすべての携帯電話の電源が切られている」という文は、部屋に携帯電話が存在しない場合に（空虚に）真となる。

### 5.2 形式検証における課題

形式検証において、空虚な真は重大な課題を提示する：

構造が式を満たすが、非興味深い方法で満たす場合、それは空虚に満たされている可能性が高く、システムまたは式のいずれかに問題があることを示唆している。例えば、リクエストが決して送信されないシステムは、`AG(req → AF grant)`を空虚に満たす。

**空虚な証明がもたらす問題：**
- 検証しようとしているDUT（Device Under Test）の動作について何の情報も提供しない
- よく書かれていない特性は、しばしば「前提」（左辺の定義）から始まり、決して真にならない矛盾した状態を定義する
- 最も一般的なのは、誤ってある信号とその補数をANDしてしまう場合

### 5.3 検出と対処

**典型的なケース：**
- 設計がサポートしていない動作を特性が記述している場合
- 例：赤→緑→黄→赤の順序を期待する信号機コントローラを検証しているが、実際のコードは赤の後に黄色を点滅させる欧州型コントローラである場合

**検出ツール：**
Questa PropCheckのような最新の形式解析ツールは、解析開始直後に空虚な特性をフラグ付けする。

## 6. 要求工学における曖昧性の問題

### 6.1 曖昧性の定義と分類

要求工学において、曖昧性（ambiguity）は「読者がRE（Requirements Engineering）の文脈を知っているにもかかわらず、複数の解釈が可能である」と定義される。要求における曖昧性は、誤解された要求や不完全な要求よりも扱いにくい問題である。なぜなら、要求は自然言語で記述されるためである。

#### **曖昧性のレベル：**

1. **語彙的曖昧性（Lexical Ambiguity）**
   - 同じ用語が異なるものを示すために使用される
   - 言語の固有の特徴である場合がある（例：自然言語における同音異義語）

2. **構文的曖昧性（Syntactic Ambiguity）**
   - 単一の文に対して複数の構文木が存在することから生じる
   - 文の構造解析が一意でない

3. **意味的曖昧性（Semantic Ambiguity）**
   - ソーステキストが語彙と構文の両方で一意に決定されているが、文に複数の意味を割り当てることができる場合
   - 文脈依存の解釈の問題

### 6.2 過小仕様と過剰仕様

#### **過小仕様（Underspecification）**

NLPシステムは曖昧なテキストにフラグを立て、過小仕様が発生する場所を指摘できる。その後、要求エンジニアは、ドメインエキスパートと正しい解決策について合意するか、それを削除できる。

**欠如（Absence）**は、特定の側面に関する詳細が完全に欠けている状態を表し、抽象化の極端なケースであり、特定の情報内容が無に抽象化されている。

#### **過剰仕様（Overspecification）**

過剰仕様は、時間の浪費や新しいエラーの生成を引き起こす可能性がある欠陥である。一方、要求における望ましい品質としての抽象化は、過剰仕様を回避し、要求を簡素化する。

### 6.3 曖昧性の軽減手法

#### **形式言語による仕様記述**

曖昧性を回避する一つの方法は、形式言語での要求の仕様化である。形式言語は、言語の構文と意味論を厳密に定義するための数学的評価に基づいている。

しかし、研究者は以下のような技術で要求の曖昧性を軽減することに焦点を当ててきた：
- 自然言語処理技術
- 要求テンプレート
- 形式手法

#### **形式手法の利点**

形式手法は、開発プロセスの早い段階で過小仕様や矛盾などのエラーを発見するのに役立つ。

## 7. 要求トレーサビリティマトリクスとギャップ分析

### 7.1 要求トレーサビリティマトリクス（RTM）の概要

要求トレーサビリティマトリクス（Requirements Traceability Matrix, RTM）は、要求と他の成果物（テスト、課題、ソースコードなど）との関係をマッピングするツールまたは文書である。RTMは、ユーザー要求を対応するテストケース、成果物、関連活動にマッピングおよび追跡する構造化された文書である。

#### **RTMの構造**

通常、RTMは要求を対応するテストケースとリンクするグリッドで構成される：
- **行**：要求を表す
- **列**：テストケースを示す
- **セル**：特定のテストケースが特定の要求をカバーしているかを表す

### 7.2 ギャップ分析

ギャップ分析（Gap Analysis）は、ソフトウェアテストにおいて提供されるものと要求されるものとの間の不一致を識別するプロセスである。ギャップテストとも呼ばれる。

#### **ギャップ分析の3つの基本的な質問：**
1. 現在どこにいるのか（Where are we now?）
2. どこにいたいのか（Where do we want to be?）
3. どうやってそこに到達するのか（How will we get there?）

### 7.3 仕様カバレッジとギャップの関連

**重要な認識：**

各要求仕様を各テストケースがカバーすることを保証できる設定されたフレームワークは存在しない。これは特に組込みシステムにおいて関連性が高く、テストは要求仕様の完全なカバレッジを保証すべきだが、設定された形式がなく、各テストケースが各要求をカバーしたという保証もない。

#### **RTMを使用したギャップの識別**

トレーサビリティマトリクスを使用してギャップを識別するプロセス：
1. テストされる要求を識別する
2. トレーサビリティマトリクスを作成する
3. テストケースを実行し、結果をトレーサビリティマトリクスに記録する
4. トレーサビリティマトリクスの結果を分析して、ギャップや不一致を識別する

**トレーサビリティマトリクスの空白スペースは、調査が必要な潜在的な領域である。**このようなギャップは2つのことを意味する可能性がある：
- テストチームがどういうわけか機能を考慮し損ねた
- その機能が実装されていない

### 7.4 カバレッジギャップの種類

**カバレッジギャップ**は、重要なビジネスフロー、統合、またはユーザージャーニーが適切にテストされていない場合に発生する。これらのギャップは、エッジケース、ネガティブシナリオ、またはクロスシステムの相互作用がテスト中に無視されたために、しばしば本番環境での障害につながる。

## 8. 仕様の完全性評価と検出技術

### 8.1 形式手法による完全性解析

JKindは、コンポジショナル検証（compositional verification）を実行することで完全性をチェックする。これは、すべてのコンポーネントレベルの要求の論理積が、各システムレベルの要求を論理的に導出するかどうかを判定する。

#### **ARSENAL フレームワーク**

ARSENALフレームワークは、自然言語処理と形式手法の組み合わせを使用して、自然言語の要求を形式表現にマッピングする。IR（中間表現）テーブルは、形式手法ツール用の形式モデルを生成するために使用される。

### 8.2 不完全性の評価方法論

形式特性のセットの不完全性を推定するために、**モデル検査、高レベル故障シミュレーション、および自動テストパターン生成の組み合わせに基づくカバレッジ方法論**が提案されている。

**重要な認識：**
証明された特性のセットは不完全である可能性があり、したがって仕様に対するデジタルシステム実装の動作チェック完全性を保証しない。

### 8.3 実現可能性（Realizability）の検証

**FRET（Formal Requirements Elicitation Tool）**は、NASAで開発された要求抽出ツールで、反応型システムの仕様の実現可能性に焦点を当てている。入力はFRETishと呼ばれる構造化自然言語で形成される。

## 9. 要求工学における完全性研究の最新動向（2024）

### 9.1 AIとLLMの統合

2000年から2024年までの研究を網羅した体系的レビューは、定義、検出方法、完全性メトリクス、改善フレームワーク、およびサポートツールを統合し、**新たなAIベースのソリューション**を強調している。

**主要な知見：**
- 大規模言語モデル（LLM）は、要求品質の向上において変革的な可能性を示している
- AIと自動化を要求工学により深く統合する機会が強調されている
- 自然言語処理と形式手法の融合が進んでいる

### 9.2 ハイブリッドアプローチの台頭

形式論理とLLMを組み合わせた**ハイブリッドアプローチ**が、以下の領域で顕著な成果を上げている：
- 矛盾検出（ALICE: 精度99%、再現率60%）
- 要求の曖昧性解消
- 自動要求検証

これらの手法は、形式手法の厳密性とAIの柔軟性を組み合わせることで、従来のアプローチの限界を克服している。

## 10. 実践的考察と課題

### 10.1 形式手法の適用における課題

形式手法コミュニティは、仕様記述と設計の完全な形式化を過度に強調しているとの指摘がある。実務者は、対象システムの複雑さだけでなく、使用される言語の表現能力の完全性も形式化を困難にすると感じている。

その結果、**軽量形式手法（lightweight formal methods）**が提案されている。これらは、部分的な仕様記述と適用に焦点を当てている。

### 10.2 日本語の曖昧性の問題

日本の要求工学において、**日本語的曖昧さが要求定義や設計を行う上で最大の障害になる**と指摘されている。仕様の曖昧さがシステム開発上の致命的な問題につながることが認識されている。

### 10.3 仕様の統合における矛盾

個々の機能で必要または有効と考えられる仕様をすべて実現しようとすると、**異なる機能のいくつかの仕様間で衝突する**という状態が生じる。これを防ぐには、早い段階で全体の仕様化を進める必要がある。

## 11. まとめと提言

### 11.1 漏れと矛盾の体系的理解

本調査により、仕様の漏れと矛盾は以下のように体系化できることが明らかになった：

**漏れの分類：**
1. **未規定（漏れA）**：仕様の部分性、定義域の不完全性
2. **カバレッジ不足（漏れB）**：要求のカバレッジギャップ、機能の漏れ

**矛盾の分類：**
1. **直接的矛盾**：明示的な要求間の衝突
2. **間接的矛盾**：論理的推論により導出される矛盾
3. **型の矛盾**：型システムレベルでの不整合
4. **一貫性の欠如**：機能間の仕様の衝突

### 11.2 検出手法の選択

**形式的アプローチ：**
- SCR表記法による一貫性チェック：型エラー、非決定性、欠落ケース、循環定義の検出
- モデル検査：完全性と一貫性の自動検証
- 定理証明：健全性と完全性の形式的保証

**ハイブリッドアプローチ：**
- ALICE（形式論理＋LLM）：高精度な矛盾検出（精度99%、再現率60%）
- 自然言語処理＋形式手法：曖昧性の軽減と形式化の支援

**実践的アプローチ：**
- 要求トレーサビリティマトリクス：カバレッジギャップの可視化
- ギャップ分析：体系的な漏れの識別
- 軽量形式手法：部分的な形式化による実用性の向上

### 11.3 今後の方向性

1. **AIと形式手法の統合の深化**：LLMの能力を活用した要求工学の自動化と高度化
2. **軽量形式手法の発展**：実務での採用を促進する実用的なアプローチ
3. **多言語対応**：日本語など自然言語の曖昧性に対応した検証技術
4. **全体的仕様化の推進**：早期段階での統合的な仕様化による矛盾の予防

### 11.4 実務への示唆

仕様の品質向上には、以下の多層的アプローチが有効である：

1. **要求獲得段階**：構造化自然言語や要求テンプレートの使用
2. **仕様記述段階**：形式手法と自然言語のハイブリッド記述
3. **検証段階**：自動化ツールによる矛盾と漏れの検出
4. **維持段階**：トレーサビリティマトリクスによる継続的な品質管理

形式手法の完全な適用が困難な場合でも、部分的な形式化や自動検証ツールの活用により、仕様の品質を大幅に向上させることが可能である。

---

## 参考文献・情報源

### 形式手法と仕様記述の基礎
- [形式手法 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%BD%A2%E5%BC%8F%E6%89%8B%E6%B3%95)
- [国立情報学研究所 石川冬樹「形式手法と仕様記述」の探求に向けて](https://research.nii.ac.jp/~f-ishikawa/work/files/2012-05-11-SQiP-intro.pdf)
- [形式手法 - 日経クロステック](https://xtech.nikkei.com/atcl/learning/lecture/19/00102/00303/)

### 仕様の完全性と不完全性
- [Completeness in Formal Specification Language Design for Process-Control Systems](http://sunnyday.mit.edu/papers/completeness.pdf)
- [Mapping the Landscape of Requirements Completeness - Springer](https://link.springer.com/chapter/10.1007/978-3-032-04200-2_26)
- [(In)completeness in specifications - ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/0950584994900337)
- [Formal Methods in Requirements Engineering: Survey and Future Directions](https://lorchrob.github.io/publications/re_survey_paper.pdf)

### 矛盾検出技術
- [Automated requirement contradiction detection through formal logic and LLMs - Springer](https://link.springer.com/article/10.1007/s10515-024-00452-x)
- [Towards an automatic contradiction detection in requirements engineering - Cambridge](https://www.cambridge.org/core/journals/proceedings-of-the-design-society/article/towards-an-automatic-contradiction-detection-in-requirements-engineering/C7D7E69A58BBC2BC6054AF0BB972A3E1)
- [Automated consistency checking of requirements specifications - ACM](https://dl.acm.org/doi/10.1145/234426.234431)
- [Practical Behavioral Inconsistency Detection - IEEE Xplore](https://ieeexplore.ieee.org/document/6983818)

### 健全性と完全性
- [Soundness and completeness - forall x: Calgary](https://forallx.openlogicproject.org/html/Ch22.html)
- [Soundness and Completeness of an Axiom System for Program Verification - SIAM](https://epubs.siam.org/doi/10.1137/0207005)
- [Soundness and Completeness - Cornell CS2800](https://www.cs.cornell.edu/courses/cs2800/2016sp/lectures/lec39-sound-complete.html)
- [Soundness - Wikipedia](https://en.wikipedia.org/wiki/Soundness)
- [論理学「健全性と完全性」- 慶應義塾大学](http://web.sfc.keio.ac.jp/~hagino/logic16/05.pdf)
- [健全性 - Wikipedia](https://ja.wikipedia.org/wiki/%E5%81%A5%E5%85%A8%E6%80%A7)

### 全域関数と部分関数
- [プログラミング言語の基礎 - Types](https://www.chiguri.info/sfja/plf/Types.html)
- [AI時代のコード品質戦略 - バグに強いコードを型でデザインする](https://zenn.dev/dinii/articles/totality-is-all-you-need)
- [Partial function - Wikipedia](https://en.wikipedia.org/wiki/Total_function)
- [Function: Specification and Definition](https://abstractmath.org/MM/MMFuncSpec.htm)

### 要求の曖昧性
- [Underspecification - Wikipedia](https://en.wikipedia.org/wiki/Underspecification)
- [Reducing Requirements Ambiguity via Gamification - PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC9313919/)
- [Ambiguity in Requirements Specification - Springer](https://link.springer.com/chapter/10.1007/978-1-4615-0465-8_2)
- [Avoiding Ambiguity in Requirements Specifications - Waterloo](https://cs.uwaterloo.ca/~dberry/FTP_SITE/tech.reports/TjongThesis.pdf)
- [Ambiguity in Requirements Engineering: Towards a Unifying Framework - ResearchGate](https://www.researchgate.net/publication/336351565_Ambiguity_in_Requirements_Engineering_Towards_a_Unifying_Framework)

### ギャップ分析とトレーサビリティ
- [What Is Gap Analysis in Software Testing? - TestFort](https://testfort.com/blog/what-is-gap-analysis-in-software-testing)
- [Gap Analysis in Software Testing - Qodo](https://www.qodo.ai/blog/gap-analysis-in-software-testing/)
- [Requirements Traceability Matrix - Perforce](https://www.perforce.com/resources/alm/requirements-traceability-matrix)
- [Requirements Traceability Matrix - GeeksforGeeks](https://www.geeksforgeeks.org/software-testing/requirement-traceability-matrix/)
- [Why Are Traceability and Test Coverage Important? - TestRail](https://www.testrail.com/blog/test-coverage-traceability/)

### SCR表記法
- [Consistency checking of SCR-style requirements specifications - IEEE](https://ieeexplore.ieee.org/document/512546)
- [Automated Consistency Checking of Requirements Specifications - DTIC](https://apps.dtic.mil/sti/tr/pdf/ADA465574.pdf)
- [SCR: a toolset for specifying and analyzing requirements - IEEE](https://ieeexplore.ieee.org/document/521891)
- [The SCR Approach to Requirements Specification - ResearchGate](https://www.researchgate.net/publication/221222683_The_SCR_Approach_to_Requirements_Specification_and_Analysis)

### 空虚な真
- [Vacuous truth - Wikipedia](https://en.wikipedia.org/wiki/Vacuous_truth)
- [Formal Tech Tip: Vacuous Proofs - Verification Horizons](https://blogs.sw.siemens.com/verificationhorizons/2017/12/06/formal-tech-tip-what-are-vacuous-proofs-why-they-are-bad-and-how-to-fix-them/)
- [Sanity Checks in Formal Verification - CS.HUJI](https://www.cs.huji.ac.il/~ornak/publications/concur06b.pdf)

### 日本語の要求工学資料
- [要求工学 - Wikipedia](https://ja.wikipedia.org/wiki/%E8%A6%81%E6%B1%82%E5%B7%A5%E5%AD%A6)
- [要求工学入門 - SQiP2011チュートリアル参加レポート - LINE Engineering](https://engineering.linecorp.com/ja/blog/requirement-engineering-intro-software-quality-2011/)
- [要求工学：現実と仮想をつなぐために - J-STAGE](https://www.jstage.jst.go.jp/article/jssst/29/2/29_2_43/_pdf)
- [要求工学 - 日経クロステック](https://xtech.nikkei.com/atcl/learning/lecture/19/00102/00508/)
- [要求仕様の曖昧さを理解し、ソフトウェアテストを組み立てる - ベリサーブ](https://www.veriserve.co.jp/asset/approach/column/test-technique/software-test03.html)

### カバレッジと仕様検証
- [カバレッジとは？ソフトウェア分野における基準や計測方法 - SHIFT](https://service.shiftinc.jp/column/4547/)
- [カバレッジ - MATLAB & Simulink](https://www.mathworks.com/discovery/coverage.html)
- [Functional Coverage - Accellera](https://www.accellera.org/images/eda/sv-ec/att-1377/01-functional-coverage.pdf)

---

**調査実施日**: 2026-02-14
**調査者**: researcher-11
