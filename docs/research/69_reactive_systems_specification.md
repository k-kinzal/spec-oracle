# リアクティブシステムの仕様

## 概要

リアクティブシステム（Reactive Systems）は、外部環境からの刺激（入力）に対して継続的に応答を返す、イベント駆動型のシステムである。David HarelとAmir Pnueliによって定義されたこの概念は、リアルタイムソフトウェアやハードウェアシステム、組み込みシステム、制御システムなど、環境との継続的相互作用が本質的なシステムを特徴づける。

リアクティブシステムの仕様記述は、変換システム（transformational systems）とは根本的に異なるアプローチを要求する。本稿では、変換システムとリアクティブシステムの区別、同期プログラミング言語（Lustre/SCADE、Esterel、Signal）、リアクティブマニフェスト、Reactive Extensions（Rx）、関数型リアクティブプログラミング（FRP）など、リアクティブシステムの仕様記述に関する主要なアプローチと技術を調査する。

## 変換システムとリアクティブシステムの区別

### Harel & Pnueliの定義

David HarelとAmir Pnueliは、リアクティブシステムを「環境が決定する速度で環境に反応するブラックボックス」として特徴づけた。**「リアクティブシステム」という用語**は、環境駆動のイベントへの反応に焦点を当てた継続的な振る舞いを示すシステムを指すために、HarelとPnueliによって造語された。

### 変換システム（Transformational Systems）

変換システムは、入力/出力関係による変換または関数によって仕様化される。入力/出力関係が通常十分な仕様と見なされる。

**特徴：**
- 入力を受け取り、計算を行い、出力を生成して終了する
- バッチ処理プログラムやコンパイラなどが典型例
- 関数的な入力→出力の関係で記述可能

### リアクティブシステム（Reactive Systems）

対照的に、リアクティブシステムは以下の特徴を持つ：

**特徴：**
- **イベント駆動**: 外部および内部の刺激に継続的に反応する必要がある
- **終了しない**: 理論的には永遠に実行され続ける
- **環境との相互作用**: 入力と出力の組み合わせを通じた環境とのリンク

リアクティブシステムは、入力から出力への変換関係だけでなく、**一つのステップでの可能な組み合わせを通じた出力と入力の間のリンク**によっても記述される。

### 仕様記述の課題

Harel とPnueliは、リアクティブシステムが振る舞いの記述のための満足できる方法を見つけることに関して特に問題があるシステムとして選別され、そのためStatechartsメソッドを推奨した。

この研究は、変換的アプローチと比較して、リアクティブシステムを仕様化する独特の課題を理解するための重要な基礎を築いた。

## 同期プログラミング言語

同期プログラミング手法は1980年代初頭から発展し、現在では多くのクリティカルな組み込みシステムプロジェクトで使用されている。最初の同期プログラミング言語は1980年代にフランスで発明された：**Esterel**、**Lustre**、**Signal**。

同期パラダイムは、リアクティブシステム設計のための論理的時間抽象化を提供し、予測可能でタイムリーでリアクティブな方法で振る舞う組み込みシステムの自動合成を可能にする。

### Lustre / SCADE

#### Lustreの概要

**Lustre**は、リアクティブシステムのプログラミングのための形式的に定義された宣言的同期データフロープログラミング言語である。1980年代初頭の研究プロジェクトとして始まった。

**特徴：**
- **データフロー指向**: ブロック図、オペレータのネットワーク、動的サンプルシステムなど、これらの領域での通常の記述ツールに非常に近い
- **同期解釈**: プログラムで時間を扱うのに適している
- **効率的コンパイル**: 同期解釈により、効率的な逐次プログラムにコンパイルできる
- **時相論理との類似性**: Lustreの形式主義は時相論理に非常に類似しており、プログラムを書くことと性質を表現することの両方に使用できる

**産業応用：**
LustreとScadeは、組み込みシステムをプログラミングするためのデータフロー言語である。Lustreは、Esterel-Technologiesによって開発されたSCADE産業環境のカーネル言語である。

#### SCADE Suite

**SCADE（Safety Critical Application Development Environment）**は、Ansys（旧Esterel Technologies、2012年にAnsysに買収）によって開発されたモデルベース設計ツールである。

**認証サポート：**
- **DO-178C**: TQL-1でDO-178C/DO-330に対応した適格開発ツール
- **IEC 61508**: SIL 3で認証済み
- **EN 50128**: SIL 3/4で適格
- **ISO 26262**: ASIL Dまで適格

**SCADE Suite KCG**は、CとAdaのコード生成器であり、DO-178Bソフトウェアのレベル Aまでの開発ツールとして適格である。

**産業成功：**
Ansysの顧客は、SCADEスイートを使用してDO-178C標準の認証を達成することに大きな成功を収めている。SCADEスイートには、DO-178C標準要件とすでに整合性のある事前適格化されたピースが含まれている。

**DO-178C認証キット**は、SCADE Suite KCGをDO-330/TQL-1で適格化するために必要なすべてのエビデンスを提供する。

**設計哲学：**
SCADEは、形式的同期言語基盤を使用して設計されており、物事が予測可能で信頼性のある方法で起こることを保証する。これは安全性クリティカルなソフトウェア開発にとって重要である。

### Esterel

#### 概要

**Esterel**は、複雑なリアクティブシステムの開発のための同期プログラミング言語である。決定論的並行リアクティブシステムの仕様のための命令型同期プログラミング言語である。

#### 主要特性

**命令型プログラミングスタイル:**
Esterelの命令型プログラミングスタイルは、並列性とプリエンプションの単純な表現を可能にし、制御支配的なモデル設計に適している。

**同期モデル:**
古典的な非同期言語とは、同期仮説によって異なる：**システムの出力は概念的に入力と同期している**。

Esterelで使用される時間の概念は、非同期言語の時間とは以下の点で異なる：物理的時間の概念が順序の概念に置き換えられ、イベントの同時性と先行性のみが考慮される。

#### 文の種類

2種類の文がある：
1. **ゼロ時間文**: 同じ瞬間に実行して終了する
2. **遅延文**: 所定のサイクル数だけ遅延する

**信号（Signals）**が唯一の通信手段であり、値を持つ信号と値を持たない信号が利用可能である。

#### 応用分野

Esterelは、SyncCharts、Lustre、Argos、Signalのような同期言語ファミリーの一つであり、リアルタイムシステムや制御オートマトンを含むリアクティブシステムのプログラミングに特に適している。

### Signal

#### 概要と多時刻性

**Signal**は、リアクティブシステムの設計と分析に使用される多時刻（同期、マルチクロック）言語である。

Signalプロセスは本質的に「多時刻的（polychronous）」である：一般に、同じクロックを持たない複数の信号を扱う。

#### 多時刻モデリング

**多時刻モデリング（Polychronous modeling）**は、同期リアクティブアプローチに関連している。同期アプローチと多時刻アプローチの基本的な違いは、時間モデルにある：

- **同期システム**: 全順序の時間概念を持ち、所与の入力に対して決定論的に離散ステップで反応する
- **多時刻システム**: 部分順序の時間概念を伴うシステムモデル

#### 実践的ツール

**Polychrony環境**は、複雑な同期問題の解決策を設計するために使用される。構造的操作的意味論を使用した統一された構成的意味論フレームワークは、同期モジュールの構成的振る舞いと多時刻ネットワークのマルチクロック振る舞いの両方を包含する。

#### 仕様記述

同期言語Signalは、組み込みシステムの設計に使用される。Signalプログラミング言語による同期リアクティブ仕様は、形式的で宣言的な方法で組み込みシステムを設計することを可能にする。

### 同期言語の産業応用

**安全性クリティカルシステム:**
同期言語Signalは、安全性クリティカルなリアルタイムシステムを開発するための形式仕様形式主義であり、決定論的並行振る舞いを仕様化するのに適したマルチクロックデータフローモデリング言語である。

Signalコンパイラは、データフロー仕様からコードを生成しながら、設計中のシステムの安全性性質（デッドロックフリー、決定論）を分析・検証する。

**航空電子工学と認証:**
航空電子ソフトウェアと他の組み込みシステムの主な違いは、実際の標準が商用標準よりもはるかに詳細で厳密であることであり、通常は何百ページもの文書で記述され、通常はリアルタイムオペレーティングシステム上で実行される。

安全性クリティカルな組み込みシステムの認証標準には、DO-178C、ISO 26262、IEC 61508が含まれる。

## Reactive Manifesto（リアクティブ宣言）

### 概要と歴史

**Reactive Manifesto（リアクティブ宣言）**は、2013年にJonas Bonerと他の開発者によって作成され、システムが**即応性（Responsive）**、**耐障害性（Resilient）**、**弾力性（Elastic）**、**メッセージ駆動（Message Driven）**であるべきことを特定しており、これらを**リアクティブシステム**と呼ぶ。22,000以上の署名を集めてサポートされている。

### 4つの核心原則

#### 1. 即応性（Responsive）

システムは可能な限りタイムリーに応答する。**即応性は使いやすさと実用性の基礎**であるが、それ以上に、即応性は問題を迅速に検出し効果的に対処できることを意味する。

平常時だけでなく、どんな場面でも維持される必要がある。

#### 2. 耐障害性（Resilient）

システムは障害に直面しても即応性を保つ。**耐障害性は、複製、封じ込め、隔離、委譲によって達成される**。

障害は各コンポーネント内に封じ込められ、コンポーネントを互いに隔離することで、システムの一部が失敗して回復できる一方で、システム全体を損なうことはない。

お互いを守り合い、再び回復できるのがリアクティブシステムの耐障害性である。

#### 3. 弾力性（Elastic）

システムは変動するワークロードの下で即応性を保つ。リアクティブシステムは、これらの入力をサービスするために割り当てられるリソースを増減させることで、入力レートの変化に反応できる。

#### 4. メッセージ駆動（Message Driven）

リアクティブシステムは、**非同期メッセージパッシング**に依ってコンポーネント間の境界を確立し、疎結合、隔離、位置透過性を保証する。

明示的なメッセージパッシングを採用することで、システム内のメッセージキューを形成・監視し、必要に応じてバックプレッシャーを適用することにより、負荷管理、弾力性、フロー制御が可能になる。

### 利点

リアクティブシステムとして構築されたシステムは、より柔軟で疎結合でスケーラブルである。これにより、開発が容易になり、変更に対応しやすくなる。障害に対して大幅に寛容であり、障害が発生した場合、災害ではなく優雅さを持って対処する。

### The Reactive Principles

リアクティブ宣言を補完するものとして、**The Reactive Principles**（リアクティブ原則）が、分散アプリケーションのための設計原則をより詳細に記述している。

## Reactive Extensions（Rx）

### 概要と歴史

**ReactiveX（Reactive Extensions）**は、観測可能なシーケンス（observable sequences）を使用して、非同期およびイベントベースのプログラムを構成するためのライブラリである。

Reactive Extensions（Rx）は、2011年頃にMicrosoftのCloud Programmability Teamによって作成され、.NET Framework向けの初期実装は2011年6月21日にリリースされた。

### 核心概念

**Observer Patternの拡張:**
Reactive Extensionsライブラリは、オブザーバーパターンを拡張し、非同期およびイベントベースのプログラムの構成を可能にする。

オブザーバーがObservableを購読し、ObservableがアイテムやitSelf通知を送信することで、オブザーバーのメソッドを呼び出す。

**Observable Streams:**
Reactive Extensionsの文脈でのObservableストリームは、next、error、completeの3つのイベントを発行するイベントエミッターのようなものであり、observableはerrorイベントまたはcompleteイベントを発行するまでnextイベントを発行する。

### 動作原理

Rxによって実装されるプッシュモデルは、Rx.Observable/Observerの観測可能パターンによって表現され、Rx.Observableはすべてのオブザーバーに状態変化を自動的に通知する。

### 利点

非同期イベントのストリームを、配列のようなデータアイテムのコレクションに使用するのと同じ種類の単純で構成可能な操作で扱うことができる。

**オペレータ（Operators）**により、Observableによって発行されるアイテムのシーケンスを変換、結合、操作、処理することができる。

### 実装と普及

ReactiveXは、Java、JavaScript、C#、Python、Swiftなど多くの言語で実装されており、クロスプラットフォームでの非同期プログラミングの標準的アプローチとなっている。

## 関数型リアクティブプログラミング（FRP）

### 概要と定義

**関数型リアクティブプログラミング（Functional Reactive Programming, FRP）**は、関数型プログラミングのビルディングブロック（map、reduce、filterなど）を使用して、リアクティブプログラミング（非同期データフロープログラミング）のためのプログラミングパラダイムである。

本質的に、FRPは関数型プログラミング原則を組み込むことでリアクティブプログラミング上に構築される。

### 歴史的背景

**元の定式化:**
関数型リアクティブプログラミングの元の定式化は、Conal ElliottとPaul HudakによるICFP 97論文「Functional Reactive Animation」に見られる。

Conal Elliottは20年前に、明確な**表示的意味論（denotational semantics）**を持つ関数型リアクティブプログラミングを提案した。

### 表示的意味論とデザイン

**基本原則:**
FRPは2つの単純で基本的な原則に基づいている：
1. **正確で単純な表示を持つこと**
2. **連続時間（continuous time）**

第一の性質は、Peter Landinが「表示的（denotative）」および「真に関数的（genuinely functional）」と呼んだもので、問題領域を超えて適用され、**正確で実装に依存しない仕様**を保証する。

**Denotational Design:**
各メソッドの意味（denotational semantics）を綴る際、Elliottは美しい繰り返しパターンに気づいた：各メソッドの意味は、その意味のための同じメソッドに対応する。これは、関数ライブラリの設計を導くために表示的意味論を使用するというElliottのより広い哲学を反映している。

### BehaviorとEvent

**古典的FRPモデル:**
1997年の論文「Functional Reactive Animation」では、振る舞い（behaviors）——時間変化する値——とイベント（events）を使用して、アニメーションのような動的システムをモデル化するHaskellに埋め込まれたドメイン固有言語としてFRPを提案した。

**Behaviorの表示:**
古典的FRPモデルでは、その表示が時間の関数である「behavior」抽象化がある。対話的振る舞いは、その後、behaviors間のホスト言語（例：Haskell）関数としてモデル化される。

より具体的には、関数型リアクティブプログラミング（FRP）で使用してきたモデルは、型aの動的（時間変化）入力と型bの動的出力のための `(T->a) -> (T->b)` である（ここでTは時間）。

**EventとSignal:**
FRPにおける重要なアイデアは、振る舞い（behaviors）とイベント（events）の概念である。FRPの最初の定式化は、連続的意味論を使用し、連続時間にわたって変化する値をモデル化し、「behaviors」、後に「signals」と呼ばれ、評価の詳細（サンプリングレートなど）をリアクティブモデルから分離した。

### 仕様との関係

**実装に依存しない仕様:**
表示的意味論に基づくFRPのアプローチは、実装の詳細から独立した振る舞いの仕様を提供する。これにより、以下が可能になる：

1. **正しさの推論**: 数学的基盤により、プログラムの性質を形式的に推論可能
2. **最適化の自由**: 実装は意味論を保持する限り自由に最適化可能
3. **コンポーザビリティ**: 振る舞いとイベントの合成が数学的に明確

**標準化への動き:**
現在FRPには複数のライブラリとアプローチがあるが、標準化への取り組みが見られる。例えば、JavaのReactive Streams仕様がリアクティブプログラミングの側面を標準化したように、異なるFRP実装間での標準化の必要性が認識されている。

ただし、FRP自体はReactive Streamsのような単一の統一された仕様を持たないが、Conal Elliottらによって定められた正確な数学的仕様または「表示的意味論」に必ずしも従わない実装を記述するために、この用語が採用され使用されている。

## リアクティブプログラミングと仕様の関係

### アーキテクチャレベル vs 実装レベル

**リアクティブシステム（アーキテクチャ）:**
リアクティブシステムはアーキテクチャレベルでリアクティブ原則を適用する。システム全体の設計として、即応性、耐障害性、弾力性、メッセージ駆動を実現する。

**リアクティブプログラミング（実装）:**
リアクティブシステムを実現する手段として、以下のようなリアクティブプログラミング技法が利用される：
- Future/Promise
- Reactive Streams
- Actor Model（Akka、Erlangなど）
- FRP

### 形式検証との接続

**時相論理による検証:**
リアクティブシステムの振る舞いは形式仕様を通じて記述され、安全性性質（safety properties）と活性性質（liveness properties）を含むタイミング性質が時相論理式によって表現される。

**検証技法:**
- **計算木論理（CTL）**: 分岐時間論理でリアクティブシステムの性質を表現
- **線形時間時相論理（LTL）**: 線形時間での性質を表現
- **公正遷移システム（FTS）**: リアクティブシステムの計算モデル

**安全性と活性:**
リアクティブシステムの性質は通常、CTLやLTLなどの時相論理を使用して表現される：
- **安全性性質**: 悪いことは決して起こらない
- **活性性質**: 良いことがいずれ起こる

**プログラム変換技法:**
プログラム変換技法は、安全性性質と活性性質の両方の検証に使用でき、蒸留（distillation）を使用してリアクティブシステムを、時相性質を検証するために分析できる単純化された形式に変換する。

### 仕様言語としての同期言語

同期言語（Lustre、Esterel、Signal）は、仕様記述言語としても機能する：

1. **形式的基盤**: 数学的に厳密な意味論
2. **実行可能仕様**: 仕様から直接コード生成可能
3. **検証可能**: モデル検査や定理証明が可能
4. **認証サポート**: DO-178CなどのSCADEのような産業ツールでの認証

## リアクティブシステム仕様の課題と展望

### 課題

1. **複雑性**: 並行性、非決定性、タイミング制約の組み合わせ
2. **活性性質の検証**: 安全性よりも証明が困難
3. **スケーラビリティ**: 状態空間爆発の問題
4. **ツールの成熟度**: 産業グレードのツールはまだ限定的
5. **学習曲線**: 形式手法と時相論理の専門知識が必要

### 将来の方向性

**AI/機械学習の統合:**
- リアクティブシステムの自動合成
- 性質の自動推論
- テストケースの自動生成

**クラウドとエッジの融合:**
- クラウドネイティブリアクティブシステム
- エッジコンピューティングでのリアクティブパターン
- サーバーレスアーキテクチャとの統合

**量子コンピューティング:**
量子リアクティブシステムの理論と実装

**標準化の進展:**
- FRPの統一的仕様
- リアクティブシステムの相互運用性標準
- 認証プロセスの標準化

## まとめ

リアクティブシステムの仕様は、変換システムとは根本的に異なるアプローチを要求する。HarelとPnueliによって確立された理論的基盤から、Lustre/SCADE、Esterel、Signalのような実用的な同期プログラミング言語、さらにReactive ManifestoやReactive Extensions（Rx）のような現代的アプローチまで、多様な技術とパラダイムが発展してきた。

**主要な洞察：**

1. **本質の違い**: リアクティブシステムは終了しない継続的相互作用であり、変換システムの入力→出力パラダイムとは異なる
2. **同期パラダイムの力**: 形式的基盤と実用性を組み合わせ、安全性クリティカルシステムでの認証を可能にする
3. **多層アプローチ**: アーキテクチャレベル（Reactive Manifesto）から実装レベル（Rx、FRP）まで
4. **形式検証の重要性**: 時相論理による安全性と活性の証明
5. **表示的意味論の価値**: FRPにおけるConal Elliottのアプローチが示す、実装に依存しない仕様の重要性

**実践的価値：**

- **SCADE**: 航空宇宙産業でのDO-178C認証
- **Rx**: クロスプラットフォーム非同期プログラミング
- **Reactive Manifesto**: 大規模分散システムのアーキテクチャ指針
- **FRP**: 宣言的で合成可能なリアクティブプログラミング

リアクティブシステムの仕様記述は、理論と実践の両面で成熟しつつあり、安全性クリティカルな組み込みシステムから大規模クラウドシステムまで、広範な応用を持つ。形式的基盤と実用的ツールの継続的発展により、より信頼性が高く保守可能なリアクティブシステムの構築が可能になっている。

---

## 主要参考文献とソース

### Harel & Pnueli / 理論的基礎
- [On the Development of Reactive Systems - Springer](https://link.springer.com/chapter/10.1007/978-3-642-82453-1_17)
- [STATEMATE: A Working Environment for the Development of Complex Reactive Systems](https://www.researchgate.net/publication/221554971_STATEMATE_A_Working_Environment_for_the_Development_of_Complex_Reactive_Systems)
- [The Temporal Logic of Reactive and Concurrent Systems: Specification - Amazon](https://www.amazon.com/Temporal-Logic-Reactive-Concurrent-Systems/dp/0387976647)

### Lustre/SCADE
- [Lustre (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Lustre_(programming_language))
- [The synchronous data flow programming language LUSTRE (PDF)](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Spring08/Papers/Halb91.pdf)
- [The Lustre Programming Language and Related Tools - Verimag](https://www-verimag.imag.fr/The-Lustre-Programming-Language-and)
- [Ansys SCADE Suite | Model-Based Design](https://www.ansys.com/products/embedded-software/ansys-scade-suite)
- [Your Guide To Implementing the DO-178C Standard - Ansys Blog](https://www.ansys.com/blog/your-guide-to-implementing-do-178c-standard)
- [DO-178C Compliant Software Development with Ansys SCADE - Webinar](https://www.ansys.com/resource-center/webinar/do-178c-compliant-software-development-with-ansys-scade)

### Esterel
- [Esterel - Wikipedia](https://en.wikipedia.org/wiki/Esterel)
- [The Esterel synchronous programming language (ScienceDirect)](https://www.sciencedirect.com/science/article/pii/016764239290005V)
- [The Esterel Language - INRIA](https://www-sop.inria.fr/meije/esterel/esterel-eng.html)
- [The Synchronous Language Esterel - Columbia University (PDF)](http://www.cs.columbia.edu/~sedwards/classes/2002/w4995-02/esterel.pdf)

### Signal
- [Designing Embedded Systems with the SIGNAL Programming Language](https://www.researchgate.net/publication/220690881_Designing_Embedded_Systems_with_the_SIGNAL_Programming_Language_Synchronous_Reactive_Specification)
- [Constructive Polychronous Systems - Springer](https://link.springer.com/chapter/10.1007/978-3-642-35722-0_24)
- [Polychronous Automata (HAL)](https://hal.science/hal-01240440/document)

### Reactive Manifesto
- [The Reactive Manifesto](https://www.reactivemanifesto.org/)
- [The Reactive Principles](https://www.reactiveprinciples.org/)
- [GitHub - reactivemanifesto/reactivemanifesto](https://github.com/reactivemanifesto/reactivemanifesto)
- [Reactive Systems in Java - Baeldung](https://www.baeldung.com/java-reactive-systems)

### Reactive Extensions (Rx)
- [ReactiveX](https://reactivex.io/)
- [ReactiveX - Wikipedia](https://en.wikipedia.org/wiki/ReactiveX)
- [ReactiveX - Observable](https://reactivex.io/documentation/observable.html)
- [Reactive Extensions for .NET Developers - Microsoft Learn](https://learn.microsoft.com/en-us/shows/on-dotnet/reactive-extensions-for-net-developers)

### 関数型リアクティブプログラミング (FRP)
- [Functional reactive programming - Wikipedia](https://en.wikipedia.org/wiki/Functional_reactive_programming)
- [Functional Reactive Programming: A Comprehensive Guide - AlgoCademy](https://algocademy.com/blog/functional-reactive-programming-a-comprehensive-guide-for-modern-developers/)
- [Functional reactive programming from first principles - ACM](https://dl.acm.org/doi/10.1145/349299.349331)
- [The Essence of FRP - begriffs](https://begriffs.com/posts/2015-07-22-essence-of-frp.html)
- [Conal Elliott - FRP](http://conal.net/blog/tag/frp)
- [Episode 9 - Conal Elliott on FRP and Denotational Design - The Haskell Cast](https://www.haskellcast.com/episode/009-conal-elliott-on-frp-and-denotational-design)

### 形式検証と時相論理
- [Temporal verification of reactive systems - safety - Semantic Scholar](https://www.semanticscholar.org/paper/Temporal-verification-of-reactive-systems-safety-Manna-Pnueli/ba6508eb538e5532c11c2cd80dca22beeefcf03d)
- [Temporal Verification of Reactive Systems: Safety - Springer](https://link.springer.com/book/10.1007/978-1-4612-4222-2)
- [Safety, Liveness and Fairness in Temporal Logic - ACM](https://dl.acm.org/doi/10.1007/BF01211865)
- [Applications of temporal logic to reactive systems - Springer](https://link.springer.com/chapter/10.1007/BFb0027047)

### 日本語リソース
- [リアクティブシステムが注目を集める理由 - Think IT](https://thinkit.co.jp/article/9185)
- [リアクティブ宣言 (日本語版)](https://www.reactivemanifesto.org/ja)
- [リアクティブシステムとは - Akkaによるリアクティブシステム開発ガイド](https://zenn.dev/j5ik2o/books/akka-book-e8771e80b20c32ed1840/viewer/02_about-reactive-system)
- [リアクティブ・システム - IBM Developer (日本語)](https://developer.ibm.com/jp/articles/reactive-systems-getting-started/)
- [リアクティブプログラミングの基本と応用 - オプスイン](https://ops-in.com/blog/%E3%83%AA%E3%82%A2%E3%82%AF%E3%83%86%E3%82%A3%E3%83%96%E3%83%97%E3%83%AD%E3%82%B0%E3%83%A9%E3%83%9F%E3%83%B3%E3%82%B0%E3%81%AE%E5%9F%BA%E6%9C%AC%E3%81%A8%E5%BF%9C%E7%94%A8/)
- [Chatwork、LINE、Netflixが進めるリアクティブシステム - @IT](https://atmarkit.itmedia.co.jp/ait/articles/1703/16/news023.html)
