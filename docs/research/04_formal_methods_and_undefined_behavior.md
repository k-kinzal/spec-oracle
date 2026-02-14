# 形式手法における未定義動作と暗黙的仕様

## 1. 概要

形式手法における未定義動作（undefined behavior）、暗黙的仕様、非決定性の問題について調査した結果をまとめる。これらの概念は、仕様と実装のギャップを理解する上で重要である。

## 2. 形式手法における未定義動作の取り扱い

### 2.1 Hoare論理と事前条件

Hoare論理は、コマンドの実行前後の状態に関するアサーション（表明）を用いてプログラムの正当性を記述する体系である[1]。基本的な形式は以下の通り：

```
{P} c {Q}
```

- P: 事前条件（precondition）
- c: コマンド
- Q: 事後条件（postcondition）

この意味は「コマンドcが事前条件Pを満たす状態で開始され、cが最終的に終了する場合、その最終状態は事後条件Qを満たす」である[1][2]。

**重要な点**：Hoare論理における「終了（termination）」は、無限ループがないことを意味するが、必ずしも実装上の制限違反（例：ゼロ除算）によるプログラムの異常停止がないことを保証するわけではない[1]。Hoareの1969年の論文では、より狭い意味での終了（実装制限違反がないこと）も含まれていた[1]。

### 2.2 弱最弱事前条件（Weakest Precondition）

Dijkstraの弱最弱事前条件（weakest precondition, wp）は、プログラムSが事後条件Rを満たす状態で終了することを保証する状態の集合を特徴付ける述語である[3][4]。

- **wp(S, R)**: 完全正当性（termination含む）のための弱最弱事前条件
- **wlp(S, R)**: 弱最弱自由事前条件（weakest liberal precondition、終了を無視）

**未定義式の扱い**：弱最弱事前条件の計算において、式Eは暗黙的に「完全に定義された、終了する、副作用のない純粋な式」として扱われる[4]。式が未定義の場合、標準的な弱最弱事前条件の規則を適用できない[4]。

### 2.3 部分関数 vs 全関数アプローチ

形式仕様において、未定義動作を扱う2つの主要なアプローチがある：

#### 部分関数（Partial Function）

部分関数は、定義域のすべての要素に対して定義されているわけではない関数である[5][6]。

- **定義**：集合XからYへの部分関数は、XのサブセットS（場合によってはX全体）からYへの関数である
- **記法**：f(a)↓ は「aがfの定義域に含まれる」ことを示し、f(a)↑ は「f(a)が未定義」であることを示す[6]
- **未定義の意味**：定義域外の値xに対してf(x)を適用した場合、その結果は未定義である[6]

#### 全関数（Total Function）

全関数は、定義域のすべての要素に対して定義されている関数である[5][6]。

- 定義域のすべての要素に対して有効な出力を返すことを保証
- 関数型プログラミングでは、プログラムがクラッシュしたり予期しない結果を生成したりしないため、全関数が望ましい[6]

#### 未定義の扱い方

定義域外の値に関数を適用することの意味については、複数のアプローチがある[6]：

1. **任意の値**：f(x)を定義域外のxに対して何か任意のものとみなす
2. **明示的な値**：定義域外の引数に対して明示的な値を指定する
3. **特殊な論理**：IMPSシステムのように、特定の項が未定義であることを許す特殊な論理を持つ（これは従来の論理に特別な「未定義」要素を追加することとほぼ同じ）[6]

### 2.4 VDMとZ仕様における部分関数と事前条件

形式仕様言語VDM（Vienna Development Method）とZでは、部分関数と事前条件の扱いが異なる[7][8]：

#### VDMのアプローチ

- 明示的な事前条件を使用する[7]
- 不変条件が維持されることを保証するため、制約を事前条件に明示的に含める必要がある[7]
- 事前条件を満たさない入力で関数が呼ばれた場合、結果は未定義である（終了さえも保証されない）[8]
- 事前条件と事後条件が契約を形成し、関数を実装する任意のプログラムがこの契約を満たす必要がある[8]

#### Zのアプローチ

- 制約を通常は暗黙的に残す[7]
- 操作の事前条件を計算することでエラー条件をチェックでき、完全な操作の事前条件が真になるようにエラーを処理する[8]

## 3. CとC++における未定義動作

### 3.1 定義

C++14標準（ISO/IEC 14882:2014）のセクション1.9では、セマンティック記述においてパラメータ化された非決定的抽象機械を定義している[9][10]。

**未定義動作**：プログラミング言語仕様が何も要求を課さないコードが含まれているか実行されている場合に発生する動作[10]。標準は実装に対して絶対的に何の要件も課さない[9]。

### 3.2 一般的な例

未定義動作の例[9][10]：

- データ競合
- 配列境界外のメモリアクセス
- 符号付き整数のオーバーフロー
- ヌルポインタの参照外し
- 中間のシーケンスポイントなしでの同じスカラーの複数回の変更
- 異なる型のポインタを通じたオブジェクトへのアクセス

### 3.3 他の動作との区別

C/C++では、未定義動作は以下の概念と区別される[9][10]：

- **未規定動作（Unspecified behavior）**：言語仕様が結果を規定しないが、プログラムの動作自体は有効
- **処理系定義動作（Implementation-defined behavior）**：プラットフォームの別のコンポーネントのドキュメントに委ねられる動作

### 3.4 形式的な結果

実装は未定義動作を診断する必要がない（多くの単純な状況では診断される）[10]。コンパイルされたプログラムは意味のあることを何もする必要がない[10]。定義により、ランタイムは未定義動作が決して起こらないと仮定できる。したがって、いくつかの無効な条件はチェックする必要がない[10]。

## 4. RFCとIETF標準における仕様の隙間

### 4.1 仕様ギャップの実例

ネットワークプロトコルは、通常、散文のドキュメントに疑似コード、ヘッダー記述、状態機械、メッセージシーケンスチャートが注釈された仕様によって定義される[11][12]。

**問題点**：

- 社会的プロセスとRFCは、プロトコル記述に曖昧さとギャップを残すことが多く、深刻なセキュリティ脆弱性を引き起こす可能性がある[11][12]
- 参照実装は仕様よりも頻繁に更新されるため、多くのプロトコルの事実上の仕様として機能する[12]
- 3GPP仕様は意図的に曖昧であることが多く、通常は参照実装を含まないため、実装の不一致が悪化する[12]

### 4.2 RS232の例

歴史的な例として、シリアル通信のRS232標準は非常に仕様が不足していたため、2つのシリアルケーブルが同じであることはほとんどないように見えた[13]。

### 4.3 実装依存動作

RFCは明示的に実装依存動作を許可する場合がある[13]：

- 「実装は未指定アドレスに対して実装依存のセマンティクスを使用する可能性がある」
- 「適切なアルゴリズムの選択はリンクと実装に依存する」

### 4.4 RFC 2119と仕様言語

RFC 2119は要求レベルを示すキーワードに関するガイダンスを提供している[13]。これらの用語は、相互運用のために実際に必要な場合、または害を引き起こす可能性のある動作を制限する場合にのみ使用する必要がある[13]。実装者に特定の方法を押し付けるために使用してはならない（その方法が相互運用性に必要でない場合）[13]。

### 4.5 仕様のアンダースペシフィケーション（過小仕様化）

**EHRシステムの例**：EHRシステムにおいて、標準が同時に過剰仕様化とアンダースペシフィケーション（過小仕様化）されているため、相互運用性の達成が困難になっている[14]。

**機械学習の例**：機械学習においてアンダースペシフィケーションとは、MLモデル構築時に実務者が念頭に置いている要件と、MLパイプラインによって実際に強制される要件の間のギャップを指す[15][16]。返されるモデルは、ランダム初期化シード、データ順序、ハードウェアなど、実装における任意の選択に依存する特性を持つ可能性がある[15][16]。

## 5. 非決定性（Nondeterminism）の形式的定義

### 5.1 天使的非決定性（Angelic Nondeterminism）

天使的非決定性は、特定の選択が常に望ましい結果を支持すると宣言される非決定的アルゴリズムの実行である（その結果が可能な場合）[17][18]。

- 「天使的」という用語は、天使が慈悲深く全知の神に代わって行動するというキリスト教の宗教的慣習に由来する[17]
- 選択の天使的性質は、可能な限り失敗を避ける性質に関係する[17]

### 5.2 悪魔的非決定性（Demonic Nondeterminism）

悪魔的非決定性は、すべての選択が非終了を支持して行われる非決定的プログラムの実行を記述する[19][20]。

- 制御できない既存のコンポーネント内の非決定性は悪魔的非決定性と呼ばれる[19]

### 5.3 ゲーム理論的解釈

- 悪魔的選択は対戦相手によって行われる動き
- 天使的選択は我々の動き
- 組み合わされた仕様が正しいのは、対戦相手が何をしても望ましい目標を達成できるような動きができる場合である[19]

### 5.4 形式的モデリングにおける役割

システムの形式的モデリングにおいて、悪魔的および天使的非決定性は抽象化メカニズムとして基本的な役割を果たす[20]。二項多重関係は、天使的および悪魔的の両方の種類の非決定性をモデル化できる[20]。

### 5.5 非決定性 vs 未定義

**重要な区別**：非決定性は「仕様を決めていない」こととは異なる。非決定性は仕様において明示的に許可された選択の範囲を意味するが、未定義は仕様が何も述べていない（または意図的に曖昧にしている）状況を指す。

## 6. 暗黙的仕様の発生メカニズム

### 6.1 暗黙的仕様とは

暗黙的仕様は、明示的に文書化されていないが、言語、実行基盤、または実装によって暗黙的に想定されている要件や制約である[21][22]。

### 6.2 隠れた仮定の種類

ソフトウェアシステムにおいて、プログラムコードのほぼすべての行と形式モデルのすべてのエンティティには、隠れた仮定が伴う[22]：

1. **サイレント条件**：レビュアーが、開発者が条件を常に真、常に偽、または無関係と期待しているかどうかを容易に判断できない場所
2. **固定パラメータと初期値**：値の選択に関する明白な仮定と、値が固定されすべてのケースで等しく適用されるという暗黙的な仮定の両方を表す
3. **暗黙的要件**：まったく述べられていないが、言語または実行基盤によって暗示される要件[23]

### 6.3 ソフトwareAPIにおける暗黙的契約

TensorFlow、Scikit-learn、PyTorchなどの機械学習ライブラリにおけるバグの大部分は、暗黙的契約の違反によって説明される[21]。

- APIの統合は、暗黙的な「契約」（文書化されていない使用プロトコル）を通じて重要な信頼性の課題を導入する
- これらが違反されると、ランタイムエラーからサイレント論理バグまでの範囲の障害が発生する[21]
- Stack Overflowからの413の非形式的仕様の分析により、ほとんどのML API障害は暗黙的要件に関する違反された仮定に起因することが明らかになった[21]

### 6.4 テストにおける暗黙的要件

暗黙的要件は、明示的にキャプチャされなかったがユーザーが期待するものである[23]：

- パフォーマンス
- 使いやすさ
- 可用性
- セキュリティ

### 6.5 創発的動作と暗黙的仕様

複雑なシステムにおいて、暗黙的な仕様のギャップは予期しない創発的動作につながる可能性がある[24][25]：

- **創発**：複雑なエンティティが、その部分が単独では持たない性質や動作を持ち、より広い全体で相互作用する場合にのみ現れる現象[24]
- **創発効果の形式的定義**：グローバルな固有の仕様（真の仕様）とそのローカル近似（異なる報酬コンポーネントや観察の構成など）の間の不一致を特定することで、創発効果を形式的に定義できる[25]
- 2つの仕様の盲点が重複すると、対象のコンポーネントが新しい方法で相互作用する可能性がある[25]

### 6.6 スウォームロボティクスにおける創発的動作の仕様化

スウォームロボティクスの特徴は、個々のロボットの低レベル動作の観点から全体的な創発的なスウォーム動作を指定することが非常に困難であることである[26]。しかし、スウォームロボティクスが実験室から現実世界のエンジニアリング実現に移行するためには、そのような仕様が必要である[26]。

時相論理を使用して、ロボットスウォームの創発的動作を形式的に指定し、場合によっては証明することができる[26]。

## 7. 完全な仕様 vs 不完全な仕様

### 7.1 不完全な仕様の定義

形式仕様言語が、システム仕様で特定されたまたは暗示されたすべての重要な動作特性を指定できない場合、その仕様は定義により不完全である[27]。

### 7.2 ロバストネスと不完全性

ロバストネス基準は、すべての状態から常に1つの遷移を取ることができることを保証するが、環境に関するすべての仮定が指定されていること、または環境が生成できるすべての可能な入力条件に対して定義された応答があることを保証するものではない[27]。

タイミングと負荷の仮定は特に重要であり、要件仕様から省略されたり不完全に残されたりすることが多い[27]。

### 7.3 形式仕様化のメリット

形式的に仕様化する過程で、エンジニアまたは設計者はモデリング言語を使用してシステムを厳密に定義する。通常、形式的な数学的構文とセマンティクスを使用して、不正確さと曖昧さを排除する[28]。

仕様を形式化するプロセスは、形式的定義が考慮される前に元々存在していた不完全性を発見するのに役立っている[28]。

### 7.4 演繹的 vs 帰納的アプローチ

- **演繹的合成アプローチ**：プログラムの完全な形式仕様に依存する
- **帰納的アプローチ**：例から仕様を推論する[28]

## 8. 結論

形式手法における未定義動作、暗黙的仕様、非決定性の問題は、以下のように整理できる：

### 8.1 未定義動作の階層

1. **形式仕様レベル**：
   - 事前条件外の入力：部分関数アプローチでは明示的に未定義
   - 全関数アプローチでは、すべての入力に対して何らかの動作を定義

2. **実装レベル**：
   - C/C++のundefined behavior：仕様が何も要求しない
   - Implementation-defined：実装が定義する
   - Unspecified：複数の有効な選択肢がある

3. **プロトコル/標準レベル**：
   - Underspecification：仕様の隙間
   - 参照実装が事実上の標準になる

### 8.2 暗黙的仕様の生成メカニズム

1. **不完全な形式化**：すべての重要な特性を仕様化できない
2. **隠れた仮定**：言語、実行基盤、または実装に暗黙的に含まれる
3. **創発的動作**：コンポーネント間の相互作用から生じる予期しない動作
4. **仕様ギャップ**：意図的または非意図的な曖昧さ

### 8.3 非決定性と未定義の区別

- **非決定性**：仕様において明示的に許可された選択の範囲
  - 天使的：望ましい結果を支持
  - 悪魔的：制御不能な選択
- **未定義**：仕様が何も述べていない状況
  - 仕様の外側の動作
  - 実装の自由度（または危険性）

### 8.4 実践的含意

形式手法を用いても、以下の理由で未定義動作や暗黙的仕様を完全に排除することは困難である：

1. 完全な仕様を書くことの複雑さ
2. 相互運用性と実装の自由度のバランス
3. 創発的動作の予測不可能性
4. 社会的・技術的プロセスの限界

したがって、形式手法の適用においては、これらの限界を認識し、重要な性質に焦点を当てた仕様化、テスト、検証の組み合わせが必要である。

## 参考文献

1. [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
2. [Hoare: Hoare Logic, Part I - Software Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)
3. [Predicate transformer semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
4. [Weakest Precondition - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/weakest-precondition)
5. [Partial function - Wikipedia](https://en.wikipedia.org/wiki/Partial_function)
6. [Partial functions and undefined terms - rbjones.com](https://www.rbjones.com/rbjpub/logic/jrh0113.htm)
7. [VDM and Z: A Comparative Case Study](https://staff.itee.uq.edu.au/ianh/Papers/ndb.pdf)
8. [Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)
9. [Undefined behavior - cppreference.com](http://en.cppreference.com/w/cpp/language/ub.html)
10. [Undefined behavior - Wikipedia](https://en.wikipedia.org/wiki/Undefined_behavior)
11. [It Takes a Village: Bridging the Gaps between Current and Formal Specifications for Protocols - ACM](https://cacm.acm.org/research/it-takes-a-village-bridging-the-gaps-between-current-and-formal-specifications-for-protocols/)
12. [It Takes a Village: Bridging the Gaps between Current and Formal Specifications for Protocols - arXiv](https://arxiv.org/html/2509.13208)
13. [RFC 2119 - Key words for use in RFCs to Indicate Requirement Levels](https://datatracker.ietf.org/doc/html/rfc2119)
14. [The Perils of Over Specification and Underspecification in EHR Systems](https://www.physicianspractice.com/view/perils-over-specification-and-underspecification-ehr-systems)
15. [How Underspecification Presents Challenges for Machine Learning - Google Research](https://research.google/blog/how-underspecification-presents-challenges-for-machine-learning/)
16. [How Underspecification Presents Challenges for Machine Learning - Google Research Blog](https://blog.research.google/2021/10/how-underspecification-presents.html?m=1)
17. [Angelic non-determinism - Wikipedia](https://en.wikipedia.org/wiki/Angelic_non-determinism)
18. [Angelic nondeterminism - PLS Lab](https://www.pls-lab.org/en/Angelic_nondeterminism)
19. [Demonic nondeterminism - PLS Lab](https://www.pls-lab.org/en/Demonic_nondeterminism)
20. [Demonic non-determinism - Wikipedia](https://en.wikipedia.org/wiki/Demonic_non-determinism)
21. [Contracts for Large Language Model APIs](https://tanzimhromel.com/assets/pdf/llm-api-contracts.pdf)
22. [Toward Methodical Discovery and Handling of Hidden Assumptions in Complex Systems and Models](https://arxiv.org/html/2312.16507v1)
23. [3 Types of Requirements for Testing - StickyMinds](https://www.stickyminds.com/article/3-types-requirements-testing)
24. [Emergence - Wikipedia](https://en.wikipedia.org/wiki/Emergence)
25. [Emergence in Multi-Agent Systems: A Safety Perspective](https://arxiv.org/html/2408.04514v1)
26. [On formal specification of emergent behaviours in swarm robotic systems - University of Manchester](https://research.manchester.ac.uk/en/publications/on-formal-specification-of-emergent-behaviours-in-swarm-robotic-s/)
27. [Completeness in Formal Specification Language Design for Process-Control Systems](http://sunnyday.mit.edu/papers/completeness.pdf)
28. [Formal specification - Wikipedia](https://en.wikipedia.org/wiki/Formal_specification)
