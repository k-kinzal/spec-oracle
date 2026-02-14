# 時相論理（Temporal Logic）の基礎

## 1. はじめに

時相論理（Temporal Logic）は、時間との関連で問題を理解し表現するための形式論理体系である。古典的な命題論理や述語論理が真理値の静的な状態を扱うのに対し、時相論理は命題の真理値が時間に沿ってどのように変化するかを記述する。

時相論理は、並行システムやリアクティブシステムの仕様記述と検証において中心的な役割を果たしている。「要求が発生したら常にリソースへのアクセスがそのうちに承認される」「決して2つの要求を同時に承認してはならない」といった時間的制約を形式的に表現できる。

時相論理は様相論理（Modal Logic）の一種であり、命題論理に時間に関する様相演算子を追加したものと見なせる。本稿では、線形時相論理（LTL）、計算木論理（CTL）、CTL*、μ計算などの主要な時相論理とその応用について解説する。

## 2. 時相論理の歴史的背景

### 2.1 Pnueliの貢献

時相論理のコンピュータサイエンスへの応用は、Amir Pnueliの先駆的研究によって始まった。Pnueliは1977年の論文「The temporal logic of programs」において、プログラムの仕様記述と検証に時相論理を使用する統一的アプローチを提案した。

**Pnueliの主要貢献**：
- プログラムの振る舞い特性を記述する便利な形式言語として時相論理を特定
- 並列プログラムおよびより一般的なリアクティブシステムに適用
- 線形時相論理の証明システムを開発
- 有限状態システムの時相性質検証のためのモデル検査アルゴリズムを開発
- 順次プログラムと並列プログラムの両方に適用される統一的アプローチを提案
- イベントの時間依存性を基本概念とする時相推論を主要証明手法とした

**学術的影響**：
Pnueliは、プログラム仕様記述と検証への時相論理の導入、プログラムおよびシステム検証への顕著な貢献により、1996年のチューリング賞を受賞した。

### 2.2 モデル検査の誕生

1981年は、モデル検査の誕生年とされる。この年、Edmund M. ClarkeとE. Allen Emersonが米国で、Joseph Sifakisがフランスで独立に、後に高い成功を収めるモデル検査分野を創始する先駆的論文を発表した。

**CTLの開発**：
計算木論理（CTL）は、1981年にEdmund M. ClarkeとE. Allen Emersonによる論文「Design and Synthesis of Synchronization Skeletons Using Branching Time Temporal Logic」で初めて導入された。彼らは、並行システムの同期特性を仕様記述し合成するための分岐時間時相論理としてCTLを提案した。

**主要技術貢献**：
- EmersonとClarkeは、CTLのモデル検査問題を解く多項式時間アルゴリズムを与えた
- 1986年、Clarke、Emerson、A. Prasad Sistlaは「Automatic Verification of Finite-State Concurrent Systems Using Temporal Logic Specifications」において、CTLの効率的なモデル検査アルゴリズムを開発し、この問題がP完全であることを証明した
- これによりCTLは有限状態システムの自動検証の要となった

**学術的評価**：
Edmund M. Clarke、E. Allen Emerson、Joseph Sifakisは、CTLの理論的・実践的進歩を含むモデル検査への先駆的研究により、2007年のACM A.M.チューリング賞を受賞した。

## 3. 線形時相論理（LTL）

### 3.1 LTLの基本概念

線形時相論理（Linear Temporal Logic、LTL）は、時間に関する様相を持つ様相時相論理である。LTLでは、時間が線形である：トレースに沿って、任意の点は唯一の可能な未来を持つ。

**時間モデル**：
- 時間の流れは離散的な線形系列として見なされる
- 各時点で、唯一の実際の未来タイムラインが存在する
- 伝統的には現在時点から始まり、無限に未来へ進行すると定義される

**表現能力**：
LTLでは、ある条件が最終的に真となる、または別の事実が真になるまでその条件は真である、といった将来の出来事について論理式で表すことができる。

### 3.2 LTLの時相演算子

LTLは、時相様相演算子X（next）とU（until）から構築され、論理演算子と組み合わされる。

**基本演算子**：

1. **Next（X、次に）**：
   - Xφ：φは次の状態で成立しなければならない

2. **Until（U、～になるまで）**：
   - φ U ψ：ψが真になるまでφは真でなければならない

**派生演算子**：

3. **Eventually/Finally（F、◇、いつかは）**：
   - Fφ := true U φ
   - ◇φ：φはいつかは（未来のある時点で）真になる

4. **Always/Globally（G、□、いつも）**：
   - Gφ := ¬F¬φ
   - □φ：φは常に（すべての未来時点で）真である

5. **Weak Until（W）**：
   - φ W ψ：ψが成立するまでφは成立しなければならない
   - Uとの違いは、ψが決して検証される保証がないこと

### 3.3 LTLの実例

**安全性の例**：
```
□¬p
```
pは決して成立しない（pという「悪いこと」は決して起こらない）

**応答性の例**：
```
□(p → ◇q)
```
pが起こるとき、いつでもqが最終的に起こる（要求pに対して応答qがいつか返される）

**エレベータの仕様例**：
「エレベータが2階にいて、上向きになっていて、5階行きのボタンが押されたならば、5階に到着するまで上向きのままである」という仕様を時相論理で表現できる。

## 4. 計算木論理（CTL）

### 4.1 CTLの基本概念

計算木論理（Computation Tree Logic、CTL）は分岐時間論理であり、時間のモデルが木構造であることを意味する。未来は決定されておらず、未来には異なるパスがあり、そのいずれかが実現される可能性がある。

**時間モデル**：
- 時間は分岐する：実行に沿った任意の点は複数の可能な未来を持つ
- 状態遷移システムの計算木として表現される
- 各状態から複数の後続状態への遷移が可能

**LTLとの違い**：
- LTL：線形時間、単一のトレースに沿った性質
- CTL：分岐時間、複数のパスに関する性質

### 4.2 CTLのパス量化子と時相演算子

CTLでは、時相演算子の前に必ずパス量化子が付く。

**パス量化子**：
- **∀（A、All paths）**：すべてのパスで性質が成立
- **∃（E、Exists path）**：少なくとも1つのパスで性質が成立

**時相演算子**（パス量化子と組み合わせて使用）：
- **X（next）**：次の状態
- **F（eventually）**：いつかは
- **G（always）**：常に
- **U（until）**：～になるまで

**CTLの構文的制約**：
すべてのU（until）は即座に∀または∃で量化されなければならない。これにより、すべてのCTL式が純粋に状態に関する意味を持つ。

### 4.3 CTLの実例

**安全性の例**：
```
∀□¬p
```
すべてのパスでpは決して成立しない

**到達可能性の例**：
```
∃◇p
```
pが成立する状態に到達するパスが存在する

**可能性の例**：
```
∀□(∃◇p)
```
常にpに到達する可能性がある（LTLでは表現不可能）

## 5. LTLとCTLの表現力比較

### 5.1 比較不可能性

LTLとCTLは表現力の観点で比較不可能である。各論理には、他方では表現できない式が存在する。

**両方で表現可能な性質**：
- LTL式 □¬p と CTL式 ∀□¬p は同じ性質「pは決して成立しない」を表現
- LTL式 □(p → ◇q) と CTL式 ∀□(p → ∀◇q) は同じ性質「pが起こるときはいつでもqが最終的に起こる」を表現

### 5.2 CTLのみで表現可能

**例1：常に可能性がある**
```
∀□(∃◇p)
```
常に、実行中にある状態に到達する可能性がある（たとえ実際には決して到達しなくても）。この性質はLTLでは表現できない。

**例2：その他のCTL専用式**
- ∀◇(a ∧ ∀○a)
- ∀◇∀□a
- ∀□∃◇a

これらのCTL式に等価なLTL式は存在しない。

### 5.3 LTLのみで表現可能

**例：最終的に常に**
```
◇□p
```
最終的にpが常に成立する状態になる。

この性質はCTL式 ∀◇∀□p と等価ではない。さらに強い事実として、◇□pが表現する性質はいかなるCTL式でも表現できない。

### 5.4 CTL*による統合

CTL*は、CTLまたはLTLよりも厳密に表現力が高い。CTL*は、パス量化子と時相演算子の無制限な組み合わせを許すことで、この表現力のギャップを解決する。

## 6. CTL*とモデル検査の複雑性

### 6.1 CTL*の位置づけ

CTL*は、LTLとCTLの両方を包含する時相論理である。CTL*はパス量化子と時相演算子を自由に組み合わせることができ、CTLよりも表現力が高い。

**階層関係**：
- CTLはCTL*の厳密な断片であり、モデル検査が多項式時間で解決可能
- LTLもCTL*の断片である
- CTL*は両者を統合する

### 6.2 モデル検査の計算複雑性

**CTLのモデル検査**：
- P完全（多項式時間）
- 効率的なアルゴリズムが存在

**LTLのモデル検査**：
- PSPACE完全
- LTL式のサイズに対して指数時間を要する
- モデル検査アルゴリズムは時間 |M| · 2^O(|φ|) で実行される（Mはモデル、φはLTL式）

**実用的意義**：
モデル検査は、プログラムの活性性（liveness）と安全性（safety）性質を記述するのに有用な、最も広く使われた検証手法の一つである。

## 7. μ計算（Mu-Calculus）

### 7.1 μ計算の基本

様相μ計算（Modal μ-Calculus、Lμ）は、命題様相論理を最小不動点演算子μと最大不動点演算子νで拡張した不動点論理である。μ計算は時相論理のバックボーンと呼ばれることが多い。

**不動点演算子**：
- **μ（最小不動点演算子）**：最小不動点を表現
- **ν（最大不動点演算子）**：最大不動点を表現

### 7.2 表現力の階層

**μ計算の表現力**：
- LTL、CTL、CTL*を含む多くの時相論理をμ計算でエンコードできる
- μ計算の表現力は、一般的に使用されるすべての時相論理（LTL、CTL、CTL*）を超える
- 交代パリティ木オートマトンまたは木上の単項2階理論の双模倣閉包断片と等しい表現力を持つ

**CTL*のμ計算への翻訳**：
完全な分岐時間CTL*とその拡張ECTL*の様相μ計算への直接埋め込みが示されている。ただし、CTL*のすべての式が純粋に状態に関する意味を持つわけではないため、Lμのような純粋な状態ベース論理への翻訳は問題がある。

### 7.3 不動点交代階層

不動点交代の概念は、論理に関するいくつかの興味深い問題で役割を果たす。研究文献では「μ計算の交代深さ階層は二分木上で厳密である」などの結果が参照されている。

## 8. 安全性、活性、公平性

### 8.1 安全性（Safety）

安全性性質は、「悪いことが起こらない」ことを非形式的に述べる。

**定義**：
- 性質に違反する任意の単語は「悪い接頭辞」を持つ
- その接頭辞を持つ単語は性質を満たさない
- 性質が安全性ならば、有限の接頭辞を見るだけで悪いことが起こることを確信できる

**例**：
- 「PINが入力されない限り、現金が払い出されてはならない」（ATMの仕様）
- 「デッドロックが発生してはならない」
- 「p は決して成立しない」（□¬p）

### 8.2 活性（Liveness）

活性性質は、「良いことがいつかは起こる」ことを述べる。

**定義**：
- 性質が活性ならば、良いことが起こらないことを確信するには必然的に無限全体のトレースを見なければならない
- 有限の接頭辞だけでは違反を確定できない

**例**：
- 「プログラムは最終的に終了する」
- 並行計算において「すべてのプロセスは最終的にサービスされなければならない」
- 「要求が発生したら、応答がいつかは返される」（□(request → ◇response)）

### 8.3 公平性（Fairness）

公平性性質は、非現実的なトレースを排除するためにシステムに課される前提条件である。

**定義**：
- 技術的には、システムモデルの実行（パス）に対する条件
- 検証すべき性質ではないが、時相論理で表現可能

**例**：
- 「すべてのプロセスは無限回そのターンを得る」
- スケジューラの公平性：「すべての準備完了プロセスは最終的に実行される」

**モデル検査への影響**：
公平性制約は、モデル検査の際に考慮すべき実行パスを制限し、より現実的な検証を可能にする。

## 9. 時相論理の拡張と変種

### 9.1 実時間時相論理

**MTL（Metric Temporal Logic）**：
- 線形時相論理（LTL）の実時間拡張
- 時間区間を伴う時相演算子を導入
- MTL自体は決定不可能
- MITL（Metric Interval Temporal Logic）はMTLの変種で、時相区間の句読点を禁止（左境界と右境界が異なる必要）

**STL（Signal Temporal Logic）**：
- ハイブリッドシステム向けの連続時間・実数値版時相論理
- 形式仕様言語として提案された
- 車の加速度など実世界システムでよく現れる時系列に沿って変化する値をより厳密に仕様記述できる

**時刻付きオートマトンとの関係**：
- MTLやMITLの性質を時刻付きオートマトンに翻訳する技術が研究されている
- 有界変動性仮定の下で、完全なMTLを扱い、すべての未来演算子を含む時刻付きオートマトンの構築手法が提案されている

### 9.2 ハードウェア検証における時相論理

**SystemVerilog Assertions（SVA）**：
- SystemVerilogで提供されるアサーション機能
- ハードウェアの時相的性質を記述・検証

**PSL（Property Specification Language）**：
- IEEE標準のプロパティ仕様言語
- SVAと並んでアサーション言語の代表的な言語

**応用分野**：
- ハードウェアの仕様（プロパティ）の記述
- RTL（Register Transfer Level）テストベンチの開発
- 制約付きランダム検証
- 関数型カバレッジ

## 10. 時相論理の実用応用

### 10.1 モデル検査

**概要**：
モデル検査は、形式システムをアルゴリズム的に検証する手法である。ハードウェアやソフトウェアの設計から導出されたモデルが形式仕様を満足するかどうかを検証する。

**仕様記述**：
仕様は時相論理の論理式の形式で記述することが多い。特にLTLとCTLが広く使用される。

**技術**：
- LTLモデル検査：オートマトン理論に基づく手法
- CTLモデル検査：不動点計算に基づく効率的アルゴリズム
- 境界モデル検査：SATソルバを活用

### 10.2 制御工学への応用

時相論理仕様を満たす制御器の設計、移動ロボットのプランニング、電力システムの制御など、制御工学においても時相論理は重要な道具になりつつある。

**Signal Temporal Logic（STL）の活用**：
- 連続的な時間変化を扱う拡張
- 実世界のシステムでよく現れる時系列データの仕様記述に適している

### 10.3 ランタイム検証

**モニタリング**：
システムが仕様通りの振る舞いをしているかを実行時に確認する実行時検証において、線形時相論理（LTL）、Metric Temporal Logic（MTL）、Signal Temporal Logic（STL）といった時相論理が効率的に使用されている。

**時相論理モニタリングの調査**：
近年、時相論理のモニタリング技術に関する調査研究が進展しており、実用的なツールの開発が進んでいる。

### 10.4 並行システムの検証

**応用例**：
- 並行プログラムのデッドロック検出
- 相互排除プロトコルの正当性証明
- 分散アルゴリズムの活性保証
- 通信プロトコルの正当性検証

## 11. 時相論理による仕様記述の意義

### 11.1 形式性と厳密性

時相論理は、システムの時間的振る舞いを曖昧さなく厳密に記述する手段を提供する。自然言語による仕様では解釈の余地があるが、時相論理式は一意の数学的意味を持つ。

### 11.2 自動検証との親和性

時相論理で記述された仕様は、モデル検査などの自動検証ツールで直接処理できる。これにより、手作業による証明の誤りを回避し、大規模システムの検証を実現できる。

### 11.3 抽象化レベルの適切性

時相論理は、実装の詳細から離れた適切な抽象レベルでシステムの要求を記述できる。「何を達成すべきか（What）」を「どのように達成するか（How）」から分離できる。

### 11.4 安全性と活性の明確な区別

時相論理は、安全性性質（悪いことが起こらない）と活性性質（良いことがいつかは起こる）を明確に区別して記述できる。この区別は、システム検証において重要な役割を果たす。

## 12. 時相論理の限界と課題

### 12.1 表現力の制約

- LTLやCTLでは表現できない性質が存在する（例：文脈自由言語）
- より表現力の高い論理（CTL*、μ計算）は計算複雑性が高い
- 実用的には、表現力と決定可能性・複雑性のトレードオフが重要

### 12.2 状態空間爆発

モデル検査では、システムの状態空間が指数的に増大する状態空間爆発問題が生じる。並行システムでは特に深刻である。

**対策**：
- シンボリックモデル検査（BDD等）
- 部分順序削減
- 抽象化技術
- 境界モデル検査

### 12.3 学習曲線

時相論理の論理式は、形式手法に慣れていない技術者にとって直感的でない場合がある。仕様パターンや構造化された記述法による支援が重要である。

### 12.4 実時間性の扱い

標準的なLTL/CTLは実時間を直接扱えない。MTLやSTLなどの拡張が提案されているが、決定可能性や複雑性の問題がある。

## 13. まとめと今後の展望

時相論理は、並行システムやリアクティブシステムの仕様記述と検証のための強力な形式的枠組みを提供する。Pnueliの先駆的研究から始まり、Clarke、Emerson、Sifakisらによるモデル検査の確立を経て、今日では形式手法の中心的技術となっている。

**主要な貢献**：
- **形式的仕様記述言語**：システムの時間的振る舞いを厳密に記述
- **自動検証技術**：モデル検査による大規模システムの検証
- **安全性と活性の明確化**：性質の分類と検証手法の体系化
- **実用ツールの発展**：SPIN、NuSMV、UPPAAL等の成功

**表現力の階層**：
- 基本：LTL（線形時間）、CTL（分岐時間）
- 統合：CTL*（両者を包含）
- 最強：μ計算（不動点演算子による表現力）

**応用分野の拡大**：
- ハードウェア検証（SVA、PSL）
- ソフトウェア検証（並行プログラム、分散システム）
- 制御工学（ロボティクス、電力システム）
- ランタイム検証（モニタリング）

**今後の課題**：
- 実時間システムの検証（MTL、STL、時刻付きオートマトン）
- 確率的システムの検証（PCTL、確率的モデル検査）
- スケーラビリティの向上（状態空間爆発への対処）
- 仕様記述の容易性（パターン、ドメイン特化言語）
- AI/機械学習との融合（仕様マイニング、学習ベース検証）

時相論理は、「仕様とは何か」という根本的な問いに対して、時間的側面を形式的に扱う一つの明確な答えを提供している。システムの振る舞いを時間軸に沿って厳密に記述し、その正当性を自動的に検証できることは、現代のソフトウェア・ハードウェアエンジニアリングにおいて不可欠な能力となっている。

## 参考文献

- [Linear temporal logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_temporal_logic)
- [Computation tree logic - Wikipedia](https://en.wikipedia.org/wiki/Computation_tree_logic)
- [時相論理 - Wikipedia](https://ja.wikipedia.org/wiki/%E6%99%82%E7%9B%B8%E8%AB%96%E7%90%86)
- [線形時相論理 - Wikipedia](https://ja.wikipedia.org/wiki/%E7%B7%9A%E5%BD%A2%E6%99%82%E7%9B%B8%E8%AB%96%E7%90%86)
- [The temporal logic of programs | Semantic Scholar](https://www.semanticscholar.org/paper/The-temporal-logic-of-programs-Pnueli/c3fcf116688ffc322b6c78915e1896c7daeab6b0)
- [Amir Pnueli | Formal Verification, Model Checking & Temporal Logic | Britannica](https://www.britannica.com/biography/Amir-Pnueli)
- [The Birth of Model Checking (PDF)](https://www.cs.cmu.edu/~emc/15817-f08/lectures/lec-01_4up.pdf)
- [Model checking: algorithmic verification and debugging - ACM](https://dl.acm.org/doi/10.1145/1592761.1592781)
- [Safety, liveness and fairness in temporal logic - Formal Aspects of Computing](https://link.springer.com/article/10.1007/BF01211865)
- [Linear time property - Wikipedia](https://en.wikipedia.org/wiki/Linear_time_property)
- [Temporal Logic (Stanford Encyclopedia of Philosophy)](https://plato.stanford.edu/entries/logic-temporal/)
- [Common Temporal Logic Constructs for CTL and LTL](https://www.cl.cam.ac.uk/~djg11/pubs/temporal.html)
- [CTL* - Wikipedia](https://en.wikipedia.org/wiki/CTL*)
- [CS 512: Model-Checking: Comparison of LTL, CTL and CTL* (PDF)](https://www.cs.bu.edu/faculty/kfoury/UNI-Teaching/CS512-Spring18/Lecture/HD15.compare-LTL-CTL-CTL-star.pdf)
- [Modal μ-calculus - Wikipedia](https://en.wikipedia.org/wiki/Modal_%CE%BC-calculus)
- [The Modal Mu-Calculus - Cambridge](https://www.cambridge.org/core/books/abs/temporal-logics-in-computer-science/modal-mucalculus/B7FFF5B1DB48FE4DBF08971377271F49)
- [The mu-calculus and model-checking (PDF)](https://www.labri.fr/perso/igw/Papers/igw-mu.pdf)
- [CTL* and ECTL* as fragments of the modal μ-calculus](https://www.researchgate.net/publication/225529961_CTL_and_ECTL_as_fragments_of_the_modal_m-calculus)
- [時相論理 (Temporal Logic) のモニタリングの調査](https://makenowjust-labs.github.io/blog/post/2024-03-09-temporal-logic-monitoring/)
- [時相論理(temporal logic) (PDF)](http://www.cs.tsukuba.ac.jp/~mizutani/under_grad/programtheory/2014/2014-09.pdf)
- [From Real-time Logic to Timed Automata - ACM](https://dl.acm.org/doi/10.1145/3286976)
- [STL Model Checking of Continuous and Hybrid Systems (PDF)](https://mediatum.ub.tum.de/doc/1430235/124621.pdf)
- [Bounded Model Checking for Metric Temporal Logic Properties](https://www.mdpi.com/1424-8220/22/23/9552)
- [Specification and Verification using Temporal Logics (PDF)](https://inria.hal.science/hal-00776601v1/document)
- [The Complexity of Temporal Logic Model Checking (PDF)](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/Sch-aiml02.pdf)
- [Translating a Continuous-Time Temporal Logic into Timed Automata](https://link.springer.com/chapter/10.1007/978-3-540-40018-9_21)
