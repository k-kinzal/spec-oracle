# 分離論理（Separation Logic）

## 1. はじめに

分離論理（Separation Logic）は、ホーア論理の拡張であり、共有可変データ構造を扱うプログラムを推論するための論理である。John C. Reynolds、Peter O'Hearn、Samin Ishtiaq、Hongseok Yangにより開発され、Rod Burstallの初期研究に基づいている。

分離論理の最大の特徴は、**局所推論（local reasoning）**を可能にすることである。これにより、プログラムコンポーネントの仕様と証明は、そのコンポーネントが実際に使用するメモリの部分のみに言及し、システムの全体的な大域状態には言及しない。この局所性の原理により、大規模なプログラムの検証が実用的になる。

分離論理は、2016年のゲーデル賞をO'HearnとBrookesが並行分離論理（Concurrent Separation Logic）の発明により受賞するなど、学術的にも高く評価されている。また、Facebook Inferなどの産業ツールで実用化されており、理論と実践の両面で成功を収めている形式手法である。

## 2. 分離論理の基礎概念

### 2.1 ホーア論理との関係

分離論理は、ホーア論理の基礎論理を房論理（bunched logic）に変更したものである。房論理は線形論理のようなリソース論理の仲間である。

**房論理の結合子**：
- ∧（通常の論理積）
- ∨（通常の論理和）
- →（通常の含意）
- ✱（分離接続子、separating conjunction）
- -∗（分離含意、separating implication）

最初の3つは直観主義論理そのままであり、✱と-∗がリソース的な結合子である。

### 2.2 分離接続子（Separating Conjunction）

**記法**：A ∗ B または A ** B

**意味**：
分離接続子 A ∗ B は、AとBが独立したメモリ領域に対して成り立つことを主張する。より正確には、ヒープを2つの分離された部分に分割でき、一方でAが成り立ち、もう一方でBが成り立つことを意味する。

**読み方**：
「and separately」と読む。日本語では「分離して〜かつ〜」。

**エイリアシングの排除**：
Aで言及しているポインタと、Bで言及しているポインタが指しているヒープ領域が分離されている（エイリアシングがない）ことを表す。

### 2.3 ポイントツー表明（Points-to Assertion）

**記法**：x ↦ v

**意味**：
ポインタ変数xが、値vが格納されているメモリ位置のアドレスを保持していることを表す（より簡潔には、xがvを指している）。

**シングルトンヒープ**：
x ↦ v は、xが指す単一のメモリセルのみから成るヒープを表す。

### 2.4 空ヒープ（Empty Heap）

**記法**：emp

**意味**：
ヒープが空であること、すなわち割り当てられたメモリセルが存在しないことを表す。

### 2.5 分離含意（Separating Implication）

**記法**：A -∗ B

**意味**：
現在のヒープに、Aを満たすヒープを追加すると、結果として得られるヒープがBを満たすことを表す。

**魔法の杖（Magic Wand）**：
しばしば「魔法の杖」と呼ばれる。

## 3. フレームルール（Frame Rule）

### 3.1 フレームルールの定義

フレームルールは、分離論理の中心的な推論規則であり、局所推論を可能にする。

**形式**：
```
{P} C {Q}
──────────────────
{P ∗ R} C {Q ∗ R}
```

ただし、Cが変更しない変数をRが参照していない場合（変数に関する制約）。

### 3.2 フレームルールの意義

**局所推論の実現**：
フレームルールにより、プログラムコンポーネントが実際に使用する変数とヒープセル（O'Hearnが「フットプリント」と呼ぶ）のみを含む局所仕様を、コードによって変更または変更されないヒープセルに関する任意の述語を追加することで拡張できる。

**コンパクトな証明**：
命令型プログラムのより簡潔な証明と仕様を可能にする。なぜなら、プログラムコンポーネントが実際に使用する可能性のあるメモリ部分のみに集中でき、システムの全体的な大域状態に集中する必要がないからである。

**合成性**：
プログラム部分の証明を合成することができ、フットプリント外の領域を無視できる。

## 4. ヒープの局所推論

### 4.1 メモリ権限とヒープ分割

分離論理では、房論理の命題を「メモリ権限が満たすべき条件」の記述に使う。メモリ権限Mを独立した2つの権限M1、M2に分割して、それぞれが命題を満たすようにできる。

**ヒープの構造の反映**：
分離論理は述語計算を新しい論理結合子（空ヒープ emp、シングルトンヒープ p ↦ v、分離接続子 H1 ∗ H2）で拡張し、表明の構造が基礎となるヒープの構造を反映するようにしている。

### 4.2 局所性の原理

**メモリアクセスの限定**：
局所推論の原理により、コードは到達不可能なメモリに影響を与えたり、影響を受けたりすることができないことが保証される。

**フットプリントによる限定**：
分離論理は、複雑なヒープ操作プログラムを検証するために設計されたホーア論理の変種であり、その力は、証明がメモリアクセスが仕様によって画定されたフットプリントに限定されていることを主張しなければならない状態に関する局所推論から生まれる。

### 4.3 インプレース推論

**ポインタ操作の公理化**：
ポインタ操作の公理化により、ヒープ更新の操作的局所性を反映して、前提条件から事後条件に渡る際に、式の一部がインプレースで更新されるインプレース推論がサポートされる。

## 5. 並行分離論理（Concurrent Separation Logic）

### 5.1 並行性への拡張

並行分離論理は、分離論理を並行プログラムに拡張したものである。Stephen BrookesとPeter O'Hearnにより開発された。

**2016年ゲーデル賞**：
O'HearnとBrookesは、並行分離論理の発明により2016年のゲーデル賞を共同受賞した。

### 5.2 並行プログラムの推論

並行分離論理は、共有可変状態を持つ並行プログラムの安全性を推論するための論理として使用できる。また、論理関係における論理として、型システムやデータ抽象化などについて推論するためにも使用できる。

## 6. Iris: 高階並行分離論理フレームワーク

### 6.1 Irisの概要

Irisは、高階並行分離論理の汎用フレームワークであり、Rocq証明支援系（旧Coq）で実装・検証されている。

**認識**：
Irisは、2023年のアロンゾ・チャーチ賞を「論理と計算への卓越した貢献」により受賞した。

### 6.2 Irisの応用

**広範な検証プロジェクト**：
Irisは、Coq証明支援系で実装され、非常に効果的に広範な検証プロジェクトに展開されている。

**用途**：
- 並行プログラムの安全性推論
- 論理関係における論理
- 型システムの推論
- データ抽象化の推論

### 6.3 Irisの特徴

**モジュラーな基盤**：
Irisは、高階並行分離論理のためのモジュラーな基盤を提供する。

**検証された実装**：
Rocq/Coqで実装され、形式的に検証されている。

## 7. メモリ安全性の仕様と証明

### 7.1 メモリ安全性の定義

**メモリ安全性の意味**：
局所推論の原理により、コードは到達不可能なメモリに影響を与えたり、影響を受けたりすることができない。分離論理のバリアントは、メモリ フットプリントの外部の領域を無視しながら証明を合成することを具現化するフレームルールを生成する。

### 7.2 分離論理による検証

**メモリ安全性エラーの検出**：
分離論理を使用した自動プログラム解析ツールは、通常、制限されたクラスのバグ（メモリ安全性エラーなど）を探すか、それらの不在を証明しようとする。

**関数的正当性の証明**：
対話的証明アプローチは、定理証明器（RocqやHOLなど）への分離論理の埋め込みを使用して行われ、より多くの人間の努力を必要とするが、関数的正当性まで深い性質を証明する。

### 7.3 最近の応用

**Quiver**：
Quiverは、関数的正当性仕様を分離論理で推論しながら、同時にそれらが正しいことを基礎的に検証する最初の技術である。

**PulseParse**：
PulseParse は、メモリ安全性、関数的正当性、非可鍛性の形式的証明を伴う分離論理で実装されている。

## 8. 実用ツールと産業応用

### 8.1 Facebook Infer

**概要**：
Facebook Inferは、Facebook がモバイルコードを出荷する前にバグを特定するために使用する静的プログラム解析器である。

**技術基盤**：
Inferは、分離論理と双方向帰納推論（bi-abduction）の2つの技術を使用する。双方向帰納推論は、局所推論に関する重要なアイデアを自動化する分離論理の論理推論の形式である。

**応用範囲**：
- Facebook の主要な Android および iOS アプリ（10億人以上が使用）
- Facebook Messenger
- Instagram
- その他、Spotify、Uber、WhatsApp、Marks and Spencer、Skyなどでも使用

**検出バグ**：
現在、解析器は、ヌルポインタアクセス、リソースおよびメモリリークによって引き起こされる問題を報告し、これらはアプリクラッシュの大部分を引き起こす。

**毎日の使用**：
Facebook では、Inferは毎日数百万行のコードを検証するために使用されている。

### 8.2 VeriFast

**概要**：
VeriFastは、分離論理で注釈付けされた前提条件と事後条件を持つ、単一スレッドおよびマルチスレッドのC、Rust、Javaプログラムの正当性特性のモジュラーな形式検証のためのツールの研究プロトタイプである。

**検証手法**：
VeriFastは、シンボリック実行に基づく分離論理検証器である。

**必要な注釈**：
プログラムには、関数/メソッドの前提条件と事後条件、ループ不変条件、およびゴースト宣言（データ構造のレイアウトを指定する分離論理述語の定義や、述語を畳んだり展開したりするためのゴーストコマンドなど）で注釈を付ける必要がある。

**最近の発展**：
VeriFastの分離論理は、細粒度並行プログラムのモジュラー検証のための「later」なしの論理である。

### 8.3 Viper

**概要**：
Viperツールチェーンは、可変状態を持つ順次および並行プログラムの検証技術を簡単に実装できるように設計されている。

**パーミッションベースの推論**：
分離論理のスタイルで、パーミッションまたは所有権を使用してプログラムの状態について推論するためのネイティブサポートを提供する。

**バックエンド検証器**：
Viperは、シンボリック実行に基づくものと、検証条件生成に基づくものの2つのバックエンド検証器を提供する。

**表明論理**：
サポートされている表明論理は、暗黙動的フレーム（implicit dynamic frames）の変種であり、分離論理を含む様々な推論パラダイムをエンコードするために使用できる。

**翻訳的検証器の基盤**：
研究により、Viperの要素を持つコア中間検証言語がインスタンス化され、2つのViperバックエンドと並行分離論理のフロントエンドに接続されている。

### 8.4 その他のツール

**Gillian**：
JavaScriptとCのための実世界検証を提供する合成的シンボリック実行ツール。

**CN**：
C言語のための検証ツール。

**Infer-Pulse**：
Facebookが開発した検証ツールの拡張版。

**共通特徴**：
複数の成功した合成的シンボリック実行ツールとプラットフォームが、合成的検証のために分離論理を活用している。

## 9. RustBeltと所有権

### 9.1 RustBeltの概要

RustBeltは、Rustの現実的なサブセットを表す言語の最初の形式的（かつ機械検査された）安全性証明である。

**拡張可能性**：
証明は拡張可能であり、unsafeな機能を使用する新しいRustライブラリごとに、それを言語への安全な拡張と見なすために満たさなければならない検証条件を述べることができる。

**重要ライブラリの検証**：
検証は、Rustエコシステム全体で使用されている最も重要なライブラリのいくつかに対して実施されている。

### 9.2 IrisとRust型のエンコーディング

Irisは、並行分離論理を理解するための統一フレームワークであり、Rust型の意味論的モデルをエンコードできる。

## 10. 分離論理の理論的基盤

### 10.1 決定可能性

**単項帰納的定義**：
単項帰納的定義と暗黙存在のある分離論理のエンテイルメントの決定可能性が証明されている。

**エンテイルメント判定器**：
単項帰納的定義をもつ記号ヒープのエンテイルメント判定器が実装されている。

### 10.2 自動推論

**共有を伴う再帰データ構造**：
ヒープと分離を用いた制約ベースのプログラム推論により、共有を伴う再帰データ構造の自動推論が可能になる。

**シンボリックヒープ**：
Smallfoot検証ツールは、「シンボリックヒープ」と呼ばれる分離論理の決定可能な断片（B ∧ H の形式の式で、Hはヒープ事実の分離接続であり、Bは非ヒープデータに関するブール表明）を使用した。

## 11. 分離論理の実用化と課題

### 11.1 実用化の成功例

**大規模産業応用**：
Facebook Inferは毎日数百万行のコードを検証し、Instagram、WhatsApp、Uberなどで使用されている。

**実証された有効性**：
アプリクラッシュの大部分の原因となるメモリ安全性エラーを実際に検出し、修正に貢献している。

### 11.2 教育と普及

**初心者向けガイド**：
「A beginner's guide to Iris, Coq and separation logic」などの教材が整備され、学習障壁を下げる努力がなされている。

**大学での教育**：
多くの大学で分離論理がカリキュラムに組み込まれている。

### 11.3 課題と限界

**注釈の必要性**：
VeriFastなどの対話的ツールでは、前提条件、事後条件、ループ不変条件、ゴースト宣言などの注釈が必要で、人間の努力を要する。

**学習曲線**：
分離論理の概念（分離接続子、フレームルール、述語の畳み込みと展開など）を理解するには相当の学習が必要。

**スケーラビリティ**：
非常に大規模なコードベースでの完全な検証は依然として課題。

## 12. 分離論理と仕様の関係

### 12.1 仕様記述への貢献

**局所仕様の表現**：
分離論理により、プログラムコンポーネントの仕様を、そのコンポーネントが実際に使用するメモリ部分のみで表現できる。これは、仕様の簡潔性と理解容易性を大幅に向上させる。

**合成的仕様**：
フレームルールにより、小さなコンポーネントの仕様から大きなシステムの仕様を合成できる。

### 12.2 仕様と実装の関係

**実行可能仕様**：
分離論理の仕様（前提条件と事後条件）は、プログラムの振る舞いを正確に規定し、実装の正当性を検証する基準となる。

**形式的保証**：
分離論理による検証は、仕様が実装によって実際に満たされていることの形式的保証を提供する。

### 12.3 メモリ安全性の形式化

**仕様レベルでの安全性**：
メモリ安全性という重要な性質を、分離論理の仕様として形式化できる。

**エイリアシングの制御**：
分離接続子により、エイリアシングの有無を仕様で明示的に制御できる。

## 13. 最新の研究動向

### 13.1 量子プログラムへの拡張

量子プログラムの局所推論のための分離論理に基づく分離接続子の量子解釈が研究されている。

### 13.2 セキュリティへの応用

**安全な構文解析とシリアライゼーション**：
分離論理を使用した安全な構文解析とシリアライゼーションの研究が進められている（例：PulseParse）。

### 13.3 型システムとの統合

**線形型と分離論理**：
線形型と分離論理の証明を合成してメモリ安全性を証明する研究が行われている。

### 13.4 結果分離論理（Outcome Separation Logic）

正当性と効率性の局所推論のための結果分離論理が提案されている。

## 14. まとめと展望

分離論理は、共有可変データ構造を扱うプログラムの推論のための強力な形式手法である。局所推論を可能にするフレームルールにより、大規模プログラムの検証が実用的になっている。

**主要な貢献**：
- **局所推論**：フットプリントに集中した簡潔な仕様と証明
- **合成性**：小さなコンポーネントの証明から大きなシステムの証明を構築
- **メモリ安全性**：ポインタ操作とエイリアシングの形式的扱い
- **並行性**：並行分離論理による並行プログラムの推論

**実用的成功**：
- **Facebook Infer**：毎日数百万行のコードを検証
- **広範な産業採用**：Instagram、WhatsApp、Uber、Spotifyなど
- **学術的認識**：ゲーデル賞、アロンゾ・チャーチ賞の受賞

**主要ツール**：
- **Iris**：高階並行分離論理の汎用フレームワーク
- **VeriFast**：C/Rust/Javaのモジュラー検証
- **Viper**：パーミッションベースの検証フレームワーク
- **Facebook Infer**：産業規模の静的解析

**今後の展望**：
- **自動化の向上**：注釈の自動推論
- **新しいドメインへの拡張**：量子プログラム、セキュリティプロトコル
- **教育の改善**：より分かりやすい教材と学習ツール
- **スケーラビリティの向上**：より大規模なコードベースへの適用
- **AIとの統合**：機械学習による不変条件の発見

分離論理は、「仕様とは何か」という問いに対して、局所性という重要な視点を提供している。プログラムの各部分が使用するリソース（メモリ）を明示的に仕様化することで、合成的で理解しやすい仕様を実現している。これは、大規模ソフトウェアシステムの形式検証を実用的にする鍵となっている。

## 参考文献

- [Separation logic - Wikipedia](https://en.wikipedia.org/wiki/Separation_logic)
- [Separation Logic – Communications of the ACM](https://cacm.acm.org/research/separation-logic/)
- [Separation Logic - Peter O'Hearn's Home Page](http://www0.cs.ucl.ac.uk/staff/p.ohearn/SeparationLogic/Separation_Logic/SL_Home.html)
- [An Introduction to Separation Logic - John C. Reynolds (PDF)](https://www.cs.cmu.edu/~jcr/copenhagen08.pdf)
- [Separation Logic: A Logic for Shared Mutable Data Structures - Reynolds (PDF)](https://www.cs.cmu.edu/~jcr/seplogic.pdf)
- [Concurrent Separation Logic - Brookes & O'Hearn (PDF)](https://read.seas.harvard.edu/~kohler/class/cs260r-17/brookes16concurrent.pdf)
- [Separation Logic - Peter O'Hearn (PDF)](https://discovery.ucl.ac.uk/10075346/1/O%27Hearn_AAM_sl-cacm-cameraready.pdf)
- [Coqで分離論理(separation logic) - keigoiの日記](https://keigoi.hatenadiary.org/entry/20110709/1310171928)
- [分離論理 - mrsekut-p](https://scrapbox.io/mrsekut-p/%E5%88%86%E9%9B%A2%E8%AB%96%E7%90%86)
- [Iris Project](https://iris-project.org/)
- [A beginner's guide to Iris, Coq and separation logic (PDF)](https://arxiv.org/pdf/2105.12077)
- [Iris from the ground up (PDF)](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
- [Iris from the ground up - Cambridge Core](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/iris-from-the-ground-up-a-modular-foundation-for-higherorder-concurrent-separation-logic/26301B518CE2C52796BFA12B8BAB5B5F)
- [Separation logic and bi-abduction | Infer](https://fbinfer.com/docs/separation-logic-and-bi-abduction/)
- [Open-sourcing Facebook Infer - Engineering at Meta](https://engineering.fb.com/2015/06/11/developer-tools/open-sourcing-facebook-infer-identify-bugs-before-you-ship/)
- [RustBelt: Logical Foundations - Jane Street](https://www.janestreet.com/tech-talks/rustbelt/)
- [RustBelt: Securing the Foundations of the Rust Programming Language (PDF)](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)
- [A Primer on Separation Logic (PDF)](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf)
- [The Meaning of Memory Safety (PDF)](https://arxiv.org/pdf/1705.07354)
- [The Meaning of Memory Safety](https://link.springer.com/chapter/10.1007/978-3-319-89722-6_4)
- [Automating Separation Logic with Trees and Data (PDF)](https://www.cs.yale.edu/homes/piskac/papers/2014PiskacETALSLtrees.pdf)
- [Qiver: Guided Abductive Inference (PDF)](https://plv.mpi-sws.org/quiver/paper-quiver.pdf)
- [Composing Linear Types and Separation Logic Proofs](https://dl.acm.org/doi/10.1145/3563768.3564119)
- [GitHub - verifast/verifast](https://github.com/verifast/verifast)
- [VeriFast's separation logic (PDF)](https://arxiv.org/html/2505.04500)
- [Viper – Programming Methodology Group | ETH Zurich](https://www.pm.inf.ethz.ch/research/viper.html)
- [Formal Foundations for Translational Separation Logic Verifiers (PDF)](https://dardinier.me/papers/POPL25_CoreIVL.pdf)
- [Verification Algorithms for Automated Separation Logic Verifiers](https://arxiv.org/html/2405.10661)
- [Gillian, Part II: Real-World Verification for JavaScript and C (PDF)](https://giltho.github.io/publications/GillianCAV2021.pdf)
- [Tutorial on Separation Logic](https://link.springer.com/chapter/10.1007/978-3-540-70545-1_5)
- [Lectures 8 and 9: Separation Logic | CS 839](https://tchajed.github.io/sys-verif-fa24/notes/sep-logic.html)
- [Chapter 6 Iterated Separating Conjunction (PDF)](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2009/ch6.pdf)
- [Constraint-based Program Reasoning with Heaps and Separation (PDF)](https://www.comp.nus.edu.sg/~gregory/papers/heaps.pdf)
