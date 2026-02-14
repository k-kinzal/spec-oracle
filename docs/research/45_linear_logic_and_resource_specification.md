# 線形論理と資源管理仕様

## 調査概要

本調査では、Jean-Yves Girardの線形論理（Linear Logic）と資源管理仕様について調査した。線形論理は、命題を資源として扱う革新的な論理体系であり、線形型システム、セッション型、Rustの所有権モデルなど、現代のプログラミング言語と形式手法に広範な影響を与えている。

## 1. 線形論理の基礎

### 1.1 Girardの線形論理

線形論理は、フランスの論理学者Jean-Yves Girardによって提案された部分構造論理（substructural logic）であり、古典論理と直観主義論理の洗練として位置付けられる。古典論理の双対性と、直観主義論理の構成的性質の多くを結合している。

参考: [Linear logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_logic)

### 1.2 根本的なイノベーション

Girardの線形論理における核心的イノベーションは、**命題を資源として扱う**ことである。古典論理や直観主義論理とは異なり、線形論理は式を組み合わせる異なる方法を区別し、仮定を証明中に消費される有限の資源として扱い、無限に再生産可能なものとは見なさない。

参考: [Linear logic in nLab](https://ncatlab.org/nlab/show/linear+logic)

### 1.3 「ちょうど一回」の使用

線形論理における鍵となるアイデアは、証明における各仮定は**ちょうど一回**使用されるべきである：それ以上（複製なし）でもなく、それ以下（削除なし）でもない。

より直感的には、命題は貴重な資源として扱われる。資源は捨てられるべきではなく、どこからともなく現れるべきでもない。

参考: [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)

## 2. 構造規則の制限

### 2.1 弱化（Weakening）と縮約（Contraction）

線形論理は、資源を自由に複製または破棄する能力を制限することでこれを扱う。具体的には、線形論理は、**弱化（weakening）**と**縮約（contraction）**という構造規則の拒絶から部分的に導出できる。

- **弱化**: 任意の命題を追加する規則
- **縮約**: 重複した命題を単一の出現に簡約する規則

参考: [Linear Logic | PLS Lab](https://www.pls-lab.org/Linear_Logic)

### 2.2 論理の変容

これらの論理規則の変更により、論理は**超越的**（真理はその使用を超越する）から**実用的または唯物論的**（真理は使用によって制限される）へと変容する。

したがって、線形論理には「資源解釈（resource interpretation）」を与えることができ、真理の論理ではなく、物の論理となる：生産と消費、与えることと取ること、押すことと引くこと。

参考: [Linear logic in nLab](https://ncatlab.org/nlab/show/linear+logic)

### 2.3 式の振る舞いの変化

縮約と弱化の規則を削除すると、式はもはや真理値として振る舞わなくなる。実際、これらの構造規則なしで A ⇒ B の証明と A の証明を合成すると、それらを消費してBの証明を得る：つまり、A ⇒ B とAは合成後にもはや利用可能ではない。

参考: [Linear Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-linear/)

## 3. 線形論理の結合子（Connectives）

### 3.1 乗法的（Multiplicative）結合子

古典的な連言とその単位元 ∧ と⊤は、加法的（additive）な & (with) と ⊤ (top)、および乗法的（multiplicative）な ⊗ (tensor) と 1 (one) に分割される。

同様に、古典的な選言とその単位元 ∨ と⊥は、加法的な ⊕ (oplus) と 0 (zero)、および乗法的な ⅋ (par) と ⊥ (bottom) に分割される。

参考: [Linear logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_logic)

### 3.2 加法的（Additive）結合子

まとめると：

- **乗法的結合子**: ⊗ (tensor) と ⅋ (par)
- **加法的結合子**: & (with) と ⊕ (oplus)

参考: [Linear Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-linear/)

### 3.3 指数的（Exponential）結合子

直観主義論理と古典論理の完全な表現力を回復するためには、MALLフラグメントに2つの双対な様相を追加する必要があり、これらは線形論理の文献では通常**指数的（exponentials）**と呼ばれる。

- **! (bang, "of course")**: 式!Bに対して左側のシーケント文脈で縮約と弱化を適用可能にする
- **? (question mark, "why not")**: 式?Bに対して右側のシーケント文脈で縮約と弱化を適用可能にする

参考: [Linear Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-linear/)

### 3.4 指数的の役割

指数的は、縮約と弱化への制御されたアクセスを提供するために使用される。!Aは「bang A」または「of course A」と読まれ、?Aは「question mark A」または「why not A」と読まれる。

参考: [Linear logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_logic)

### 3.5 算術との関係

「指数的（exponential）」という用語は特に適切である。なぜなら、指数、加算、乗算の間の通常の関係に従って、線形論理は以下の等価性をサポートするからである：

- !(B & C) ≡ (!B ⊗ !C)
- ?(B ⊕ C) ≡ (?B ⅋ ?C)

参考: [Linear logic additive, multiplicative, and exponential](https://www.johndcook.com/blog/2022/01/15/linear-logic-arithmetic/)

## 4. 線形型システム（Linear Type Systems）

### 4.1 部分構造型システム

部分構造型システムは、部分構造論理に類似した型システムのファミリーであり、1つ以上の構造規則が欠如しているか、制御された状況下でのみ許可される。

このようなシステムは、ファイル、ロック、メモリなどのシステム資源へのアクセスを、状態の変化を追跡し、無効な状態を禁止することによって制約できる。

参考: [Substructural type system - Wikipedia](https://en.wikipedia.org/wiki/Substructural_type_system)

### 4.2 線形型

**線形型**は線形論理に対応し、オブジェクトがちょうど一回使用されることを保証する。これにより、システムはオブジェクトの使用後に安全に割り当て解除できる。または、資源が閉じられた後または異なる状態に遷移した後に使用できないことを保証するソフトウェアインターフェースを設計できる。

参考: [Substructural type system - Wikipedia](https://en.wikipedia.org/wiki/Substructural_type_system)

### 4.3 アフィン型

**アフィン型**は、資源を破棄することを許可する線形型のバージョンである。アフィン資源は**高々一回**使用できるが、線形資源は**ちょうど一回**使用しなければならない。

参考: [Affine and Linear Types in LSTS - Medium](https://medium.com/@andrew_johnson_4/affine-and-linear-types-in-lsts-73ae6657f8f4)

### 4.4 資源管理

部分構造型システムによって提供される命名法は、言語の資源管理側面を特徴付けるのに有用である。資源管理は、割り当てられた各資源がちょうど一回割り当て解除されることを保証することに関係する言語安全性の側面である。

参考: [Substructural type system - Wikipedia](https://en.wikipedia.org/wiki/Substructural_type_system)

### 4.5 プログラミング言語への応用

プログラミング言語は、線形型を使用して、Javaのようなメモリ安全でガベージコレクションされる言語と、手動メモリ管理を使用するCやC++のような「メモリ不安全」な言語との間の「両方の世界の最良」を得ることができる。

人々は、Javaがuse-after-freeやdouble-freeのバグを排除する事実を好むが、ガベージコレクションにはコストがかかる。

参考: [CS 4110 – Linear Types](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture29.pdf)

## 5. Rustの所有権モデルと線形型

### 5.1 Rustのアフィン型

Rustのほとんどの型は**アフィン型**であり、一回または零回のみ使用できることを意味する。それらを使用することは移動することである；それらを使用しないことは破棄することである。これが所有権（ownership）の意味である。

Rustは通常の型もサポートしており、これらは任意の回数使用できる；現在、これらはCopyを実装する型である。

参考: [Ownership - without.boats](https://without.boats/blog/ownership/)

### 5.2 アフィン型vs線形型の区別

重要な区別：Rustの所有権と借用システムは、コンパイル時に単一所有権と移動意味論を強制することによって線形型を近似する。しかし、Rustは厳密な線形性を強制しない；例えば、値は使用せずに破棄できる。これはアフィン型を反映するものであり、線形型ではない。

参考: [Rust and Linear types: a short guide - Medium](https://medium.com/@martriay/rust-and-linear-types-a-short-guide-4845e9f1bb8f)

### 5.3 線形型への関心

**線形型**、つまりちょうど一回使用しなければならない型への関心が多い。違いは、通常の型は弱化と縮約を許可し（任意の回数使用可能）、アフィン型は弱化のみを許可し（高々一回）、線形型は弱化も縮約も許可しない（ちょうど一回）ことである。

参考: [Rust and Linear types: a short guide - Medium](https://medium.com/@martriay/rust-and-linear-types-a-short-guide-4845e9f1bb8f)

### 5.4 借用システム

規則が緩和される一つの方法は、値を借用（borrow）できることである。所有者を乱さずに値へのアクセスを一時的に他者に付与する方法がある。所有者は変わらないが、借用された参照によって値への一時的なアクセスを得る。

Rustには2種類の借用がある：

- **不変借用（Immutable borrowing）**: 値への複数の不変参照を持てるが、値を変更できない
- **可変借用（Mutable borrowing）**: 値への可変参照は1つのみ持て、他の参照（可変または不変）は共存できない

参考: [Moves and Borrowing In Rust - CoRecursive Podcast](https://corecursive.com/016-moves-and-borrowing-in-rust-with-jim-blandy/)

### 5.5 実装メカニズム

Rustは、移動意味論、借用チェック、ライフタイム推論、所有権規則の組み合わせを使用して、線形性（より正確にはアフィン型、線形型の緩和）を強制する。

参考: [Rust Inference Rules for Linear Types - Medium](https://medium.com/@andrew_johnson_4/rust-inference-rules-for-linear-types-e55cb6a347ed)

## 6. セッション型（Session Types）

### 6.1 線形論理とセッション型の対応

2010年、Luis CairesとFrank Pfenningは、線形論理の一形式とセッション型を備えたπ計算を接続する、並行計算のための命題としての型対応を開発した。

参考: [Linear Logic Propositions as Session Types](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)

### 6.2 セッションベース並行性

セッションベース並行性では、プロセスはちょうど2つのサブシステムを接続するセッションチャネルを通じて通信し、通信はセッションプロトコルによって規律される。これにより、アクションは常に双対のペアで発生する：

- 一方のパートナーが送信すると、他方が受信
- 一方のパートナーが選択を提供すると、他方が選択
- セッションが終了すると、それ以上の相互作用は発生しない

参考: [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf)

### 6.3 プロトコル仕様

セッション型は、チャネル上の通信を交換のシーケンスとして指定する。例えば、セッション型 `!int.?bool.end` は、チャネルの意図されたプロトコルを記述する：整数を送信し、ブール値を受信し、チャネルを閉じる。

参考: [Linear Logic Propositions as Session Types](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)

### 6.4 デッドロックフリーの保証

型システムは、メッセージが指定されたプロトコルに従うという意味で正しい通信を保証し、循環的な相互接続を禁止することによって並行プロセスのデッドロックフリーな実行を保証する。

参考: [Linear Logic, Session Types and Deadlock-Freedom](https://simons.berkeley.edu/talks/linear-logic-session-types-deadlock-freedom)

### 6.5 非同期通信

直観主義線形論理は、π計算のためのセッション型規律と見なすことができ、シーケント計算におけるカット削減は同期的プロセス簡約に対応する。非同期解釈の下では、カット削減は、各セッションが別々の通信バッファを割り当てられる自然な非同期バッファ付きセッション意味論に対応する。

参考: [Cut Reduction in Linear Logic as Asynchronous Session-Typed Communication](https://www.researchgate.net/publication/267665670_Cut_Reduction_in_Linear_Logic_as_Asynchronous_Session-Typed_Communication)

## 7. 分離論理（Separation Logic）

### 7.1 線形論理との関係

分離論理（Separation Logic）は、Reynolds、O'Hearn、Yangによって2000年頃に発明され、ヒーププログラムを効果的に推論できるようにする様々な構成をHoare論理に追加する。

分離論理は、ヒープへのポインタを操作する（割り当て、解放、初期化、更新）プログラムに有用である。

参考: [Lectures 8 and 9: Separation Logic](https://tchajed.github.io/sys-verif-fa24/notes/sep-logic.html)

### 7.2 線形型とアフィン型

**線形論理**は、すべての命題または「資源」が証明で**ちょうど一回**使用されることを要求する。典型的には、線形論理と affine 分離論理の間の分岐は、線形論理が手動メモリ管理を持つ言語に使用され、affine 論理がガベージコレクション言語に使用されることである。

参考: [A Modern Eye on Separation Logic](https://inria.hal.science/tel-04076725v1/document)

### 7.3 分離結合子

分離論理において、分離結合子 P ∗ Q は、主張Pがヒープの一部で成立し、Qが別の部分で成立し、これら2つの部分が互いに素であり、それらの和集合が P ∗ Q によって推論されるヒープ全体を形成する場合にヒープ上で成立する。

参考: [Lecture 33: Separation Logic](https://course.ccs.neu.edu/cs2800sp23/l33.html)

### 7.4 小フットプリント仕様

分離論理のトリプルは、項がメモリ状態と持つ可能性のあるすべての相互作用を捉える。事前条件で明示的に記述されていない状態の任意の部分は、未接触のまま残ることが保証される。

参考: [A Primer on Separation Logic](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf)

### 7.5 資源消費の追跡

分離論理ベースの前方解析を使用して、プログラムの実行を記号的に追跡し、記号的Presburger算術式を使用してヒープメモリにおける割り当てと割り当て解除の効果を表現できる。

線形論理的契約の性質により、複雑な再帰的データ構造のメモリ形状とエイリアシング性質の指定が容易になる。

参考: [Expressing Heap-shape Contracts in Linear Logic](https://www.cs.princeton.edu/~dpw/papers/llcontracts-gpce06)

## 8. 証明ネットとカット除去

### 8.1 証明ネット

証明ネットは、線形論理の証明をグラフとして表現する方法である。MLL（乗法的線形論理）の証明ネットにおけるカット除去は、線形時間で実行できる。

参考: [Structural Cut Elimination in Linear Logic](https://www.cs.cmu.edu/~fp/papers/cutlin94.pdf)

### 8.2 資源消費の分析

微分線形論理（Differential Linear Logic, DiLL）は、カット除去における資源消費の細かい分析を提供する。

参考: [A Deep Inference System for Differential Linear Logic](https://www.researchgate.net/publication/357526535_A_Deep_Inference_System_for_Differential_Linear_Logic)

### 8.3 カット除去の複雑性

線形論理のカット除去は、初期証明のサイズにおいて多項式を超える多くのステップを要する可能性があるが、それらのステップを実装するコストは、それらの数と証明サイズにおいて多項式的、理想的には線形的でなければならない。

カット除去戦略は、しばしばサイズ爆発に悩まされ、証明のファミリーはカット除去ステップにおける悪意のある複製パターンによって証明サイズの指数的成長を持つ可能性がある。

参考: [Exponentials as Substitutions, and the Cost of Cut Elimination](https://arxiv.org/pdf/2205.15203)

## 9. 線形論理による資源管理の形式化

### 9.1 命題としての資源

線形論理における根本的な洞察は、命題を資源として扱うことである。これにより、以下が可能になる：

- メモリ割り当てと割り当て解除の追跡
- ファイルハンドルやネットワーク接続などのシステム資源の管理
- 並行性におけるチャネルとプロトコルの仕様
- 所有権と借用の形式化

### 9.2 使用パターンの制御

線形論理は、資源の使用パターンを制御する：

- **線形**: ちょうど一回使用（縮約も弱化もなし）
- **アフィン**: 高々一回使用（弱化のみ）
- **関連**: 少なくとも一回使用（縮約のみ）
- **無制限**: 任意の回数使用（縮約と弱化の両方）

### 9.3 型システムへの応用

これらの概念は、以下の型システムに応用されている：

- Rustの所有権とライフタイム
- Clean の uniqueness types
- Linear Haskell
- セッション型による通信プロトコル

## 10. 線形論理の限界と課題

### 10.1 実用性の課題

線形論理とそれに基づく型システムには、実用上の課題がある：

- **学習曲線**: 線形型は、従来の型システムよりも理解が困難
- **プログラミングの制約**: 厳密な線形性は、プログラミングを制約する
- **型推論の複雑性**: 線形型の推論は、より複雑

### 10.2 表現力のトレードオフ

線形性を厳格に強制すると、一部の有用なプログラミングパターンが表現困難になる：

- 共有データ構造
- 永続的データ構造
- 高階関数の柔軟な使用

### 10.3 指数的の必要性

完全な表現力を回復するために指数的(!と?)を導入する必要があるが、これは線形性の利点の一部を失うことを意味する。

## 11. 線形論理の応用領域

### 11.1 並行プログラミング

セッション型による通信プロトコルの仕様と検証：

- デッドロックフリーの保証
- プロトコル準拠の静的検証
- 型安全な並行性

### 11.2 メモリ管理

線形型とアフィン型によるメモリ安全性：

- Use-after-freeの防止
- Double-freeの防止
- メモリリークの防止（線形型の場合）

### 11.3 資源管理

ファイル、ネットワーク接続、ロックなどのシステム資源：

- 資源リークの防止
- 資源の適切な解放の保証
- 状態遷移の型による追跡

### 11.4 プログラム検証

分離論理による低レベルコードの検証：

- ヒープ操作の正しさ
- メモリ形状の不変条件
- エイリアシングの制御

## 12. まとめ

### 12.1 線形論理の本質

線形論理の核心的貢献：

1. **命題を資源として扱う**: 真理から資源へのパラダイムシフト
2. **構造規則の明示的制御**: 弱化と縮約の選択的適用
3. **結合子の精密化**: 乗法的・加法的・指数的結合子による細かい制御
4. **実用的応用**: 型システム、並行性、検証への広範な影響

### 12.2 理論的成果

- **証明論**: 証明ネット、カット除去の線形時間アルゴリズム
- **意味論**: ゲーム意味論、圏論的意味論
- **複雑性**: カット除去の計算複雑性の分析

### 12.3 実用的影響

線形論理は、以下の実用的技術に影響を与えた：

- **Rust**: 所有権、借用、ライフタイム
- **セッション型**: 通信プロトコルの型システム
- **分離論理**: メモリ安全性検証
- **線形型システム**: 関数型言語への統合（Clean、Linear Haskell）

### 12.4 今後の方向性

- より使いやすい線形型システムの開発
- 線形論理と他の論理の統合
- 実用的プログラミング言語への更なる採用
- 教育的アプローチの改善

線形論理は、資源としての命題という革新的な視点を提供し、形式手法とプログラミング言語理論に永続的な影響を与え続けている。

## 参考文献

### 線形論理の基礎
- [Linear logic - Wikipedia](https://en.wikipedia.org/wiki/Linear_logic)
- [Linear Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-linear/)
- [linear logic in nLab](https://ncatlab.org/nlab/show/linear+logic)
- [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)
- [Linear Logic | PLS Lab](https://www.pls-lab.org/Linear_Logic)
- [J.-Y. Girard's Linear Logic | Equivalent Exchange](https://equivalentexchange.blog/2011/03/09/j-y-girards-linear-logic/)

### 線形型システム
- [Substructural type system - Wikipedia](https://en.wikipedia.org/wiki/Substructural_type_system)
- [CS 4110 – Linear Types](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture29.pdf)
- [CS 6110 S17 Lecture 30 Linear Type Systems](https://www.cs.cornell.edu/courses/cs6110/2017sp/lectures/lec30.pdf)
- [Linear types for programmers](https://twey.io/for-programmers/linear-types/)
- [Practical Affine Types](https://users.cs.northwestern.edu/~jesse/pubs/alms/tovpucella-alms.pdf)
- [Affine and Linear Types in LSTS - Medium](https://medium.com/@andrew_johnson_4/affine-and-linear-types-in-lsts-73ae6657f8f4)

### Rust所有権モデル
- [Ownership - without.boats](https://without.boats/blog/ownership/)
- [Rust and Linear types: a short guide - Medium](https://medium.com/@martriay/rust-and-linear-types-a-short-guide-4845e9f1bb8f)
- [Rust Inference Rules for Linear Types - Medium](https://medium.com/@andrew_johnson_4/rust-inference-rules-for-linear-types-e55cb6a347ed)
- [Rust: Ownership Principles - High Assurance Rust](https://highassurance.rs/chp3/rust_4_own_1.html)
- [The Pain Of Linear Types In Rust - Faultlore](https://faultlore.com/blah/linear-rust/)
- [Moves and Borrowing In Rust - CoRecursive Podcast](https://corecursive.com/016-moves-and-borrowing-in-rust-with-jim-blandy/)

### セッション型
- [Linear Logic Propositions as Session Types](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)
- [Propositions as Sessions](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf)
- [A New Linear Logic for Deadlock-Free Session-Typed Processes](https://link.springer.com/chapter/10.1007/978-3-319-89366-2_5)
- [Cut Reduction in Linear Logic as Asynchronous Session-Typed Communication](https://www.researchgate.net/publication/267665670_Cut_Reduction_in_Linear_Logic_as_Asynchronous_Session-Typed_Communication)
- [Linear Logic, Session Types and Deadlock-Freedom](https://simons.berkeley.edu/talks/linear-logic-session-types-deadlock-freedom)
- [Comparing Session Type Systems derived from Linear Logic](https://arxiv.org/pdf/2401.14763)

### 分離論理
- [Lectures 8 and 9: Separation Logic](https://tchajed.github.io/sys-verif-fa24/notes/sep-logic.html)
- [Expressing Heap-shape Contracts in Linear Logic](https://www.cs.princeton.edu/~dpw/papers/llcontracts-gpce06)
- [Tactics for Separation Logic](https://www.cs.princeton.edu/~appel/papers/septacs.pdf)
- [Lecture 33: Separation Logic](https://course.ccs.neu.edu/cs2800sp23/l33.html)
- [A Modern Eye on Separation Logic](https://inria.hal.science/tel-04076725v1/document)
- [A Primer on Separation Logic](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/Marktoberdorf11LectureNotes.pdf)

### 証明ネットとカット除去
- [Structural Cut Elimination in Linear Logic](https://www.cs.cmu.edu/~fp/papers/cutlin94.pdf)
- [A Deep Inference System for Differential Linear Logic](https://www.researchgate.net/publication/357526535_A_Deep_Inference_System_for_Differential_Linear_Logic)
- [An application of parallel cut elimination](https://arxiv.org/html/1902.05193)
- [Exponentials as Substitutions, and the Cost of Cut Elimination](https://arxiv.org/pdf/2205.15203)
- [Isolating Resource Consumption in Linear Logic Proof Search](https://www.researchgate.net/publication/220368124_Isolating_Resource_Consumption_in_Linear_Logic_Proof_Search)

### 指数的と結合子
- [Linear logic additive, multiplicative, and exponential](https://www.johndcook.com/blog/2022/01/15/linear-logic-arithmetic/)
- [Linear Logic - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/logic-linear/)
