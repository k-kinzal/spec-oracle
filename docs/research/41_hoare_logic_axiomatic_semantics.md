# Hoare論理と公理的意味論

## 概要

本レポートは、プログラム検証の基礎であるHoare論理（Hoare logic）と公理的意味論（axiomatic semantics）について調査し、その理論的基盤、主要概念、応用、および最新の発展を明らかにすることを目的とする。

---

## 1. Hoare論理の歴史と概要

### 1.1 歴史的背景

**Floyd-Hoare論理**は、プログラミング言語の各構文構造に対して、プログラムの正しさを合成的に推論するための一般的な「証明規則」を装備した推論システムである。

**主要な貢献者:**

- **Robert W. Floyd (1967)**: プログラムに一階述語論理で表現された論理アサーションを注釈付けする手法を提案し、論理アサーションが対応するプログラム文に一致する際の正確な規則を提供した。

- **C.A.R. (Tony) Hoare (1969)**: Floydの研究を基に、公理的意味論スタイルを開発。これはプログラムの正しさと停止性について推論するための基盤となった。

**参考文献:**
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
- [Tony Hoare - Contributions - Hoare Logic](https://cs.stanford.edu/people/eroberts/courses/soco/projects/2008-09/tony-hoare/logic.html)
- [Axiomatic semantics - Wikipedia](https://en.wikipedia.org/wiki/Axiomatic_semantics)

### 1.2 現代における位置づけ

Hoare論理は1960年代に起源を持ち、現在も集中的な研究の対象となっている。学界と産業界で実際のソフトウェアシステムの仕様記述と検証に使用される多数のツールの中核に位置している。

**参考文献:**
- [Ten Years of Hoare's Logic: A Survey - Krzysztof R. Apt](https://www.cs.cornell.edu/courses/cs6860/2019sp/Handouts/Apt10years.pdf)

---

## 2. 公理的意味論（Axiomatic Semantics）

### 2.1 定義と目的

**公理的意味論**は、コンピュータプログラムの正しさを証明するための数学的論理に基づくアプローチである。形式的なプログラム検証の手段として設計された。

**主要な特徴:**

公理的意味論は、プログラム内のコマンドの意味を、プログラム状態に関するアサーションへの影響によって定義する。具体的には、プログラムの実行効果を述語変換器（predicate transformer）としてモデル化する。

**参考文献:**
- [Axiomatic Semantics and Hoare-style Verification - CMU](https://www.cs.cmu.edu/~aldrich/courses/17-355-18sp/notes/notes11-hoare-logic.pdf)
- [Axiomatic semantics - Wikipedia](https://en.wikipedia.org/wiki/Axiomatic_semantics)

### 2.2 基本構成要素

公理的意味論は以下の2つの要素から構成される:

1. **アサーション記述言語**: プログラムに関するアサーション（例: 「この関数が停止する場合、停止時にx > 0である」）を記述するための言語

2. **証明規則**: アサーションの真偽を確立するための規則
   - **公理（Axiom）**: 真であると仮定される論理的命題
   - **推論規則（Inference Rule）**: あるアサーションから次のアサーションへの変換を記述する方法

**参考文献:**
- [Axiomatic Semantics - University of Iowa](https://homepage.divms.uiowa.edu/~slonnegr/plf/Book/Chapter11.pdf)
- [Semantics of Programming Language - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/semantics-of-programming-language)

### 2.3 述語変換器（Predicate Transformer）

公理的意味論は、各文や式を**述語変換器**としてモデル化する。述語変換器は、初期状態で真であることが知られている条件の集合を受け取り、構文が評価された後に真であることが保証される新しい条件の集合を導出する推論規則である。

**参考文献:**
- [Predicate transformer semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)

---

## 3. Hoare三つ組（Hoare Triple）

### 3.1 基本概念

Floyd-Hoare論理における基本的な概念は**Hoare三つ組（Hoare triple）**である。

**表記法:**

```
{P} c {Q}
```

**意味:**

コマンドcが、アサーションPを満たす状態で実行を開始し、最終的に何らかの最終状態で停止する場合、その最終状態はアサーションQを満たす。

- **P**: 事前条件（precondition）
- **c**: コマンド（command）
- **Q**: 事後条件（postcondition）

**参考文献:**
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
- [Hoare Logic for control structures - Xavier Leroy](http://xavierleroy.org/control-structures/book/main016.html)

### 3.2 事前条件と事後条件

**事前条件（Precondition）:**
- プログラムが実行される前に成立していなければならない要件を記述
- しばしば`requires`節として表現される

**事後条件（Postcondition）:**
- プログラムが戻る際に真となる性質を記述
- しばしば`ensures`節として表現される

**参考文献:**
- [Reasoning About Code (Hoare Logic) - University of Washington](https://courses.cs.washington.edu/courses/cse331/13sp/conceptual-info/hoare-logic.pdf)
- [Software Foundations - Hoare Logic, Part I](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)

---

## 4. Hoare論理の証明規則

### 4.1 主要な証明規則

Hoare論理は、各プログラム構造に対する証明規則を提供する。以下は主要な規則の例:

#### (1) 代入規則（Assignment Rule）

```
{P[x := E]} x := E {P}
```

xにEを代入した後にPが成り立つためには、代入前にP[x := E]（PのxをEで置換したもの）が成り立っていなければならない。

#### (2) 連接規則（Sequential Composition Rule）

```
{P} c1 {Q}  {Q} c2 {R}
─────────────────────
    {P} c1; c2 {R}
```

#### (3) 条件分岐規則（Conditional Rule）

```
{P ∧ b} c1 {Q}  {P ∧ ¬b} c2 {Q}
──────────────────────────────
  {P} if b then c1 else c2 {Q}
```

#### (4) ループ規則（While Rule）

```
{P ∧ b} c {P}
────────────────────
{P} while b do c {P ∧ ¬b}
```

Pはループ不変条件（loop invariant）と呼ばれる。

#### (5) 帰結規則（Consequence Rule）

```
P' ⇒ P  {P} c {Q}  Q ⇒ Q'
──────────────────────────
      {P'} c {Q'}
```

**参考文献:**
- [Lecture Notes: Hoare Logic - CMU](https://www.cs.cmu.edu/~aldrich/courses/654-sp09/notes/3-hoare-notes.pdf)
- [Hoare Logic: Proving Programs Correct - CMU](https://www.cs.cmu.edu/~aldrich/courses/654-sp07/slides/7-hoare.pdf)

### 4.2 ループ不変条件（Loop Invariant）

whileループの事前条件Pは**ループ不変条件**として使用される。

**性質:**

- ループ本体sは、Pが初期状態で成り立ち、ループ条件bが真であることを仮定できる
- ループの各反復で真のままである性質をアサートする
- どの要素が既に処理されたかなどの性質を表現

**参考文献:**
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)

---

## 5. 最弱事前条件と最強事後条件

### 5.1 Dijkstraの述語変換器意味論

**Edsger W. Dijkstra**は、1975年に論文「Guarded commands, nondeterminacy and formal derivation of programs」において、述語変換器意味論を導入した。

述語変換器意味論は、命令型プログラミングパラダイムの意味論を、各文に対応する述語変換器（状態空間上の2つの述語間の全関数）を割り当てることによって定義する。

**参考文献:**
- [Predicate transformer semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)

### 5.2 最弱事前条件（Weakest Precondition）

**定義:**

プログラム文Sと事後条件Rに対して、Sの実行が開始されればSが終了してRが真となる状態に到達することが保証される（空の可能性もある）プログラム状態の集合が存在する。Rに関するSの最弱事前条件（通常wp(S,R)と表記）は、この状態集合を特徴づける述語である。

**性質:**

事後条件を確立するために必要な最も一般的な事前条件である。任意の事前条件Pに対して、P ⇒ Qとなるような述語Qが最弱事前条件である。言い換えれば、Sの後にRが成り立つことを保証するために必要な「最も緩い」または最も制限の少ない要件である。

**目的:**

Dijkstraは、プログラムの導出を、プログラムの完全正当性証明の同時開発によって導くための計算法と併せて、最弱事前条件を導入した。

**参考文献:**
- [Weakest-Precondition Reasoning - University of Maryland](https://www.cs.umd.edu/~mvz/handouts/weakest-precondition.pdf)
- [Weakest Precondition - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/weakest-precondition)
- [Weakest precondition - Encyclopedia.com](https://www.encyclopedia.com/computing/dictionaries-thesauruses-pictures-and-press-releases/weakest-precondition)

### 5.3 最強事後条件（Strongest Postcondition）

**定義:**

最弱事前条件の双対概念として、最強事後条件が導入された。

**目的:**

最弱事前条件と最強事後条件は、Hoare論理の妥当な演繹を構築するための完全な戦略である。

**参考文献:**
- [Predicate transformer semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
- [Computing Preconditions and Postconditions of While Loops - Springer](https://link.springer.com/chapter/10.1007/978-3-642-23283-1_13)

---

## 6. 部分正当性と完全正当性

### 6.1 部分正当性（Partial Correctness）

**定義:**

プログラムが**停止する場合に**正しいこと。実行前に事前条件が真であると仮定し、関数が停止する場合、事後条件が真となる。

**Hoare三つ組の意味:**

標準のHoare三つ組 `{P} c {Q}` は部分正当性仕様と呼ばれる。なぜなら、cの停止を要求しないからである。

**参考文献:**
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
- [Introduction to Deductive Program Verification - UT Austin](https://www.cs.utexas.edu/~isil/cs389L/HoareLogic-6up.pdf)

### 6.2 完全正当性（Total Correctness）

**定義:**

完全正当性 = 部分正当性 + 停止性

**表記法:**

完全正当性は通常、角括弧を用いて `[P] S [Q]` と表記される。

**参考文献:**
- [Hoare logic Total correctness - Cambridge](https://www.cl.cam.ac.uk/teaching/1819/HLog+ModC/slides/lecture6-4.pdf)
- [Total Correctness Specification - Cambridge](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/Oct17.pdf)

### 6.3 停止性の証明

**ループ変数（Loop Variant）:**

停止性は、**ループ変数**と呼ばれる式によって証明される。この式の値は各反復中に厳密に減少する。関係が整礎的であるため、厳密に減少する連鎖は有限の長さしか持てず、したがって変数は永遠に減少し続けることはできない。

**拡張されたWhile規則:**

標準のHoare論理を使用すると、部分正当性のみを証明できる。完全正当性を証明するには、停止性を別途証明するか、While規則の拡張版を使用する。

**参考文献:**
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
- [Lecture Notes: Hoare Logic - CMU](https://www.cs.cmu.edu/~aldrich/courses/654-sp09/notes/3-hoare-notes.pdf)

---

## 7. 健全性と完全性

### 7.1 健全性定理（Soundness Theorem）

**定義:**

証明システムが部分正当性について健全であること、すなわち、`{p} S {q}` が証明可能（⊢{p} S {q}）ならば、それは妥当（⊨{p} S {q}）であることを示す。

**言い換え:**

Hoare論理は健全であり、各Hoare論理定理は妥当な部分正当性三つ組であることが保証される。

**証明方法:**

帰納法により、システムのすべての公理が妥当であり、すべての証明規則が健全であることを証明する。証明規則が健全であるとは、前提のHoare三つ組の妥当性が結論のHoare三つ組の妥当性を含意することである。

**参考文献:**
- [Soundness and Completeness of Hoare Logic - NTU](https://www.im.ntu.edu.tw/~tsay/dokuwiki/lib/exe/fetch.php?media=courses:ssv2024:hoare_logic_soundness_completeness.pdf)
- [Soundness and Completeness - Cornell](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture10.pdf)

### 7.2 完全性定理（Completeness Theorem）

**定義:**

Hoare三つ組 `{P} c {Q}` が意味論的に妥当（⊨{P} c {Q}）である場合、帰結規則に現れるアサーションの妥当性に対する証明が存在する限り、Hoare論理の規則を使用した証明（⊢{P} c {Q}）が存在する。

**重要な制限:**

Gödelの第一不完全性定理によれば、算術の一階理論に対する完全な証明システムは存在しない。したがって、Hoare論理の完全性は、実際にはすべてのアサーションの真理性に対して**相対的**である。

**結論:**

Hoare論理は、基礎となる論理が健全かつ完全である場合、健全かつ完全である。ただし、基礎となる論理（例: Peano算術）は健全であるが不完全であることが多い。

**参考文献:**
- [Soundness and Completeness of an Axiom System for Program Verification - SIAM](https://epubs.siam.org/doi/10.1137/0207005)
- [On the soundness and completeness of generalized Hoare logic - ResearchGate](https://www.researchgate.net/publication/238286887_On_the_soundness_and_completeness_of_generalized_Hoare_logic)
- [A language independent proof of the soundness and completeness - ScienceDirect](https://www.sciencedirect.com/science/article/pii/0890540189900187)

---

## 8. 検証条件生成（Verification Condition Generation）

### 8.1 定義と目的

**検証条件生成器（Verification Condition Generator, VCG）**は、プログラムとその形式仕様から論理式の集合を生成するツールである。これらの論理式は、定理証明器によって妥当性が示される必要がある。

**プロセス:**

検証条件生成器が検証条件を作成した後、それらは自動定理証明器に渡され、コードの正しさを形式的に証明できる。

**参考文献:**
- [Verification condition generator - Wikipedia](https://en.wikipedia.org/wiki/Verification_condition_generator)
- [Verification Condition Generation Via Theorem Proving - Springer](https://link.springer.com/chapter/10.1007/11916277_25)

### 8.2 自動定理証明との統合

**手法:**

与えられた機械言語の操作的意味論と既存の定理証明器を、高保証検証条件生成器に変換する手法が存在する。これにより、定理証明器を検証条件の生成と解消の両方に使用できる。

**利点:**

- カスタムビルドのVCGツールの必要性を排除
- 部分正当性と完全正当性の両方を扱える
- 合成的：サブルーチンの正しさは、各呼び出しサイトではなく、一度証明すればよい

**参考文献:**
- [Verification Condition Generation Via Theorem Proving - University of Florida](https://www.ece.ufl.edu/wp-content/uploads/sites/119/publications/lpar06.pdf)
- [A Certified Multi-prover Verification Condition Generator - Inria](https://inria.hal.science/hal-00639977v1/document)

### 8.3 応用とツール

**歴史的事例:**

1960年代後半、一階定理証明器がコンピュータプログラムの正しさ検証の問題に適用された。Stanford Pascal Verifierは初期のプログラム検証システムの中でも注目すべきものである。

**現代のツール:**

- **Boogie**: 一階論理によるアノテーションで強化されたC#とCのフロントエンドを持つ、命令型コア言語の検証条件生成器

**参考文献:**
- [Automated theorem proving - Wikipedia](https://en.wikipedia.org/wiki/Automated_theorem_proving)
- [Using Automated Theorem Provers to Certify Auto-Generated Aerospace Software - NASA](https://ntrs.nasa.gov/api/citations/20040068177/downloads/20040068177.pdf)

### 8.4 現在の課題

実世界のプログラム検証では、既存の自動定理証明器が証明できない困難な検証条件に頻繁に遭遇し、検証条件の定理証明には多大な手作業が必要とされる。

**最新の研究（2025）:**

ニューラル定理証明を検証条件に適用する研究が進められており、実世界のベンチマークが提供されている。

**参考文献:**
- [Neural Theorem Proving for Verification Conditions - arXiv](https://arxiv.org/html/2601.18944)
- [Neural Theorem Proving for Verification Conditions - arXiv PDF](https://arxiv.org/pdf/2601.18944)

---

## 9. 分離論理（Separation Logic）

### 9.1 概要と動機

**分離論理（Separation Logic）**は、Hoare論理を拡張し、並行プログラムの検証を可能にする形式体系である。

**歴史:**

並行分離論理（Concurrent Separation Logic, CSL）は、Stephen BrookesとPeter O'Hearnによる論文（John Reynoldsの70歳記念論文集、Theoretical Computer Science 2007に掲載）で発表された。O'HearとBrookesは、並行分離論理の発明により2016年Gödel賞を共同受賞した。

**参考文献:**
- [Separation logic - Wikipedia](https://en.wikipedia.org/wiki/Separation_logic)
- [Concurrent Separation Logic - Harvard](https://read.seas.harvard.edu/~kohler/class/cs260r-17/brookes16concurrent.pdf)

### 9.2 主要概念

**並行システムにおける推論:**

並行分離論理（CSL）は、並行システムにおける共有リソースと並行性制御について推論するための強力な形式体系として登場した。

**分数許可権（Fractional Permissions）:**

分数許可権を持つ並行分離論理（CSL-Perm）は、最も複雑な逐次および並行細粒度プログラムを検証するための有望な推論システムを提供する。

**参考文献:**
- [Concurrent Separation Logic (CSL) - ResearchGate](https://www.researchgate.net/publication/372748817_Concurrent_Separation_Logic_CSL)
- [Towards Concurrent Quantitative Separation Logic - Dagstuhl](https://drops.dagstuhl.de/storage/00lipics/lipics-vol243-concur2022/LIPIcs.CONCUR.2022.25/LIPIcs.CONCUR.2022.25.pdf)

### 9.3 検証ツールと実装

**主要なツール:**

- **VeriFast**: オブジェクト指向パターンから高度な並行アルゴリズム、システムプログラムまで、さまざまな証明を実証した高度なツール

- **Viper**: 許可権ベースの推論のための最先端の自動検証インフラストラクチャ。プログラミング言語と2つの検証バックエンドから構成。Viperインフラストラクチャに基づき、さまざまなプログラミング言語のフロントエンドが登場:
  - Gobra（Go用）
  - Nagini（Python用）
  - Prusti（Rust用）
  - VerCors（C、Java、OpenCL、OpenMP用）

- **Iris**: Coq証明支援器で機械化された最先端の分離論理。並行プログラムについて推論するために使用できるプログラム論理を含む

**参考文献:**
- [VeriFast's separation logic - arXiv](https://arxiv.org/abs/2505.04500)
- [Simuliris: A Separation Logic Framework - Iris Project](https://iris-project.org/pdfs/2022-popl-simuliris.pdf)
- [Separation Logic for Concurrency and Persistency - Iris Project](https://iris-project.org/pdfs/2023-phd-vindum.pdf)

### 9.4 最新の発展

**確率的推論:**

最近の研究は、並行性を考慮に入れた量的分離論理の結果を基に、確率的推論をサポートする並行分離論理を開発している。

**参考文献:**
- [Specifying Concurrent Programs in Separation Logic - arXiv](https://arxiv.org/pdf/1904.07136)
- [Compositional Verification in Concurrent Separation Logic - arXiv](https://arxiv.org/pdf/2508.18115)

---

## 10. 最新の研究動向（2025年）

### 10.1 関係的Hoare論理（Relational Hoare Logic）

**2025年の研究:**

関係的Hoare論理は、精緻化を確立するための強力なツールとして機能するが、しばしば標準Hoare論理を超える形式化を必要とする。特に非決定的設定では、∀∃関係的Hoare論理が必要とされ、既存のアプローチはこの論理をゴースト状態と不変条件を持つHoare論理にエンコードしている。

**参考文献:**
- [Encode the ∀∃ Relational Hoare Logic into Standard Hoare Logic - ACM](https://dl.acm.org/doi/10.1145/3763138)

### 10.2 自然な証明のための形式フレームワーク

**課題:**

Hoare論理に基づく形式的証明は、自然な証明の論理構造を反映できない。

**解決策:**

研究者は、逐次アルゴリズムを自然に仕様記述および検証するための形式フレームワークを導入し、新しい2段階証明アプローチを持つモナド用のHoare論理を構築している。

**参考文献:**
- [A Formal Framework for Naturally Specifying and Verifying Sequential Algorithms - Springer](https://link.springer.com/chapter/10.1007/978-3-031-98208-8_4)

### 10.3 コンパイラ検証への応用

**公理的意味論の新しい応用:**

公理的意味論に基づいて、コンパイラの正しさを仕様の保存として表現できる。

**参考文献:**
- [Axiomatic semantics for compiler verification - ACM](https://dl.acm.org/doi/10.1145/2854065.2854083)
- [Axiomatic Semantics for Compiler Verification - Saarland](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2016_Axiomatic-Semantics.pdf)

---

## 11. Hoare論理と仕様理論の関係

### 11.1 仕様記述言語としてのHoare論理

Hoare論理は、プログラムの振る舞いを**宣言的**に記述する手段を提供する。

**対応関係:**

- **事前条件**: プログラムの入力ドメイン（D）の制約
- **事後条件**: プログラムの許容される出力（A）の制約
- **Hoare三つ組全体**: プログラムの仕様

### 11.2 公理的意味論と他の意味論の比較

**3つの主要な意味論:**

1. **操作的意味論（Operational Semantics）**: プログラムの実行を抽象機械でモデル化
2. **表示的意味論（Denotational Semantics）**: プログラムを数学的対象（関数など）として解釈
3. **公理的意味論（Axiomatic Semantics）**: プログラムの性質を論理的アサーションで記述

**特徴:**

公理的意味論は、プログラムが「何をするか」ではなく、「何を保証するか」に焦点を当てる。これは仕様記述の本質に最も近い。

**参考文献:**
- [Operation, Axiomatic, Denotational - CSU](https://www.cs.csub.edu/~melissa/cs350-f15/notes/notes04b.html)
- [Semantics - LMU](https://cs.lmu.edu/~ray/notes/semantics/)

---

## 12. 実用的なプログラム検証への応用

### 12.1 契約プログラミング（Design by Contract）

Hoare論理の概念は、**契約プログラミング**として実用化されている。

**主要な概念:**

- メソッドやクラスに事前条件、事後条件、クラス不変条件を注釈付け
- Eiffel、Spec#、JMLなどの言語やツールでサポート

### 12.2 静的解析ツール

**Hoare論理を基盤とするツール:**

- **Frama-C**: C言語の静的解析フレームワーク
- **Why3**: 演繹的プログラム検証のためのプラットフォーム
- **Dafny**: Microsoft Researchによる検証指向プログラミング言語
- **F***: 証明指向プログラミング言語

### 12.3 産業界での応用

**事例:**

- 航空宇宙ソフトウェアの検証
- セキュリティクリティカルなシステムの検証
- OS カーネルやデバイスドライバの検証（seL4プロジェクトなど）

---

## 13. 課題と限界

### 13.1 表現力の限界

**制約:**

- 標準のHoare論理は、ポインタやヒープ操作を扱うのが困難（→ 分離論理が解決）
- 並行性の推論が複雑（→ 並行分離論理が解決）
- ループ不変条件の発見は自動化が困難

### 13.2 スケーラビリティの問題

**課題:**

- 大規模なプログラムの検証は、依然として時間と専門知識を要する
- 検証条件の自動証明には限界がある
- 手作業による証明が必要な場合が多い

### 13.3 基礎となる論理の不完全性

**理論的限界:**

Gödelの不完全性定理により、算術を含む論理システムは必然的に不完全である。したがって、Hoare論理の完全性は、基礎となる論理に依存する。

---

## 14. 結論

### 14.1 主要な発見

1. **Hoare論理の基盤性**: Hoare論理は、プログラム検証の基礎理論であり、50年以上にわたり発展を続けている。

2. **公理的意味論の重要性**: 公理的意味論は、プログラムの「保証すべき性質」に焦点を当て、仕様記述の本質に最も近い意味論である。

3. **拡張と発展**: 分離論理、並行分離論理、関係的Hoare論理など、Hoare論理は現代的な課題に対応するために拡張され続けている。

4. **実用化**: 契約プログラミング、静的解析ツール、定理証明器など、Hoare論理の概念は実用的な検証ツールの基盤となっている。

### 14.2 仕様記述への示唆

**Hoare論理の視点から見た仕様:**

- **仕様 = 事前条件 + 事後条件の集合**: 許容される振る舞いの論理的記述
- **ループ不変条件**: 状態遷移の不変性を表現
- **検証可能性**: 仕様が検証可能であることが重要

**U-D-Aモデルとの関連:**

- **D（対象領域）**: 事前条件で制約される入力空間
- **A（許容集合）**: 事後条件を満たす状態・遷移の集合
- **検証**: U中の要素がDに属し、実行後にAの条件を満たすことの証明

### 14.3 今後の展望

1. **自動化の向上**: 機械学習やニューラル定理証明による検証条件の自動証明
2. **スケーラビリティの改善**: モジュラー検証、合成的推論の強化
3. **新しいプログラミングパラダイムへの対応**: 量子コンピューティング、確率的プログラミングなど
4. **実用ツールの普及**: より使いやすい検証ツールの開発

---

## 参考文献リスト

### 基礎理論
- [Hoare logic - Wikipedia](https://en.wikipedia.org/wiki/Hoare_logic)
- [Axiomatic semantics - Wikipedia](https://en.wikipedia.org/wiki/Axiomatic_semantics)
- [Tony Hoare - Contributions - Hoare Logic](https://cs.stanford.edu/people/eroberts/courses/soco/projects/2008-09/tony-hoare/logic.html)
- [Ten Years of Hoare's Logic: A Survey - Krzysztof R. Apt](https://www.cs.cornell.edu/courses/cs6860/2019sp/Handouts/Apt10years.pdf)

### 公理的意味論
- [Axiomatic Semantics and Hoare-style Verification - CMU](https://www.cs.cmu.edu/~aldrich/courses/17-355-18sp/notes/notes11-hoare-logic.pdf)
- [Axiomatic Semantics - University of Iowa](https://homepage.divms.uiowa.edu/~slonnegr/plf/Book/Chapter11.pdf)
- [Semantics of Programming Language - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/semantics-of-programming-language)
- [Operation, Axiomatic, Denotational - CSU](https://www.cs.csub.edu/~melissa/cs350-f15/notes/notes04b.html)
- [Semantics - LMU](https://cs.lmu.edu/~ray/notes/semantics/)

### Hoare三つ組と証明規則
- [Hoare Logic for control structures - Xavier Leroy](http://xavierleroy.org/control-structures/book/main016.html)
- [Software Foundations - Hoare Logic, Part I](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)
- [Reasoning About Code (Hoare Logic) - University of Washington](https://courses.cs.washington.edu/courses/cse331/13sp/conceptual-info/hoare-logic.pdf)
- [Lecture Notes: Hoare Logic - CMU](https://www.cs.cmu.edu/~aldrich/courses/654-sp09/notes/3-hoare-notes.pdf)
- [Hoare Logic: Proving Programs Correct - CMU](https://www.cs.cmu.edu/~aldrich/courses/654-sp07/slides/7-hoare.pdf)
- [Program Verification with Hoare Logic - Aarhus](https://cs.au.dk/~amoeller/talks/hoare.pdf)

### 述語変換器意味論
- [Predicate transformer semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
- [Weakest-Precondition Reasoning - University of Maryland](https://www.cs.umd.edu/~mvz/handouts/weakest-precondition.pdf)
- [Weakest Precondition - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/weakest-precondition)
- [Weakest precondition - Encyclopedia.com](https://www.encyclopedia.com/computing/dictionaries-thesauruses-pictures-and-press-releases/weakest-precondition)
- [Computing Preconditions and Postconditions of While Loops - Springer](https://link.springer.com/chapter/10.1007/978-3-642-23283-1_13)
- [Weakest precondition - Oxford Reference](https://www.oxfordreference.com/viewbydoi/10.1093/oi/authority.20110803121433218)

### 部分正当性と完全正当性
- [Introduction to Deductive Program Verification - UT Austin](https://www.cs.utexas.edu/~isil/cs389L/HoareLogic-6up.pdf)
- [Hoare logic Total correctness - Cambridge](https://www.cl.cam.ac.uk/teaching/1819/HLog+ModC/slides/lecture6-4.pdf)
- [Total Correctness Specification - Cambridge](https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/Oct17.pdf)
- [Hoare Logic - std::bodun::blog](https://www.bodunhu.com/blog/posts/hoare-logic/)
- [Lecture: Program Semantics — Hoare Logic - Lean Forward](https://lean-forward.github.io/logical-verification/2018/32_notes.html)

### 健全性と完全性
- [Soundness and Completeness of Hoare Logic - NTU](https://www.im.ntu.edu.tw/~tsay/dokuwiki/lib/exe/fetch.php?media=courses:ssv2024:hoare_logic_soundness_completeness.pdf)
- [Soundness and Completeness - Cornell](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture10.pdf)
- [Soundness and Completeness of an Axiom System for Program Verification - SIAM](https://epubs.siam.org/doi/10.1137/0207005)
- [On the soundness and completeness of generalized Hoare logic - ResearchGate](https://www.researchgate.net/publication/238286887_On_the_soundness_and_completeness_of_generalized_Hoare_logic)
- [A language independent proof of the soundness and completeness - ScienceDirect](https://www.sciencedirect.com/science/article/pii/0890540189900187)
- [Expressiveness and the Completeness of Hoare's Logic](https://core.ac.uk/download/pdf/82230597.pdf)
- [Hoare Logic in the Abstract - Springer](https://link.springer.com/chapter/10.1007/11874683_33)

### 検証条件生成
- [Verification condition generator - Wikipedia](https://en.wikipedia.org/wiki/Verification_condition_generator)
- [Verification Condition Generation Via Theorem Proving - Springer](https://link.springer.com/chapter/10.1007/11916277_25)
- [Verification Condition Generation Via Theorem Proving - University of Florida](https://www.ece.ufl.edu/wp-content/uploads/sites/119/publications/lpar06.pdf)
- [A Certified Multi-prover Verification Condition Generator - Inria](https://inria.hal.science/hal-00639977v1/document)
- [Automated theorem proving - Wikipedia](https://en.wikipedia.org/wiki/Automated_theorem_proving)
- [Using Automated Theorem Provers to Certify Auto-Generated Aerospace Software - NASA](https://ntrs.nasa.gov/api/citations/20040068177/downloads/20040068177.pdf)
- [Neural Theorem Proving for Verification Conditions - arXiv](https://arxiv.org/html/2601.18944)
- [Neural Theorem Proving for Verification Conditions - arXiv PDF](https://arxiv.org/pdf/2601.18944)

### 分離論理
- [Separation logic - Wikipedia](https://en.wikipedia.org/wiki/Separation_logic)
- [Concurrent Separation Logic - Harvard](https://read.seas.harvard.edu/~kohler/class/cs260r-17/brookes16concurrent.pdf)
- [Concurrent Separation Logic (CSL) - ResearchGate](https://www.researchgate.net/publication/372748817_Concurrent_Separation_Logic_CSL)
- [Specifying Concurrent Programs in Separation Logic - arXiv](https://arxiv.org/pdf/1904.07136)
- [Separation Logic and Concurrency - IMDEA](https://software.imdea.org/~aleks/oplss16/notes.pdf)
- [Compositional Verification in Concurrent Separation Logic - arXiv](https://arxiv.org/pdf/2508.18115)
- [Towards Concurrent Quantitative Separation Logic - Dagstuhl](https://drops.dagstuhl.de/storage/00lipics/lipics-vol243-concur2022/LIPIcs.CONCUR.2022.25/LIPIcs.CONCUR.2022.25.pdf)
- [Simuliris: A Separation Logic Framework - Iris Project](https://iris-project.org/pdfs/2022-popl-simuliris.pdf)
- [Separation Logic for Concurrency and Persistency - Iris Project](https://iris-project.org/pdfs/2023-phd-vindum.pdf)
- [VeriFast's separation logic - arXiv](https://arxiv.org/abs/2505.04500)

### 最新研究（2025）
- [Encode the ∀∃ Relational Hoare Logic into Standard Hoare Logic - ACM](https://dl.acm.org/doi/10.1145/3763138)
- [A Formal Framework for Naturally Specifying and Verifying Sequential Algorithms - Springer](https://link.springer.com/chapter/10.1007/978-3-031-98208-8_4)
- [Axiomatic semantics for compiler verification - ACM](https://dl.acm.org/doi/10.1145/2854065.2854083)
- [Axiomatic Semantics for Compiler Verification - Saarland](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2016_Axiomatic-Semantics.pdf)

### 教科書・講義ノート
- [Lecture 5: Axiomatic Semantics and Hoare Logic - UT Austin](https://www.cs.utexas.edu/~bornholt/courses/cs345h-24sp/lectures/5-axiomatic/)
- [The Axiomatic Semantics of Programs Based on Hoare's Logic - ResearchGate](https://www.researchgate.net/publication/220197227_The_Axiomatic_Semantics_of_Programs_Based_on_Hoare's_Logic)
- [Hoare Logic - Nanjing University](https://cs.nju.edu.cn/hongjin/teaching/semantics/07_Hoare.pdf)
- [Introduction to Axiomatic Semantics - UC Davis](https://www.cs.ucdavis.edu/~su/teaching/ecs240-w17/lectures/lecture10-11.pdf)
- [Concepts of Programming Languages - Semantics - KSU](https://faculty.ksu.edu.sa/sites/default/files/06-semantics.pdf)

---

**調査完了日**: 2026-02-14
**調査者**: researcher-07
**タスクID**: #41
