# 定理証明器の比較と実用

## 概要

本レポートは、現代の定理証明器（theorem provers）を包括的に調査し、主要なシステムの比較、実用的な応用事例、および産業界での利用状況を明らかにすることを目的とする。

---

## 1. 定理証明器の分類

定理証明器は、大きく2つのカテゴリに分類される:

### 1.1 対話的定理証明器（Interactive Theorem Provers, ITPs）

**特徴:**
- ユーザーが証明の構築を対話的に導く
- 強力な表現力と柔軟性
- 複雑な数学的定理やプログラムの正しさの証明に適している

**主要システム:**
- Coq（現在はRocqに改名）
- Isabelle/HOL
- Lean
- HOL4, HOL Light
- Agda
- Idris
- PVS

**参考文献:**
- [Proof assistant - Wikipedia](https://en.wikipedia.org/wiki/Proof_assistant)
- [Interactive Theorem Proving](https://itp-conference.github.io/)

### 1.2 自動定理証明器（Automated Theorem Provers, ATPs）

**特徴:**
- ユーザーの介入を最小限に抑えて自動的に証明を探索
- SMTソルバーなどが含まれる
- プログラム検証や制約解決に適している

**主要システム:**
- Z3
- Yices
- CVC5
- Vampire
- E prover

**参考文献:**
- [Automated theorem proving - Wikipedia](https://en.wikipedia.org/wiki/Automated_theorem_proving)
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)

---

## 2. 主要な対話的定理証明器の比較

### 2.1 Coq（Rocq）

#### 概要

Coqは、対話的定理証明の分野で多くの機能を先駆的に導入したシステムである。現在は**Rocq Prover**と改名されている。

**参考文献:**
- [Welcome to a World of Rocq](https://rocq-prover.org/)

#### 主要な特徴

- **タクティクベースの証明開発**: 証明をステップバイステップで構築
- **証明からの実行可能プログラムの抽出**: 証明された仕様から実際のプログラムを生成
- **モジュールシステム**: 大規模な開発を整理するためのモジュール機構

#### 理論的基盤

Coq（Rocq）は**依存型理論（Calculus of Inductive Constructions, CIC）**に基づいている。

**参考文献:**
- [Coq and Lean: Powerful Interactive Theorem Provers - Open Source For You](https://www.opensourceforu.com/2023/10/coq-and-lean-powerful-interactive-theorem-provers/)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 主要なプロジェクト

- **CompCert**: 検証済みCコンパイラ
- **4色定理の証明**: 数学的定理の機械検証
- **Verified Software Toolchain**: Cライクなプログラムの証明

**参考文献:**
- [Welcome to a World of Rocq](https://rocq-prover.org/)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### コミュニティ

Leanと比較して、より大きく古いコミュニティを持つ。

**参考文献:**
- [My first impressions from a few weeks with Lean and Coq](https://ntietz.com/blog/first-impressions-of-lean-and-coq/)

### 2.2 Isabelle/HOL

#### 概要

Isabelle/HOLは、LCF伝統に由来するHOL（Higher-Order Logic）ファミリーの証明器である。

**参考文献:**
- [HOL Interactive Theorem Prover](https://hol-theorem-prover.org/)

#### 主要な特徴

- **高階論理（HOL）に基づく**: 一階論理よりも強力な表現力
- **LCFアプローチ**: 小さな信頼できるカーネルに基づく設計
- **依存型をサポートしない**: 一部の証明には向かない

**参考文献:**
- [Comparison of Two Theorem Provers: Isabelle/HOL and Coq - arXiv](https://arxiv.org/pdf/1808.09701)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 主要なプロジェクト

- **seL4マイクロカーネルの検証**: OSカーネルの完全な形式検証
- **分散アルゴリズムの検証**: Martin Kleppmannによる研究

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### アーキテクチャ

IsabelleはLCFアプローチを実装しており、証明された定理の抽象データ型を定義するライブラリとして実装されている。この型の新しいオブジェクトは、高階論理の推論規則に対応するライブラリ内の関数を使用してのみ作成できる。

**参考文献:**
- [The Common HOL Platform - arXiv](https://arxiv.org/pdf/1507.08718)

### 2.3 Lean

#### 概要

Leanは、Microsoft ResearchのLeonardo de Mouraによって2013年から開発された、対話的定理証明と自動推論の両方に適したシステムである。

**参考文献:**
- [Frequently Asked Questions - Lean Lang](https://lean-lang.org/faq/)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 主要な特徴

- **依存型理論に基づく**: Coqと同様にCICに基づく
- **高性能**: Lean 4はCにコンパイルされ、「定理証明器として速い」のではなく「実際に速い」
- **大規模な数学ライブラリ**: Mathlibは190万行で、史上最大の一貫した数学ライブラリ
- **数学者に人気**: ユーザーフレンドリーな機能と活発なコミュニティ

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)
- [My first impressions from a few weeks with Lean and Coq](https://ntietz.com/blog/first-impressions-of-lean-and-coq/)

#### 理論的基盤

Leanは依存型理論に基づき、信頼できる小さなカーネルに渡される明示的な証明を構築する。

**参考文献:**
- [Comparison of Two Theorem Provers: Isabelle/HOL and Coq - arXiv](https://arxiv.org/pdf/1808.09701)

#### コミュニティと採用

対話的定理証明器（ITP）であるCoq、Isabelle/HOL、Leanは、学界と産業界に多くのアクティブユーザーを持ち、GitHubやStack Overflowなどの開発者プラットフォームにおいてプログラミング言語に匹敵する人気を持つ。

**参考文献:**
- [Lessons for Interactive Theorem Proving Researchers from a Survey of Coq Users - Springer](https://link.springer.com/article/10.1007/s10817-025-09720-1)

### 2.4 HOL4とHOL Light

#### HOL4

**特徴:**
- HOL98をベースにHOL Lightのアイデアとツールを組み込む
- Moscow MLまたはPoly/MLでビルド可能

**参考文献:**
- [HOL Interactive Theorem Prover](https://hol-theorem-prover.org/)
- [The Common HOL Platform - arXiv](https://arxiv.org/pdf/1507.08718)

#### HOL Light

**特徴:**
- **非常にシンプルな論理コア**: 他のHOLシステムと比較して、はるかにシンプルな論理コアを使用
- **レガシーコードが少ない**: システムにシンプルで整然とした感触を与える
- **Objective CAML（OCaml）で実装**
- **産業規模の検証に使用**: シンプルさにもかかわらず、他のHOLバージョンに匹敵する、あるいは一部の領域ではそれ以上の定理証明能力を提供

**参考文献:**
- [The HOL Light theorem prover](https://hol-light.github.io/)
- [The Common HOL Platform - arXiv](https://arxiv.org/pdf/1507.08718)

### 2.5 PVS（Prototype Verification System）

#### 概要

PVSは、HOLシステムとは根本的に異なるアーキテクチャを持つ定理証明器である。

#### 主要な特徴

- **LCFアプローチではない**: 小さなカーネルではなく、チェッカーと多くの自動化を含む大きなモノリシックシステム
- **述語サブタイプと依存型を多用**
- **Common Lispで実装**: ユーザーインターフェースはEmacs上に構築
- **手続き的証明スタイル**: HOLシステムやPVSは手続き的スタイルを使用

**対比:**
HOLシステムは、証明された定理の抽象データ型を定義するライブラリとして実装され、LCFアプローチに従う。これらの関数が正しく実装されている限り、システムで証明されたすべての定理は妥当でなければならない。

**参考文献:**
- [The Common HOL Platform - arXiv](https://arxiv.org/pdf/1507.08718)

### 2.6 AgdaとIdris

#### 共通点

AgdaとIdrisは、依存型を持つ関数型言語であり、依存パターンマッチングをサポートし、プログラムと証明の両方を書くために使用できる。

**参考文献:**
- [Agda vs. Coq vs. Idris - Meta-cedille blog](https://whatisrt.github.io/dependent-types/2020/02/18/agda-vs-coq-vs-idris.html)

#### Agda

**特徴:**
- **依存型付き関数型プログラミング言語および証明支援器**
- **暗黙引数の優れた処理**: Idrisよりも高速で便利
- **対話的な証明項の精緻化**: Epigram-Agdaスタイルの対話をサポート

**参考文献:**
- [Agda: A dependently typed functional programming language and proof assistant](https://hackage.haskell.org/package/Agda)
- [Agda's documentation - Dependent types](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/what-is-agda.html)
- [Agda vs. Coq vs. Idris - Meta-cedille blog](https://whatisrt.github.io/dependent-types/2020/02/18/agda-vs-coq-vs-idris.html)

#### Idris

**特徴:**
- **汎用プログラミングを重視**: 定理証明よりもプログラミングを強調
- **副作用の管理とドメイン固有言語の埋め込みを優先**
- **両方の対話スタイルをサポート**: タクティク呼び出しとEpigram-Agdaスタイルの両方
- **モジュラーバックエンド**: Chez Scheme、Racket、JavaScript（ブラウザーとNode.js）、Cのバックエンドを含む

**課題:**
- 暗黙引数の弱い処理により、タクティクを使用する際にも多くの追加引数を提供する必要がある
- コンパイル時間が長く、ランダムに動作しない場合がある

**参考文献:**
- [Idris (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Idris_(programming_language))
- [Frequently Asked Questions - Idris documentation](https://docs.idris-lang.org/en/latest/faq/faq.html)
- [Agda vs. Coq vs. Idris - Meta-cedille blog](https://whatisrt.github.io/dependent-types/2020/02/18/agda-vs-coq-vs-idris.html)

---

## 3. 自動定理証明器とSMTソルバー

### 3.1 SMT（Satisfiability Modulo Theories）とは

**定義:**

SMTは、数学的公式が充足可能かどうかを判定する問題であり、実数、整数、リスト、配列、ビットベクトル、文字列などのさまざまなデータ構造を含むより複雑な公式にブール充足可能性を一般化したものである。

**参考文献:**
- [Satisfiability modulo theories - Wikipedia](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)

### 3.2 SMTソルバーと自動定理証明器の関係

**重複と違い:**

SMT解決と自動定理証明（ATP）の間には実質的な重複がある。一般的に、自動定理証明器は量化子を伴う完全な一階論理のサポートに焦点を当てるのに対し、SMTソルバーはさまざまな理論のサポートに焦点を当てる。ATPは量化子が多い問題に優れ、SMTソルバーは量化子のない大規模な問題に優れている。

**参考文献:**
- [Satisfiability modulo theories - Wikipedia](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)

### 3.3 Z3

#### 概要

Z3は、Microsoftによって開発された充足可能性モジュロ理論（SMT）ソルバーである。Microsoft Research Redmondのソフトウェア工学研究（RiSE）グループで開発され、ソフトウェア検証とプログラム解析に起因する問題の解決を対象としている。

**参考文献:**
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)
- [GitHub - Z3Prover/z3](https://github.com/Z3Prover/z3)

#### サポートする理論

Z3は以下をサポートする:
- 算術
- 固定サイズビットベクトル
- 拡張配列
- データ型
- 未解釈関数
- 量化子

**参考文献:**
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)

#### モデルベースアプローチ

Z3の効率と能力の背後には、モデルベースのアプローチがある。

**参考文献:**
- [Model-based approach behind Z3 theorem prover's efficiency, power - Microsoft Research](https://www.microsoft.com/en-us/research/blog/the-inner-magic-behind-the-z3-theorem-prover/)

#### 他のソルバーとの比較

**汎用性:**
Z3は、SMTソルバーのスイスアーミーナイフとして特に優れており、さまざまな問題タイプにわたって汎用性を提供する。ただし、特化したソルバーは特定の問題領域でZ3を上回る可能性がある。

**例:**
Yicesは、プログラマーが行う固定ビット整数値を使用する種類の作業では、より高速である可能性がある。

**参考文献:**
- [Benchmarking theorem provers for programming tasks: yices vs. z3 - Daniel Lemire's blog](https://lemire.me/blog/2020/11/08/benchmarking-theorem-provers-for-programming-tasks-yices-vs-z3/)

#### 応用

sbvライブラリは、HaskellプログラムのSMTベースの検証を提供し、ユーザーがZ3、ABC、Boolector、cvc5、MathSAT、Yicesなどの多数のソルバーから選択できる。

**参考文献:**
- [Satisfiability modulo theories - Wikipedia](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)

### 3.4 その他の自動定理証明器

#### Vampire

Vampireは、一階論理の自動定理証明に特化した高性能システムである。

**参考文献:**
- [Vampire](https://vprover.github.io/)

#### ACL2

ACL2は、プログラミング言語、一階論理理論、およびBoyer-Moore伝統における対話的および自動モードの両方を持つ定理証明器である。

**参考文献:**
- [Automated Theorem Proving - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/automated-theorem-proving)

---

## 4. 学習曲線と使いやすさ

### 4.1 学習曲線の経験

#### 経験豊富なインストラクターの視点

証明支援器の経験があるインストラクターは、比較的平坦な学習曲線を報告しており、優秀な学生やプログラミング経験のある学生はLeanを楽に学習する。

**参考文献:**
- [Teaching with Computer-Based Proof Assistants - CMS Notes](https://notes.math.ca/en/article/teaching-with-computer-based-proof-assistants-perspectives-from-instructors-of-mathematics/)

#### 初心者の経験

プログラミング経験のないインストラクターと学生の両方にとって、学習曲線は最初は急である。

**個人差:**
多くの学生にとってLeanを学ぶことは非常に役に立つが、コースの終わりまでにLeanが「しっくりこない」学生もいる。優秀な学生は本当に多くを学び、平均的な学生の一部も満足しているが、弱い学生は何も得られず、ITPは数学的に成熟した学生に最も効果的である。

**参考文献:**
- [Teaching with Computer-Based Proof Assistants - CMS Notes](https://notes.math.ca/en/article/teaching-with-computer-based-proof-assistants-perspectives-from-instructors-of-mathematics/)

### 4.2 主要な使いやすさの課題

#### インストールとUI理解

主な障壁は、Leanのインストールに関する問題と、Leanユーザーインターフェースの読み方の誤解であるように見える。

**参考文献:**
- [Teaching with Computer-Based Proof Assistants - CMS Notes](https://notes.math.ca/en/article/teaching-with-computer-based-proof-assistants-perspectives-from-instructors-of-mathematics/)

#### 証明状態の理解

ユーザーにとっての主要な障害は、証明を成功裏に見つけるために証明器を導くために証明状態を理解することである。

**参考文献:**
- [A Usability Evaluation of Interactive Theorem Provers Using Focus Groups - Springer](https://link.springer.com/chapter/10.1007/978-3-319-15201-1_1)

### 4.3 使用パターン

対話的定理証明器は、コンピュータサイエンスと数学の多くの分野で重要なツールであるが、専門家でさえ効果的に使用することは困難である。

**効率性のボトルネック:**

対話的定理証明器の有効性は向上し、証明プロセスのボトルネックが有効性から効率性に移った。大きな定理は原理的には証明可能であるが、ユーザーがシステムと対話するのに多大な労力がかかる。

**参考文献:**
- [An Observation Study of Proof Assistant Users - ACM](https://dl.acm.org/doi/pdf/10.1145/3720426)

---

## 5. 産業界での応用と成功事例

### 5.1 ハードウェア検証

#### プロセッサの検証

AMD、Intelなどは、プロセッサで除算やその他の操作が正しく実装されていることを検証するために自動定理証明を使用している。

**ACL2の成功:**

ACL2は、Pentium FDIV バグがハードウェアの正しさを経営陣にとって突如として興味深いものにした後、AMDの浮動小数点除算の検証を含む、注目すべき産業的成功を達成した。

**参考文献:**
- [Automated Theorem Proving - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/automated-theorem-proving)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

### 5.2 CompCert: 検証済みCコンパイラ

#### 概要

CompCertは、Rocq（旧Coq）証明支援器を使用して開発された検証済みCコンパイラである。

**参考文献:**
- [Welcome to a World of Rocq](https://rocq-prover.org/)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 産業界での採用

CompCertは、信頼できる最適化されたコードを生成するため、Airbusのツールチェーンに導入されている。形式的証明がなければ、認証当局はコンパイラ最適化の使用を容認しない。

**参考文献:**
- [Welcome to a World of Rocq](https://rocq-prover.org/)

#### 検証の質

CompCertの検証の質は経験的に実証されている。CompCertには機能的正当性証明が付属しており、テストでは、他のすべてのコンパイラで見つかったミドルエンドのバグが存在しない。2011年初頭の時点で、Csmithが誤ったコードエラーを見つけることができなかった唯一のコンパイラであった。

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

### 5.3 seL4: 検証済みマイクロカーネル

#### 概要

seL4オペレーティングシステムマイクロカーネルは、Isabelleを使用して検証されている。

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)
- [seL4 Proofs](https://sel4.systems/Verification/proofs.html)

#### 検証のコスト

seL4の形式検証には約20人年を要し、マイクロカーネル自体の開発には2.2人年であったのと比較される。

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 最近の進歩（2025-2026）

最近の進歩は、自動化がこれらの検証作業を改善していることを示している。

**AutoReal-Proverの成果:**

AutoReal-Proverは、seL4の10の証明カテゴリすべてにわたって、seL4指定の重要理論からの660の定理で51.67%の証明成功率を達成し、seL4での以前の試み（27.06%）を大幅に上回った。Archive of Formal Proofsからの3つのセキュリティ関連プロジェクトに適用した場合、53.88%の証明成功率を達成した。

**参考文献:**
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv](https://arxiv.org/abs/2602.08384)
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv HTML](https://arxiv.org/html/2602.08384)

### 5.4 その他の産業応用

#### 航空宇宙ソフトウェア

NASAなどの機関は、自動生成された航空宇宙ソフトウェアを認証するために自動定理証明器を使用している。

**参考文献:**
- [Using Automated Theorem Provers to Certify Auto-Generated Aerospace Software - NASA](https://ntrs.nasa.gov/api/citations/20040068177/downloads/20040068177.pdf)

#### 高品質ソフトウェア設計

KIVは、高品質ソフトウェアの検証に特に適した対話的検証器であり、エアバッグコントローラーの検証などの産業応用がある。

**参考文献:**
- [AUTOMATED THEOREM PROVING IN HIGH-QUALITY SOFTWARE DESIGN - NASA](https://ntrs.nasa.gov/api/citations/20010084145/downloads/20010084145.pdf)

### 5.5 キラーアプリケーションの重要性

今日繁栄しているシステムは共通のパターンを共有している: アプローチが大規模に機能することを証明したキラーアプリケーションである。

- **Coq**: CompCert
- **Isabelle**: seL4

これらの存在証明は重要であった。

**参考文献:**
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv HTML](https://arxiv.org/html/2602.08384)

---

## 6. 最新の研究動向（2025-2026）

### 6.1 ITP 2026カンファレンス

**開催予定:**

国際対話的定理証明会議（ITP 2026）は、2026年7月26-29日にポルトガルのリスボンで、FLoC'26の一部として開催される。ITPは、対話的定理証明とその応用のすべての側面に関する独自の研究を記述する投稿を歓迎する。

**参考文献:**
- [ITP 2026](https://itp-conference-2026.github.io/)
- [ITP: Interactive Theorem Proving](http://www.wikicfp.com/cfp/program?id=1792)

### 6.2 LLMベースの定理証明

#### Dafnyへの応用

MiniF2F-Dafnyは、数学的推論ベンチマークminiF2Fの自動定理証明器Dafnyへの最初の翻訳を表している。以前、このベンチマークは対話的定理証明器（Lean、Isabelle、HOL Light、Metamath）にのみ存在していた。

**参考文献:**
- [MiniF2F-Dafny: LLM-Guided Mathematical Theorem Proving - POPL 2026](https://popl26.sigplan.org/details/dafny-2026-papers/16/MiniF2F-Dafny-LLM-Guided-Mathematical-Theorem-Proving-via-Auto-Active-Verification)

#### 一般的な動向

LLMベースの定理証明器は、活発な研究領域となっており、深層学習を定理証明に応用する新しいアプローチが登場している。

**参考文献:**
- [LLM-Based Theorem Provers - Emergent Mind](https://www.emergentmind.com/topics/llm-based-theorem-provers)
- [A Survey on Deep Learning for Theorem Proving - arXiv](https://arxiv.org/html/2404.09939v1)

### 6.3 教育への応用

対話的定理証明器（ITP）は、もともと形式検証のために開発されたが、構造化されたフィードバックを提供し、CS学生の既存の技術スキルとうまく整合する、有望な教育ツールとして登場した。

**参考文献:**
- [Interactive Theorem Provers for Proof Education - ACM](https://dl.acm.org/doi/10.1145/3758317.3759679)

### 6.4 Prologの検証

最近の研究では、Prologプログラムの検証のための自動定理証明が探求されている。

**参考文献:**
- [Automated Theorem Proving for Prolog Verification - arXiv](https://arxiv.org/abs/2601.03849)

---

## 7. 定理証明器選択のガイドライン

### 7.1 用途別の推奨

#### 数学的定理の形式化

**推奨: Lean**
- 大規模な数学ライブラリ（Mathlib）
- 活発な数学コミュニティ
- ユーザーフレンドリー

**代替: Coq/Rocq, Isabelle**

**参考文献:**
- [Teaching "Foundations of Mathematics" with the LEAN Theorem Prover - arXiv](https://arxiv.org/html/2501.03352v2)

#### ソフトウェア検証

**推奨: Coq/Rocq, Isabelle, Dafny**
- Coq/Rocq: プログラム抽出、CompCertなどの実績
- Isabelle: seL4などの大規模検証の実績
- Dafny: 自動検証との統合

**参考文献:**
- [Welcome to a World of Rocq](https://rocq-prover.org/)
- [seL4 Proofs](https://sel4.systems/Verification/proofs.html)

#### ハードウェア検証

**推奨: ACL2, HOL Light**
- ACL2: AMD、Intelでの実績
- HOL Light: 産業規模の応用

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### プログラム解析・制約解決

**推奨: Z3, その他のSMTソルバー**
- 高速な自動推論
- 多くのプログラミング言語との統合

**参考文献:**
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)

### 7.2 技術的考慮事項

#### 依存型が必要か

**必要な場合: Coq/Rocq, Lean, Agda, Idris**
**不要な場合: Isabelle/HOL, HOL Light**

**参考文献:**
- [Comparison of Two Theorem Provers: Isabelle/HOL and Coq - arXiv](https://arxiv.org/pdf/1808.09701)

#### 自動化の程度

**高度な自動化: SMTソルバー（Z3など）, Isabelle**
**対話的: Coq/Rocq, Lean, Agda**

#### 学習コストとコミュニティサポート

**大きなコミュニティ: Coq/Rocq, Lean, Isabelle**
**ニッチだが専門的: Agda, Idris, PVS**

**参考文献:**
- [My first impressions from a few weeks with Lean and Coq](https://ntietz.com/blog/first-impressions-of-lean-and-coq/)

---

## 8. 課題と今後の展望

### 8.1 現在の課題

#### スケーラビリティ

大規模なプロジェクトの検証は、依然として時間と専門知識を要する。seL4の検証が20人年を要したことは、この課題を示している。

**参考文献:**
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

#### 学習曲線

証明支援器の使いやすさは向上しているが、初心者にとって学習曲線は依然として急である。

**参考文献:**
- [Teaching with Computer-Based Proof Assistants - CMS Notes](https://notes.math.ca/en/article/teaching-with-computer-based-proof-assistants-perspectives-from-instructors-of-mathematics/)

#### 自動化の限界

対話的定理証明器の有効性は向上したが、ユーザーとシステムの対話には依然として多大な労力がかかる。

**参考文献:**
- [An Observation Study of Proof Assistant Users - ACM](https://dl.acm.org/doi/pdf/10.1145/3720426)

### 8.2 今後の展望

#### AI/LLMの統合

LLMを使用した定理証明の自動化は、急速に進歩している。seL4での最近の成果（51.67%の証明成功率）は、この方向性の可能性を示している。

**参考文献:**
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv](https://arxiv.org/abs/2602.08384)

#### より強力な自動化

Matryoshkaプロジェクトなどは、強力な高階自動化を通じて高速な対話的検証を目指している。

**参考文献:**
- [Matryoshka: Fast Interactive Verification](https://matryoshka-project.github.io/)

#### 教育への統合

証明支援器の教育ツールとしての利用は拡大しており、プログラミング教育と形式手法教育の融合が進んでいる。

**参考文献:**
- [Interactive Theorem Provers for Proof Education - ACM](https://dl.acm.org/doi/10.1145/3758317.3759679)

#### 産業界での普及

CompCertやseL4のような成功事例は、他の産業分野への形式検証の普及を促進する可能性がある。

---

## 9. まとめ

### 9.1 主要な発見

1. **多様なエコシステム**: 対話的定理証明器（Coq/Rocq, Isabelle, Lean）と自動定理証明器（Z3などのSMTソルバー）は、それぞれ異なるニーズに対応している。

2. **成功事例の重要性**: CompCert（Coq）とseL4（Isabelle）は、定理証明器が産業規模の検証に適用可能であることを実証した。

3. **理論的基盤の違い**:
   - 依存型理論（CIC）: Coq/Rocq, Lean
   - 高階論理（HOL）: Isabelle, HOL Light, HOL4
   - SMT: Z3などのソルバー

4. **学習曲線の課題**: 初心者にとって証明支援器の学習は依然として困難であるが、数学的に成熟した学生やプログラミング経験のある学生にとっては効果的である。

5. **自動化の進歩**: LLMや深層学習を用いた定理証明の自動化が急速に進展しており、証明成功率が向上している。

### 9.2 仕様記述への示唆

**定理証明器と仕様:**

- 定理証明器は、仕様を形式的に記述し、その性質を検証するための強力なツールである
- 対話的定理証明器は、複雑な仕様の正しさを証明するために使用される
- SMTソルバーは、プログラムが仕様を満たすかどうかを自動的にチェックするために使用される

**実用的な選択:**

- **教育・研究**: Lean（数学）、Coq/Rocq（ソフトウェア）
- **産業検証**: Isabelle（大規模システム）、Coq/Rocq（コンパイラ）、Z3（プログラム解析）
- **ハードウェア**: ACL2、HOL Light

### 9.3 今後の研究方向

1. **AI統合の深化**: LLMと定理証明器のさらなる統合
2. **使いやすさの向上**: UIの改善、証明状態の可視化
3. **教育への応用拡大**: より多くの学生が形式手法を学ぶ機会の提供
4. **産業界での普及**: CompCert、seL4に続く成功事例の創出
5. **相互運用性**: 異なる定理証明器間での証明の移植と再利用

---

## 参考文献リスト

### 概要と分類
- [Proof assistant - Wikipedia](https://en.wikipedia.org/wiki/Proof_assistant)
- [Interactive Theorem Proving](https://itp-conference.github.io/)
- [Automated theorem proving - Wikipedia](https://en.wikipedia.org/wiki/Automated_theorem_proving)
- [Z3 Theorem Prover - Wikipedia](https://en.wikipedia.org/wiki/Z3_Theorem_Prover)
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html)

### Coq/Rocq
- [Welcome to a World of Rocq](https://rocq-prover.org/)
- [Coq and Lean: Powerful Interactive Theorem Provers - Open Source For You](https://www.opensourceforu.com/2023/10/coq-and-lean-powerful-interactive-theorem-provers/)
- [Lessons for Interactive Theorem Proving Researchers from a Survey of Coq Users - Springer](https://link.springer.com/article/10.1007/s10817-025-09720-1)

### Isabelle
- [HOL Interactive Theorem Prover](https://hol-theorem-prover.org/)
- [Comparison of Two Theorem Provers: Isabelle/HOL and Coq - arXiv](https://arxiv.org/pdf/1808.09701)

### Lean
- [Frequently Asked Questions - Lean Lang](https://lean-lang.org/faq/)
- [My first impressions from a few weeks with Lean and Coq](https://ntietz.com/blog/first-impressions-of-lean-and-coq/)
- [Teaching "Foundations of Mathematics" with the LEAN Theorem Prover - arXiv](https://arxiv.org/html/2501.03352v2)
- [Topic: Lean vs other systems](https://leanprover-community.github.io/archive/stream/113488-general/topic/Lean.20vs.20other.20systems.html)

### HOL Systems
- [The HOL Light theorem prover](https://hol-light.github.io/)
- [The Common HOL Platform - arXiv](https://arxiv.org/pdf/1507.08718)
- [HOL Light: A tutorial introduction - Springer](https://link.springer.com/chapter/10.1007/BFb0031814)
- [Releases - HOL-Theorem-Prover/HOL](https://github.com/HOL-Theorem-Prover/HOL/releases)

### Agda & Idris
- [Agda vs. Coq vs. Idris - Meta-cedille blog](https://whatisrt.github.io/dependent-types/2020/02/18/agda-vs-coq-vs-idris.html)
- [Idris (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Idris_(programming_language))
- [Frequently Asked Questions - Idris documentation](https://docs.idris-lang.org/en/latest/faq/faq.html)
- [Agda: A dependently typed functional programming language and proof assistant](https://hackage.haskell.org/package/Agda)
- [Agda's documentation - Dependent types](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/what-is-agda.html)
- [Agda](https://agda.github.io/agda/)

### SMT Solvers & Z3
- [Satisfiability modulo theories - Wikipedia](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
- [GitHub - Z3Prover/z3](https://github.com/Z3Prover/z3)
- [Benchmarking theorem provers for programming tasks: yices vs. z3 - Daniel Lemire's blog](https://lemire.me/blog/2020/11/08/benchmarking-theorem-provers-for-programming-tasks-yices-vs-z3/)
- [Model-based approach behind Z3 theorem prover's efficiency, power - Microsoft Research](https://www.microsoft.com/en-us/research/blog/the-inner-magic-behind-the-z3-theorem-prover/)
- [Z3: An Efficient SMT Solver - Springer](https://link.springer.com/content/pdf/10.1007/978-3-540-78800-3_24.pdf)
- [Lessons Learned With the Z3 SAT/SMT Solver - John D. Cook](https://www.johndcook.com/blog/2025/03/17/lessons-learned-with-the-z3-sat-smt-solver/)

### Other ATP Systems
- [Vampire](https://vprover.github.io/)
- [Automated Theorem Proving - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/automated-theorem-proving)

### Usability & Learning
- [Teaching with Computer-Based Proof Assistants - CMS Notes](https://notes.math.ca/en/article/teaching-with-computer-based-proof-assistants-perspectives-from-instructors-of-mathematics/)
- [A Usability Evaluation of Interactive Theorem Provers Using Focus Groups - Springer](https://link.springer.com/chapter/10.1007/978-3-319-15201-1_1)
- [An Observation Study of Proof Assistant Users - ACM](https://dl.acm.org/doi/pdf/10.1145/3720426)
- [Research report - Proof assistants for teaching](https://hal.science/hal-04705580v1/document)
- [A case for proof assistants, and a comparison - Aaron Tomb](https://atomb.wordpress.com/2007/04/18/a-case-for-proof-assistants-and-a-comparison/)

### Industrial Applications
- [AUTOMATED THEOREM PROVING IN HIGH-QUALITY SOFTWARE DESIGN - NASA](https://ntrs.nasa.gov/api/citations/20010084145/downloads/20010084145.pdf)
- [An Industrial Strength Theorem Prover - UT Austin](https://www.cs.utexas.edu/~moore/publications/km97.pdf)
- [Using Automated Theorem Provers to Certify Auto-Generated Aerospace Software - NASA](https://ntrs.nasa.gov/api/citations/20040068177/downloads/20040068177.pdf)

### CompCert & seL4
- [seL4 Proofs](https://sel4.systems/Verification/proofs.html)
- [Comprehensive Formal Verification of an OS Microkernel - seL4](https://sel4.systems/Research/pdfs/comprehensive-formal-verification-os-microkernel.pdf)
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv](https://arxiv.org/abs/2602.08384)
- [Towards Real-World Industrial-Scale Verification: LLM-Driven Theorem Proving on seL4 - arXiv HTML](https://arxiv.org/html/2602.08384)

### Recent Research (2025-2026)
- [ITP 2026](https://itp-conference-2026.github.io/)
- [ITP: Interactive Theorem Proving](http://www.wikicfp.com/cfp/program?id=1792)
- [MiniF2F-Dafny: LLM-Guided Mathematical Theorem Proving - POPL 2026](https://popl26.sigplan.org/details/dafny-2026-papers/16/MiniF2F-Dafny-LLM-Guided-Mathematical-Theorem-Proving-via-Auto-Active-Verification)
- [Automated Theorem Proving for Prolog Verification - arXiv](https://arxiv.org/abs/2601.03849)
- [Interactive Theorem Provers for Proof Education - ACM](https://dl.acm.org/doi/10.1145/3758317.3759679)
- [LLM-Based Theorem Provers - Emergent Mind](https://www.emergentmind.com/topics/llm-based-theorem-provers)
- [A Survey on Deep Learning for Theorem Proving - arXiv](https://arxiv.org/html/2404.09939v1)
- [Matryoshka: Fast Interactive Verification](https://matryoshka-project.github.io/)
- [CLEVER: A Curated Benchmark for Formally Verified Code Generation - arXiv](https://arxiv.org/pdf/2505.13938)

### Technical Resources
- [Comprehensive Exam Report - Foundations of Theorem Provers - University of Iowa](http://homepage.divms.uiowa.edu/~viswanathn/comprep1.pdf)
- [Deductive Software Verification - University of Twente](https://ris.utwente.nl/ws/files/147323572/H_hnle2019deductive.pdf)
- [Position paper: the science of deep specification - PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC5597730/)

---

**調査完了日**: 2026-02-14
**調査者**: researcher-07
**タスクID**: #51
