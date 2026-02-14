# 仕様の意味論：「仕様とは何か」の哲学的・理論的考察

## 1. はじめに：なぜ「仕様とは何か」が問題になるのか

本稿では「仕様（specification）とは何か」という根源的な問いについて、哲学的・理論的観点から掘り下げる。ソフトウェア工学の実践において、私たちは日常的に「仕様」という言葉を使用するが、その本質的な意味について深く問い直されることは少ない。しかし、仕様は自然言語で書かれることもあれば形式的に書かれることもあり、曖昧さや矛盾が存在しうる。数学的推論で全てを捉えられるのか、形式仕様は仕様の部分集合なのか――こうした問いは、仕様の本質を理解する上で避けて通れない。

## 2. 仕様（specification）の定義：複数の視点から

### 2.1 形式手法における定義

形式手法の文脈では、**仕様とは、システムが何をすべきか（what）を記述するものであり、どのように実現するか（how）を記述するものではない**。これは[Formal Methods - Wikipedia](https://en.wikipedia.org/wiki/Formal_methods)や[NASA Langley Formal Methods Program](https://shemesh.larc.nasa.gov/fm/fm-what.html)で強調されている基本原則である。

より具体的には：

- **形式仕様（formal specification）**は、形式論理に基づく数学的に厳密な記法を用いて、システムの要求、設計、前提条件を定義するものである
- 形式仕様は実装ではなく、実装を開発するために使用されるものである
- 設計や実装は、それ自体で「正しい」と宣言されることはできない。**特定の仕様に対してのみ「正しい」と言える**（"correct with respect to a given specification"）

[Formal Specification - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/formal-specification)によれば、形式仕様はシステムを記述し、その振る舞いを分析し、重要な特性を厳密な手法で検証することによって設計を支援するために使用される。

### 2.2 Leslie Lamportの見解：仕様とは何か

Leslie Lamportは、TLA+（Temporal Logic of Actions）の開発者として形式仕様の分野で重要な貢献をしている。Lamportによれば：

**「仕様とは、システムが何をすべきかについての書かれた記述であり、それが正しく機能することを確認する方法である」**（[TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)より）

Lamportは、システムを実装する前に仕様を書くことの重要性を強調する。**システムを構築する前に理解することは良い考えであり、したがって実装前に仕様を書くことは良い考えである**。

Lamportの重要な洞察は、仕様記述の実践的側面にある。彼は時相論理（temporal logic）に幻滅した経験を語っている。研究者たちが単純なFIFOキューを仕様化するのに何日も費やし、列挙した特性が十分かどうかを議論しているのを見て、Lamportは時相特性の連言として仕様を書くアプローチが**実際には機能しない**ことに気づいた。これがTLA（Temporal Logic of Actions）の開発につながった（[Specifying Systems - Leslie Lamport](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)）。

TLAでは、**仕様は状態遷移関係を記述するアクション（primed/unprimedな変数の論理式）を用いて表現される**。これは、並行・分散システムの振る舞いを記述する効果的な手段を提供する（[Temporal Logic of Actions - Wikipedia](https://en.wikipedia.org/wiki/Temporal_logic_of_actions)）。

### 2.3 Daniel Jacksonの見解：軽量形式手法と抽象化

MIT教授でAlloyモデリング言語の主設計者であるDaniel Jacksonは、仕様に対して異なる角度からアプローチする。彼の著書『Software Abstractions』で提示される「軽量形式手法（lightweight formal methods）」または「アジャイルモデリング（agile modeling）」は、形式仕様の理念を取り入れつつ、実践的な適用を重視する。

Jacksonのアプローチは：

- 形式仕様の**簡潔で表現力豊かな記法**という理念を採用する
- **最小限のシンプルで堅牢な概念のツールキット**に基づく
- 定理証明に基づく従来の分析を、**設計者に即座にフィードバックを与える完全自動化された分析**に置き換える

（[Software Abstractions - MIT Press](https://mitpress.mit.edu/9780262528900/software-abstractions/)、[Daniel Jackson - Wikipedia](https://en.wikipedia.org/wiki/Daniel_Jackson_(computer_scientist))）

Jacksonは、プログラマーが一時的な技術の複雑さに対処することに引き込まれがちだが、**もし私たちが根底にある概念に焦点を当て、小さなパフォーマンス向上やより複雑な機能ではなく、シンプルさと明確さのために努力すれば、私たちのソフトウェアはより強力で、より信頼性が高く、より使いやすくなる**と主張する。

### 2.4 Hoare LogicとDijkstraの貢献

Tony HoareとEdsger Dijkstraは、仕様の数学的基盤を確立した先駆者である。

**Hoare Logic**では、仕様は**ホーアトリプル（Hoare triple）**の形式で表現される：
```
{P} S {Q}
```
ここで：
- P：事前条件（precondition）— 実行前に真でなければならない条件
- S：プログラム文（statement）
- Q：事後条件（postcondition）— 実行後に真であるべき条件

（[Hoare Logic - Stanford](https://cs.stanford.edu/people/eroberts/courses/soco/projects/2008-09/tony-hoare/logic.html)、[Axiomatic Semantics and Hoare-style Verification - CMU](https://www.cs.cmu.edu/~aldrich/courses/17-355-18sp/notes/notes11-hoare-logic.pdf)）

**Dijkstraの弱い事前条件（weakest precondition）**は、仕様のアプローチをさらに精緻化した。目的の事後条件に対して、文の弱い事前条件を計算することで、曖昧さを排除し、有効なホーアトリプルを計算するアルゴリズムを提供する（[Predicate Transformer Semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)、[Formalizing Dijkstra - John Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/dijkstra.pdf)）。

これらの貢献により、**プログラムの正しさは数学的推論と証明によって与えられ、仕様がプログラムのテキストの論理的帰結であることを保証できる**という理論が確立された。

## 3. 仕様と要求（requirements）の違い

仕様（specification）と要求（requirements）は混同されがちだが、明確な区別がある：

### 3.1 要求（Requirements）

- **要求とは、エンジニアリングまたは取得されるべきものの必要とされる特性である**
- 高レベルの記述であり、ユーザーとビジネスのニーズを満たすために製品が何をすべきかを示す
- **自然言語で書かれた、顧客の理解のための一般的な記述**
- 「何（what）」と「なぜ（why）」に焦点を当てる
- より抽象的で一般的

（[PPI - Requirements vs Specifications](https://www.ppi-int.com/resources/systems-engineering-faq/what-is-the-difference-between-requirements-and-specifications/)、[Requirements vs. Specification - Medium](https://medium.com/@sofiia./requirements-vs-specification-bbb0b3ad3704)）

### 3.2 仕様（Specifications）

- **仕様とは、要求の集合の特定の記録、または設計の特定の記録である**
- 詳細で構造化された文書であり、システムの正確な機能、サービス、運用上の制約を定義する
- 請負業者や開発者の実装により適している
- **「どのように（how）」と「いつ（when）」に焦点を当てる**
- より具体的で詳細

（[Argon Digital - Requirements vs Specifications](https://argondigital.com/blog/product-management/requirements-vs-specifications-create-a-shared-vocabulary/)、[GeeksforGeeks - Product Requirements vs Specifications](https://www.geeksforgeeks.org/software-engineering/difference-between-product-requirements-and-product-specifications/)）

### 3.3 本質的な違い

**要求仕様（requirement specification）はwhatに対処し、設計仕様（design specification）はhowに対処する**。要求はステークホルダーがシステムに何を必要とするかを捉え、仕様はそれらの要求がどのように満たされるかの詳細な構造化された文書を提供する。

## 4. 仕様の数学的基盤

### 4.1 モデル理論（Model Theory）からの視点

数学論理学における**モデル理論（model theory）**は、形式理論（formal theory）とそのモデル（model）の関係を研究する。これは仕様を理解する上で重要な数学的基盤を提供する。

[Stanford Encyclopedia of Philosophy - Model Theory](https://plato.stanford.edu/entries/model-theory/)によれば：

- **解釈（interpretation）**は、不完全な文を真または偽の文に変換する欠けている情報を提供する
- ある解釈が文を真にするとき、その解釈はその文の**モデル（model）**となる
- **理論（theory）**は、それらすべてを同時に満たす構造のクラスを定義する文の集合である

モデル理論的帰結：前提のすべてのモデルが結論のモデルでもあるとき、結論は前提から帰結する。

数学では、理論は構造のクラスを公理化する。例えば、4つの一階述語論理の文の集合がアーベル群を公理化する――すべての有効な解釈が満たすべき特性を指定することで、数学的対象を定義する。

### 4.2 仕様を集合論・論理学から見る

仕様の数学的基盤は以下の要素に基づく：

1. **集合論（Set Theory）**：
   - Z仕様言語やVDM（Vienna Development Method）は、集合論と一階述語論理を数学的基盤とする
   - 状態機械をモデルとし、述語論理理論に基づく
   （[Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)）

2. **述語論理（Predicate Logic）**：
   - 仕様は述語と論理的制約として表現される
   - 非決定性仕様は形式手法におけるソフトウェア開発で中心的な役割を果たす
   - 数学的表現（通常述語計算に基づく）により、完全なプログラムまたはプログラム断片を記号的表現で表し、数学的法則に従って操作できる
   （[Formal Methods in Specification and Design](https://www.rose-hulman.edu/class/csse/csse373/current/Resources/Ardis1.pdf)）

3. **モデル理論の応用**：
   - モデル理論家のYuri Gurevichは、計算機科学における仕様のためにモデル理論的アイデアを使用する方法として**抽象状態機械（Abstract State Machines, ASMs）**を導入した
   - ASMsは古典的な数学的構造を用いて計算の状態を記述する――構造は十分に理解され、正確なモデルである
   （[Model Theory - Stanford Encyclopedia](https://plato.stanford.edu/entries/model-theory/)）

### 4.3 完全性（Completeness）と無矛盾性（Consistency）

仕様の性質を評価する上で、完全性と無矛盾性は重要な概念である：

**無矛盾性（Consistency）**：
- 形式システムが無矛盾であるとは、ある文とその否定の両方がシステムで導出可能でないことを意味する
- 意味論的には、理論が充足可能（satisfiable）であること――つまりモデルを持つこと――が無矛盾性に対応する
（[Consistency - Wikipedia](https://en.wikipedia.org/wiki/Consistency)、[Complete Theory - Wikipedia](https://en.wikipedia.org/wiki/Complete_theory)）

**完全性（Completeness）**：
- 理論が完全であるとは、それが無矛盾であり、かつ理論の言語のすべての閉じた論理式について、その論理式またはその否定が証明可能であることを意味する
- 形式システムが意味的に完全であるとは、すべてのトートロジーが定理であることを意味する
（[Completeness (logic) - Wikipedia](https://en.wikipedia.org/wiki/Completeness_(logic))、[Encyclopedia of Mathematics - Completeness](https://encyclopediaofmath.org/wiki/Completeness_(in_logic))）

**ゲーデルの不完全性定理との関連**：
- ゲーデルの不完全性定理は、一定量の初等算術を実行できる十分に強力な無矛盾な形式システムは不完全であることを示す――システムの言語の文で、それ自体もその否定も証明も反証もできない文が存在する
- これは**仕様と形式検証の能力に直接的な制約を課す**
- 任意の仕様の正しさを形式的に証明することが保証される普遍的なツールは開発できない（ただし、実用的なツールは明確に定義された言語における有限の現実世界の仕様の大部分を扱える）
（[Gödel's Incompleteness Theorems - Stanford Encyclopedia](https://plato.stanford.edu/entries/goedel-incompleteness/)、[Gödel's Incompleteness - Wikipedia](https://en.wikipedia.org/wiki/G%C3%B6del's_incompleteness_theorems)）

興味深いことに、**プレスバーガー算術（Presburger arithmetic）**は、自然数の加法に関する公理系であり、**無矛盾かつ完全である**（[Complete Theory - Wikipedia](https://en.wikipedia.org/wiki/Complete_theory)）。これは、限定された理論においては完全性と無矛盾性の両立が可能であることを示している。

## 5. 自然言語仕様と形式仕様の関係性

### 5.1 自然言語仕様の問題：曖昧性

自然言語は要求工学において最も頻繁に使用される表現形式であり、**普遍的で、柔軟で、広く普及しているが、残念ながら本質的に曖昧でもある**（[Ambiguity in Natural Language Requirements - D.M. Berry](https://cs.uwaterloo.ca/~dberry/ambiguity.res.html)）。

曖昧性には複数の種類がある：

1. **言語学的曖昧性（Linguistic ambiguities）**：
   - 曖昧な代名詞参照など、自然言語の一般的な曖昧性

2. **RE特有の曖昧性（RE-specific ambiguities）**：
   - アプリケーション、システム、開発ドメインを含む要求工学のコンテキストから生じる曖昧性

（[Resolving Ambiguities in Natural Language Software Requirements](https://dl.acm.org/doi/10.1145/2815021.2815032)）

### 5.2 曖昧性の影響

**顧客もソフトウェア開発者も曖昧性を認識せず、それぞれが異なる解釈を導き出してその違いに気づかないことが多く、開発者が顧客の意図とは異なる振る舞いをするシステムを設計・実装する原因となる**（[Natural Language in Requirements Engineering - D.M. Berry](https://cs.uwaterloo.ca/~dberry/natural.language.html)）。

### 5.3 形式仕様の利点と限界

**形式仕様言語の利点**：
- 自然言語と比較して、形式仕様言語の利点は**曖昧でない意味論**であり、仕様を入力として依存するアルゴリズム作業にアクセス可能である
（[Bridging the Gap between Natural Language Requirements and Formal Specifications](https://ceur-ws.org/Vol-1564/paper20.pdf)）

**形式仕様の限界**：
- しかし、**数学に基づく形式言語が要求仕様に使用される場合でも、自然言語の要求仕様から逃れることはできない**
- 自然言語の初期概念に固有の曖昧性は、形式仕様への移行時に影響を及ぼす可能性があり、**形式化する人が理解することが、考案者が意味したこととは異なる場合がある**
（[Minimizing Ambiguity in Natural Language Software Requirements](https://www.researchgate.net/publication/215613248_Minimizing_Ambiguity_in_Natural_Language_Software_Requirements_Specification)）

### 5.4 自然言語と形式仕様の関係

形式仕様は自然言語仕様を置き換えるものではなく、補完するものである。最近の研究では、大規模言語モデル（LLM）を用いて自然言語の意図を形式手法の事後条件に変換する試みも行われている（[Can LLMs Transform Natural Language Intent into Formal Method Postconditions?](https://dl.acm.org/doi/10.1145/3660791)）。

**自然言語仕様と形式仕様の間にはトレードオフがある**：
- 自然言語：表現力が高く、理解しやすいが、曖昧
- 形式仕様：曖昧性がなく、検証可能だが、習得と理解に専門知識が必要

（[Trade-off between Natural Language and Formal Specifications - ResearchGate](https://www.researchgate.net/figure/Trade-off-between-natural-language-and-formal-specifications-4-inset-showing-the_fig1_260799988)）

## 6. 「仕様は許容される振る舞いの集合である」という見方

### 6.1 振る舞いとしての仕様

仕様を「許容される振る舞いの集合」として見る視点は、形式手法の理論的基盤に深く根ざしている。

**基本的な考え方**：
- 基本的なシステム仕様の形式主義は、システムの動的振る舞いの局所的記述を可能にする――つまり、任意の特定の時点で状態がどのように変化するかを仕様化する
- この局所的記述から、対応する動的システムの全体的な動的振る舞いを導出することが可能である
（[Model of Computation - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/model-of-computation)）

**ブラックボックスモデリング**：
- 根底にある考え方は、**システムの入出力マッピングのみが関連性があり、内部構成には関係ない**というものである
- このアプローチ（「ブラックボックスモデリング」とも呼ばれる）は、入出力信号セットの観測と、観測された入出力関係を模倣するように調整されるモデルトポロジーの仕様のみを必要とする
（[Behavioral Modeling - ScienceDirect](https://www.sciencedirect.com/topics/engineering/behavioral-modeling)）

### 6.2 形式手法における振る舞いの集合

形式手法は、**振る舞い（形式意味論、例えば数学論理学における文）がシステム（形式意味論を持つ言語で仕様化された）において常に成立することをチェックすることを可能にする**。

より具体的には、形式手法は**M が φ を満たすこと**を示す：
- M：システムが何をするかの形式的定義
- φ：システムが何をすべきかの形式的定義

（[Formal Methods in Industry - Formal Aspects of Computing](https://dl.acm.org/doi/full/10.1145/3689374)）

### 6.3 仕様言語と振る舞い

**仕様言語は、システムの特性と振る舞いを記述するために使用される形式言語**であり、特にソフトウェアおよびハードウェア工学において、システム要求を仕様化するための正確な構文と意味論を提供する（[Specification Language - Academia.edu](https://www.academia.edu/Documents/in/Specification_Language)）。

最近の形式手法の研究（2024-2025年）では、プログラム仕様の合成において、JMLやACSLなどの形式言語で表現された仕様が使用され、これらは**すべての可能なプログラム実行について徹底的に推論し、論理的に正確な表現を生成する**ことをLLMに要求している（[Towards Formal Verification of LLM-Generated Code](https://arxiv.org/pdf/2507.13290)）。

### 6.4 モデル理論的視点

モデル理論の観点から：
- **文（sentence）はそのすべてのモデルのクラスを定義する**：Mod(S)
- 理論は、それらすべてを同時に満たす構造のクラスを定義する文の集合である

これは、仕様が許容される構造（振る舞い）の集合を定義するという見方を数学的に裏付ける。

## 7. オントロジーと仕様の本質

### 7.1 オントロジー（存在論）とは

哲学における**オントロジー（ontology）**は、存在の研究であり、**存在の本質、すべての実体が共有する特徴、それらが存在の基本カテゴリーにどのように分割されるかを探求する哲学の一分野**である（[Ontology - Britannica](https://www.britannica.com/topic/ontology-metaphysics)、[Ontology - Wikipedia](https://en.wikipedia.org/wiki/Ontology)）。

### 7.2 計算機科学におけるオントロジー

計算機科学の文脈では、Tom Gruberが重要な定義を提供している：

**「オントロジーとは概念化の仕様である」**（"An ontology is a specification of a conceptualization"）

より技術的には、オントロジーは「**概念化の明示的な仕様**」（explicit specifications of conceptualizations）として機能する（[Tom Gruber - Definition of Ontology](https://tomgruber.org/writing/definition-of-ontology/)、[What Is an Ontology? - IAOA](https://iaoa.org/isc2012/docs/Guarino2009_What_is_an_Ontology.pdf)）。

ここで：
- **概念化（conceptualization）**は、他の概念との関係とそれを支配する原則の両方を考慮することで、特定の概念の構造を理解する方法である
- **オントロジー**は、エージェントまたはエージェントのコミュニティに対して形式的に存在しうる概念と関係の記述である（プログラムの形式仕様のような記述）

### 7.3 本質（Essence）とは

哲学的オントロジーにおいて、**本質（essence）**は何かの根本的な性質を指す：

- ある文脈では、**存在（being）**は何かが存在するという事実を表現し、**本質（essence）**はその性質または何であるかを表現する
- 本質主義は伝統的に、本質と説明の間の結びつきを強調してきた――広い考え方として、**与えられた実体の本質は、その実体の特定の他の特性や振る舞いを説明するもの**である

（[Essence and Modality - Kit Fine](https://as.nyu.edu/content/dam/nyu-as/philosophy/documents/faculty-documents/fine/accessible_fine/Fine_Essence-Modality.pdf)、[The Epistemology of Essence](https://philarchive.org/archive/MALTEO-30)）

### 7.4 仕様の本質への適用

これらの哲学的概念を仕様に適用すると：

1. **仕様は概念化の形式的記述である**――システムが何であるべきか、どのような概念で構成されるか、それらの関係は何かを定義する

2. **仕様の本質は、許容される実装の特性を説明する**――なぜ特定の実装が仕様に適合するのか、なぜ他の実装が適合しないのかを説明する

3. **哲学的オントロジーと計算機オントロジーの関係**：
   - 哲学的オントロジーは根本的な現実を探求する
   - 計算機オントロジーは、知識ドメインの形式的で機械処理可能な仕様を作成するためにこれらの原則を適用する

## 8. 仕様の限界：ゲーデルの不完全性定理との関連

### 8.1 不完全性定理の核心

ゲーデルの不完全性定理は、形式システムと仕様の根本的な限界を明らかにする：

**第一不完全性定理**：
十分な量の初等算術を実行できる無矛盾な形式システムは不完全である――**システムの言語の文で、それ自体もその否定も証明も反証もできない文が存在する**。

（[Gödel's Incompleteness Theorems - Stanford Encyclopedia](https://plato.stanford.edu/entries/goedel-incompleteness/)、[Gödel's Incompleteness - Wikipedia](https://en.wikipedia.org/wiki/G%C3%B6del's_incompleteness_theorems)）

### 8.2 形式検証への影響

形式検証に対する具体的な影響：

1. **普遍的検証ツールの不可能性**：
   - **任意の仕様の正しさを形式的に証明することが保証される普遍的なツールは開発できない**
   - ただし、実用的なツールは、明確に定義された言語における有限の現実世界の仕様の大部分を扱うことができる

2. **帰納的定理証明器の限界**：
   - ゲーデルの不完全性定理は、**任意の自動帰納的定理証明器の能力に限界を課す**
   - 帰納規則構成メカニズムがどれほど洗練されていても、それが構成できない帰納規則を証明が必要とする真の論理式が常に存在する

3. **理論計算機科学への影響**：
   - 不完全性定理は理論計算機科学に影響を与え、特に**自動定理証明、プログラム検証、人工知能の限界**を理解する上で重要である
   - いくつかの問題は、コンピュータがどれほど強力になっても、アルゴリズム的に解決できないことが確立された

（[Incompleteness Theorem - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/incompleteness-theorem)、[Gödel's Incompleteness - Kronecker Wallis](https://www.kroneckerwallis.com/kurt-godels-incompleteness-theorems-limits-of-mathematical-truth/)）

### 8.3 実践的な影響

重要な点として、**不完全性は日常的な数学者の実践にはほとんど影響を与えない**。ゲーデルが構成した証明不可能な真理は人工的であり、証明不可能であるように特別に設計されている。同様に、**形式検証ツールはこれらの理論的限界にもかかわらず、高度に実用的である**。

（[Gödel's Incompleteness Theorems - LMU](https://cs.lmu.edu/~ray/notes/godeltheorems/)）

### 8.4 哲学的含意

不完全性定理は、仕様の本質について深い哲学的問いを提起する：

- **完全な仕様は可能か？** 原理的には、十分に表現力豊かな仕様言語においては、完全かつ無矛盾な仕様は不可能である

- **仕様は真実を捉えられるか？** 真であるがその仕様システム内で証明できない文が存在する可能性がある

- **数学的推論の限界は何か？** すべての真理を形式的に捉えることができないことは、仕様には常に形式システムを超えた何かが存在することを意味する

## 9. 仕様の多層的理解：統合的視点

これまでの議論を統合すると、仕様は以下の多層的な理解が可能である：

### 9.1 実践的レベル

- **仕様は要求を実装可能な形式に翻訳したもの**
- whatを記述し、howを記述しない
- 正しさの基準を提供する

### 9.2 形式的レベル

- **仕様は数学的構造で表現される述語・制約・アクションの集合**
- モデル理論的には、許容されるモデル（構造）のクラスを定義する
- ホーア論理的には、事前条件と事後条件のペア

### 9.3 意味論的レベル

- **仕様は許容される振る舞いの集合を定義する**
- システムの入出力関係を特徴づける
- 状態空間における許容される遷移を制約する

### 9.4 認識論的レベル

- **仕様は理解を促進するための概念化の記述**
- システムを構築する前に理解するためのツール
- 設計者に即座にフィードバックを提供する手段（Jacksonの軽量形式手法）

### 9.5 存在論的レベル

- **仕様は概念化の明示的な仕様である**（Gruber）
- システムの本質的特性を捉えようとする試み
- ただし、不完全性定理により、完全な捉え方には原理的限界が存在する

## 10. 結論：「仕様とは何か」への暫定的回答

「仕様とは何か」という問いに対する単一の絶対的な答えは存在しない。むしろ、仕様は以下のように理解できる：

1. **仕様は多面的な人工物である**：
   - 実践的ツール（設計と検証のため）
   - 数学的対象（形式理論とそのモデル）
   - コミュニケーション手段（ステークホルダー間の共通理解）
   - 認識論的装置（理解を促進する）

2. **仕様は境界を定義する**：
   - 許容される振る舞いと許容されない振る舞いの境界
   - 正しい実装と誤った実装の境界
   - ただし、その境界は完全に形式的に捉えられるとは限らない

3. **仕様は相対的である**：
   - 実装は仕様に対してのみ正しいと言える
   - 仕様自体は要求に対して正しい
   - これは無限後退ではなく、異なる抽象化レベルの階層である

4. **仕様には固有の限界がある**：
   - 自然言語仕様は曖昧さを持つ
   - 形式仕様は不完全性定理の制約を受ける
   - しかし、これらの限界は実践的有用性を妨げない

5. **仕様は進化する概念である**：
   - Hoare/Dijkstraの古典的アプローチ
   - Lamportの時相論理とTLA+
   - Jacksonの軽量形式手法
   - 最近のLLMを用いた自然言語と形式仕様の橋渡し

最終的に、**「仕様とは何か」を問うことそのものが重要である**。この問いは、私たちがソフトウェアシステムをより深く理解し、より良い設計を行い、より信頼性の高いシステムを構築するための継続的な探求を促す。仕様の本質を完全に捉えることはできないかもしれないが、その探求の過程で、私たちはソフトウェア工学の実践を改善し続けることができる。

## 参考文献

### 形式手法と仕様の定義
- [Formal Methods - Wikipedia](https://en.wikipedia.org/wiki/Formal_methods)
- [Formal Specification - Wikipedia](https://en.wikipedia.org/wiki/Formal_specification)
- [NASA Langley Formal Methods Program](https://shemesh.larc.nasa.gov/fm/fm-what.html)
- [Formal Specification - ScienceDirect Topics](https://www.sciencedirect.com/topics/computer-science/formal-specification)
- [Formal Methods for Software Specification and Analysis - MIT](https://web.mit.edu/16.35/www/lecturenotes/FormalMethods.pdf)

### Leslie Lamportの業績
- [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA+)
- [Temporal Logic of Actions - Wikipedia](https://en.wikipedia.org/wiki/Temporal_logic_of_actions)
- [Specifying Systems - Leslie Lamport](https://lamport.azurewebsites.net/tla/book-02-08-08.pdf)
- [Should Your Specification Language Be Typed? - Leslie Lamport](https://lamport.azurewebsites.net/pubs/lamport-types.pdf)

### Daniel Jacksonと軽量形式手法
- [Software Abstractions - MIT Press](https://mitpress.mit.edu/9780262528900/software-abstractions/)
- [Daniel Jackson (computer scientist) - Wikipedia](https://en.wikipedia.org/wiki/Daniel_Jackson_(computer_scientist))

### Hoare LogicとDijkstra
- [Hoare Logic - Stanford](https://cs.stanford.edu/people/eroberts/courses/soco/projects/2008-09/tony-hoare/logic.html)
- [Axiomatic Semantics and Hoare-style Verification - CMU](https://www.cs.cmu.edu/~aldrich/courses/17-355-18sp/notes/notes11-hoare-logic.pdf)
- [Predicate Transformer Semantics - Wikipedia](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
- [Formalizing Dijkstra - John Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/dijkstra.pdf)

### 要求と仕様の違い
- [PPI - Requirements vs Specifications](https://www.ppi-int.com/resources/systems-engineering-faq/what-is-the-difference-between-requirements-and-specifications/)
- [Argon Digital - Requirements vs Specifications](https://argondigital.com/blog/product-management/requirements-vs-specifications-create-a-shared-vocabulary/)
- [GeeksforGeeks - Product Requirements vs Specifications](https://www.geeksforgeeks.org/software-engineering/difference-between-product-requirements-and-product-specifications/)
- [Requirements vs. Specification - Medium](https://medium.com/@sofiia./requirements-vs-specification-bbb0b3ad3704)

### モデル理論と数学的基盤
- [Model Theory - Stanford Encyclopedia of Philosophy](https://plato.stanford.edu/entries/model-theory/)
- [Model Theory - Wikipedia](https://en.wikipedia.org/wiki/Model_theory)
- [Fundamentals of Model Theory - University of Toronto](https://www.math.toronto.edu/weiss/model_theory.pdf)

### 完全性、無矛盾性、不完全性定理
- [Completeness (logic) - Wikipedia](https://en.wikipedia.org/wiki/Completeness_(logic))
- [Complete Theory - Wikipedia](https://en.wikipedia.org/wiki/Complete_theory)
- [Consistency - Wikipedia](https://en.wikipedia.org/wiki/Consistency)
- [Gödel's Incompleteness Theorems - Stanford Encyclopedia](https://plato.stanford.edu/entries/goedel-incompleteness/)
- [Gödel's Incompleteness Theorems - Wikipedia](https://en.wikipedia.org/wiki/G%C3%B6del's_incompleteness_theorems)
- [Incompleteness Theorem - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/incompleteness-theorem)

### 自然言語と形式仕様
- [Ambiguity in Natural Language Requirements - D.M. Berry](https://cs.uwaterloo.ca/~dberry/ambiguity.res.html)
- [Natural Language in Requirements Engineering - D.M. Berry](https://cs.uwaterloo.ca/~dberry/natural.language.html)
- [Bridging the Gap between Natural Language Requirements and Formal Specifications](https://ceur-ws.org/Vol-1564/paper20.pdf)
- [Resolving Ambiguities in Natural Language Software Requirements - ACM](https://dl.acm.org/doi/10.1145/2815021.2815032)
- [Can LLMs Transform Natural Language Intent into Formal Method Postconditions? - ACM](https://dl.acm.org/doi/10.1145/3660791)

### 振る舞いとしての仕様
- [Formal Methods in Industry - Formal Aspects of Computing](https://dl.acm.org/doi/full/10.1145/3689374)
- [Behavioral Modeling - ScienceDirect](https://www.sciencedirect.com/topics/engineering/behavioral-modeling)
- [Model of Computation - ScienceDirect](https://www.sciencedirect.com/topics/computer-science/model-of-computation)

### オントロジーと本質
- [Ontology - Wikipedia](https://en.wikipedia.org/wiki/Ontology)
- [Ontology - Britannica](https://www.britannica.com/topic/ontology-metaphysics)
- [Ontology and Information Systems - Stanford Encyclopedia](https://plato.stanford.edu/entries/ontology-is/)
- [Definition of Ontology - Tom Gruber](https://tomgruber.org/writing/definition-of-ontology/)
- [What Is an Ontology? - IAOA](https://iaoa.org/isc2012/docs/Guarino2009_What_is_an_Ontology.pdf)
- [Essence and Modality - Kit Fine](https://as.nyu.edu/content/dam/nyu-as/philosophy/documents/faculty-documents/fine/accessible_fine/Fine_Essence-Modality.pdf)

### 形式仕様言語と述語論理
- [Formal Specification and Documentation using Z](https://people.eecs.ku.edu/~saiedian/812/Lectures/Z/Z-Books/Bowen-formal-specs-Z.pdf)
- [Formal Methods in Specification and Design](https://www.rose-hulman.edu/class/csse/csse373/current/Resources/Ardis1.pdf)
- [From Software Specifications to Constraint Programming - Springer](https://link.springer.com/chapter/10.1007/978-3-319-92970-5_2)

### 最近の形式手法研究（2024-2025）
- [Formal Methods in Industry - ACM](https://dl.acm.org/doi/full/10.1145/3689374)
- [Towards Formal Verification of LLM-Generated Code](https://arxiv.org/pdf/2507.13290)
- [A Semantics of Structures for Formal Specification - ACM](https://dl.acm.org/doi/10.1145/3644033.3644380)

---

**本調査について**：本文書は、WebSearchおよびWebFetchツールを使用して2026年2月14日に実施した学術的調査に基づいています。仕様の哲学的・理論的側面について、複数の観点から包括的に検討しました。
