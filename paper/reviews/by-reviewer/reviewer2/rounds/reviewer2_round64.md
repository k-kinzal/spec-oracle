---

## Reviewer 2 — Formal Review

**Paper:** UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization
**Target Venues:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

### 1) Recommendation

**Major Revision**

---

### 2) MUST (採択に必須)

**M1. `UStar` の定義がない（最重大）**

本文全体で `UStar`（`U*`）は「到達不可能な理想的ルート仕様」として概念的に言及されているが（§1.1, §3.8）、その**形式的定義が原稿のどこにも与えられていない**。定理 `UStar_inter_projDomOn_subset_UAndOn` は `UStar` を主語にしているにもかかわらず、それが何であるかを本文で定義していない。読者（および査読者）は補題の前提の意味を推察せざるを得ない。定理が何を主張しているか自体が不明確である。Lean ファイル名 `IdealRoot.lean` も参照されているが、本文中に形式的定義の抜粋がない。`UStar` の定義（あるいは `UStar` が公理的に与えられる抽象パラメータであるという明示的な宣言）を§2または§3.8に追加しなければ、定理の主張が評価不可能であり採択できない。

**M2. 「adequacy」の意味の実質的空洞化（重大な論理的問題）**

§3.6の adequacy 定理 `preimage_eq_semanticPullback` は `E` が任意の抽象的二項関係である前提で証明されている。§3.6.1で述べている通り、具体的 extractor に対する `hSound`・`hComplete` の証明義務は「外部」に委ねられており、本論文の claim 外である。しかし、**抽象的 `E` に対する等価定理は、それだけでは実質的な内容を持たない**。なぜなら `E` に何の制約も設けなければ、任意の関係について形式的に閉じた等価が得られるからである。この定理の mechanization-specific value（§6）として主張されている「soundness/completeness の分離可能性」は正しいが、それ自体は古典的な話である。本論文が `E` に何の意味的制約も設けずに adequacy を論じるならば、"adequacy of what?" という問いに答える必要がある。少なくとも `E` が満たすべき最小公理（たとえば well-foundedness や関数性など）を明示し、それなしでは定理の有意味性が損なわれることを議論すべきである。さもなければ adequacy 定理の novelty claim を大幅に弱める書き直しが必要である。

**M3. 主要な Lean コードが投稿物に含まれていない**

§4.4に `lake build` の手順が記載されているが、`paper/lean/` ディレクトリの内容は本原稿には含まれていない（原稿は3ファイルのみ）。Lean ファイルの実際の内容が審査対象ではないとしても、**CPP・ITP・FMでは mechanized proof の再現可能性が採択の前提条件**である。提出パッケージに Lean ソースが含まれているか否かが原稿からは判断不能である。少なくとも「Lean ソースはどのような形で入手可能か」を §9 に明示せよ。Supplement としての提出、アーカイブ、またはロック済みハッシュ付きリポジトリのいずれであるかを具体的に記せ。

---

### 3) SHOULD

**S1. §6「Mechanization Added Value」の正当化が不十分**

§6で列挙された5点（assumption surfacing, partiality discipline, one-sided adequacy granularity, adjunction caution, observability-domain linkage）はいずれも正しい観察である。しかし、これらの価値は「Lean で機械化したことの価値」ではなく「部分写像を明示的に扱う定式化の価値」である可能性がある。たとえば同じ内容をCoqやIsabelle、あるいは詳細な紙上証明で行った場合と比較して、**Lean4 という選択・機械検査という手法自体が何を付加したか**を議論すべきである。現在の記述では "mechanization value" と "modeling value" の区別が曖昧である。

**S2. `consistent_transport_left`（Transfer.lean）が本文に出てこない**

Theorem Catalog（付録）によると `Transfer.lean` には `lifted_transfer` と `consistent_transport_left` の2定理がある。しかし §3.4 は `lifted_transfer` のみを詳述し、`consistent_transport_left` は本文で一切言及されていない。これが supporting lemma なのか、独立した claim なのかを §3.4 の末尾に1文追記せよ。

**S3. `preimage_compose` における Classical.choice の依存**

§4.3の axiom audit で `preimage_compose` は `[propext, Classical.choice, Quot.sound]` に依存している。`Classical.choice` への依存は証明の構成性を損なう。構成的に証明できないのか、できないとすればなぜかを本文で説明し、その依存が定理の主張の解釈に影響するかどうかを議論せよ（特に CPP の査読者はこの点を重視する）。

**S4. Prior Work §7.5 が一方的すぎる**

§7.5でGalois connection の機械化の先行研究（Darais and Van Horn, ICFP 2016）が触れられているが、記述が「我々はその延長にある」という1文で終わっている。Darais-Van Horn の構成的Galois接続と本論文の `no_left_adjoint_of_partial` の**結果の類似点・相違点の技術的比較**が必要である。「境界定理として位置づける」だけでは差別化が不十分である。

---

### 4) MINOR

**m1. RQ1・RQ2 の扱いの非対称性**

§1.3 では RQ1〜RQ5 が定義され、§3.2末尾で "Primary RQs for this formal paper are RQ3, RQ4, and RQ5" と宣言されている。しかし §3.2 の後半で RQ1 と RQ2 の回答を述べている。Primary でない RQ の回答を Primary の節（§3.2）の中に埋め込む構造は混乱を招く。RQ1・RQ2 は §2（モデル定義）への参照で完結させるか、独立した小節を設けよ。

**m2. `UAndOn_empty_eq_univ` の記述が不完全**

§3.3 に "vacuous-truth edge cases are explicit" とあり `UAndOn_empty_eq_univ` が言及されているが、定理の主張内容（空の active set のとき `UAndOn = univ`）が**数式で示されていない**。Theorem Catalog との整合性は取れているが、本文読者が定理の内容を理解するのに参照先を辿る必要がある。定理の主張式を §3.3 に1行追記せよ。

**m3. 参考文献が不完全**

References で [8] Xiong et al.（BX/synchronization 文脈）と [9] Mossakowski et al.（Hets）は "CEUR-WS" および "SoSyM, 2012" とあるが、タイトルや著者の正式な書誌情報として不完全である（例: ページ番号, DOI, 巻号の欠落）。形式手法系会議の submission standard に合わせよ。

**m4. 用語の微小な不一致**

- Abstract では "UAD/f Two-Operator Kernel" とあるが、§2以降で "UAD/f" ではなく "UadfU0" という Lean namespace 名が使われており、`Model ι α` が中心的構造として扱われている。読者は UAD/f が具体的に何を意味するか（U=Universe, A=Admissible, D=Domain, f=function?）を本文から推察しなければならない。§2.2 か §1 で略語を展開せよ。

---

### 5) Acceptance Readiness (3行)

本論文は partial projection 下の多層仕様比較のための typed kernel を Lean4 で機械化した solid な mechanized-foundations 論文の基礎を持つが、現状では **`UStar` の形式的定義の欠如という致命的な不備**、および adequacy 定理の実質的空洞化リスクという根本的な論理問題を抱えており、Major Revision なしには採択できない。これらの問題は分量的には小規模な改定で解消できる性質のものであり、**修正の方向性は明確**である。Lean ソースの可用性を担保した上で上記 M1〜M3 を解消すれば、ITP/CPP レベルでの採択圏に入ると判断する。
