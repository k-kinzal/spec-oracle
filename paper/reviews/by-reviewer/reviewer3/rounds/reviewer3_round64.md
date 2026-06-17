---

## Reviewer 3 Report

**Submission:** UAD/f Two-Operator Kernel under Partial Projections: Assumption-Audited Lean4 Mechanization
**Venue target:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

## 1) Recommendation

**Major Revision**

---

## 2) MUST (採択に必須)

### M1: Lean ソースファイルの不在・検証不能

本稿は再現性を正面から主張する（Section 4.4, Section 9）が、投稿物の中に `paper/lean/UadfU0/` 以下の実際のソースコードが含まれていない。theorem catalog（付録）は theorem 名と行数を列挙するが、これは証明の内容を検証する手段を提供しない。

- `lake build` が成功する、sorry が 0 である、という記述はすべて著者の自己申告にとどまる。
- `#print axioms` の出力（Section 4.3）も同様に自己申告である。
- ITP/CPP 等では Lean ソースの artifact 同梱または公開リポジトリへの恒久リンクが事実上の採択条件となっている。

**必要な対応:** Lean ソース全体をサプリメンタル artifact として同梱するか、査読期間中に匿名でアクセス可能な形で提供すること。これがない限り機械検証の主張は査読不能。

---

### M2: `UStar` の定義が本文に存在しない

Section 3.8 および付録（assumption matrix, theorem catalog）において `UStar` が繰り返し使用される。しかし本文のどこにも `UStar` の定義・意味論的解釈が明示されていない。

- Section 3.8 には `projDom(i)` と `projDomOn(active)` の定義はあるが `UStar` 自体は「ideal complete root specification `U*`」（Section 1.1）への暗黙の参照として扱われているにとどまる。
- 定理 `UStar_subset_UAndOn`（theorem catalog）は assumption matrix では言及されず、本文 Section 3.8 にも proof sketch がない。
- `UStar` を仮定として受け取るのか、構築するのか、公理として設けるのかが不明。

**必要な対応:** `UStar` の型・定義・意味論的根拠を明示的に定義すること。仮定として受け取るなら assumption matrix に追加すること。

---

### M3: 関連研究の引用が不十分（特に ITP/CPP 文脈）

Section 7 は abstract interpretation、institutions、BX、Galois connections への参照を持つが、いずれも概括的な言及にとどまり、**本稿の定理が先行研究の既存定理と具体的にどう異なるかの比較が欠けている。**

特に深刻な欠落：
- Lean/Mathlib における `Set.image`/`Set.preimage` の既存定理群との比較が皆無。`preimage_monotone` 等は Mathlib に等価物が存在する可能性が高く、なぜ独自定義が必要かを正当化していない。
- CPP・ITP の近年（2020-2025）の機械検証関連研究（heterogeneous typed semantics の Lean 実装等）への参照が全く存在しない。
- 「mechanization-specific value」（Section 6）の主張は先行研究との差分が明確でなければ支持できない。

**必要な対応:** Mathlib の既存定理との関係を節として追加するか、新規性の境界を定理ごとに明示すること。

---

## 3) SHOULD

### S1: `hproj` の意味論的妥当性の正当化が不足

`lifted_transfer` の核心仮定 `hproj`（same-root linkage）は Section 3.4 の assumption audit で言及されるが、**この仮定が実際の多層仕様環境でどの程度 satisfiable か**についての議論がない。

- `hproj` は実質的に「同一ルート点 `x` において異なる層の射影が同時に定義される」という強い仮定であり、partial projection 環境では自明でない。
- この仮定が満たされない典型的な状況（例：観測粒度が異なる層）に対して、定理の適用範囲がどう制限されるかを議論すべき。

### S2: `SpecSet α := α -> Prop` と Mathlib `Set α` の関係の明示

Section 2.1 に「local alias, not a direct use of Mathlib `Set α`」とある。この選択の技術的理由（universe polymorphism, definitional equality, etc.）が説明されていない。レビュアーが独自定義の必要性を判断できない。

### S3: Password-policy case study の formal significance の説明不足

Section 5.2 は `checkConsistent_iff_allThree` を「mechanized sanity theorem」として提示するが、これがなぜ formal paper の section として必要かが不明確。この事例は model instantiation の検証として Section 5.1 で十分なのか、あるいは固有の技術的主張があるのかを明示すること。

### S4: Non-adjointness 定理（Section 3.7）のポジショニング

本定理は「guardrail」として位置付けられるが、Section 6 の novelty claim の中では「adjunction caution」として列挙されているに過ぎない。Constructive Galois Connections（Darais & Van Horn 2016）との定式上の関係を明示し、本定理がそこで扱われない partial projection 固有の側面を担うことを証明すること。

---

## 4) MINOR

### m1: 定義 `Ui` の不整合

Lean signature（Section 3.4）中に `M.Ui j` が登場するが、本文の定義体系には `Ui` という識別子は定義されていない（`lifted`, `A` が対応関係にある）。コード断片と本文の対応を整合させること。

### m2: Section 3.3 の "same-root linkage" の前方参照

`UAndOn_subset_U0On` の前提（non-empty active set）は assumption matrix に記載があるが、本文 Section 3.3 では `(requires non-empty active set)` と括弧書きにとどまる。assumption matrix との対応を明示的に cross-reference すること。

### m3: References の不完全性

- 文献 [9] Mossakowski et al. は "CEUR-WS" のみで巻号・年が欠落。
- 文献 [10] de Moura et al. は Lean4 ではなく Lean 1/2/3 の CADE 2015 論文であり、現在の Lean4 toolchain（v4.27.0）との関係を明示するか適切な Lean4 参照に置き換えること。

### m4: Section 0 の構造

Section 0 は "Scope, Split, and Quality Bar" として投稿戦略（two-paper strategy）を記述するが、これは通常 paper 内に記述しない meta-level 情報である。査読者・読者に向けた section 構成としてリファクタリングを推奨する。

---

## 5) Acceptance Readiness（3行）

本稿の理論的骨格は自己無撞着であり、mechanization の主要な設計判断（partiality first-class 化、assumption-explicit theorem インターフェース）は formal methods コミュニティにとって有用な形式化の試みである。しかし、Lean artifact が査読者から直接検証できない状態では機械検証の主張を採択の根拠とすることができず、`UStar` の未定義および Mathlib 既存定理との関係の欠落はカメラレディ品質に達していない。M1・M2・M3 への対応が示されれば再査読に値する。
