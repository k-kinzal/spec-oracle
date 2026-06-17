---

## 査読報告 — Reviewer 1

**対象投稿先:** FM / ITP / CPP / TACAS / FASE / Formal Aspects

---

### 1) Recommendation

**Major Revision**

---

### 2) MUST（採択に必須）

**M1. Lean ソースコードの不在または非アクセス性**

本論文の中核的主張はすべて「Lean4 machine-checked proofs」に依拠するが、`paper/lean/UadfU0/` 以下のソースファイルが投稿物内に含まれていない（または本文書から参照されているが閲読者に提供されていない）。論文本文に記載された Lean コードは抜粋（excerpt）に限定されており、以下が確認不能：

- `sorry` ゼロという主張の独立検証
- 59 個の theorem 宣言の内容と証明
- `lake-manifest.json` のハッシュ値の対応
- `#print axioms` 出力の再現

**要求:** 投稿パッケージに完全な Lean ソースツリー（`paper/lean/UadfU0/` 全体）を含めること、またはアーティファクト評価プロセスへの参加を宣言すること。FM/ITP/CPP では機械化証明の独立再現性が採択の前提条件である。この不在は論文の核心的主張を検証不能にする。

---

**M2. `UStar` の定義が本文に存在しない**

Section 3.8 および Theorem Catalog に `UStar` が登場し（`UStar_subset_UAndOn`, `UStar_inter_projDomOn_subset_UAndOn` 等）、これが「ideal complete root specification U*」に対応すると読める（Section 1.1）。しかし `UStar` の正式な定義は本文中のいかなるセクションにも与えられていない。

- `U*` は「usually unavailable in practice」と言及されるのみで、形式的定義なし
- Section 3.8 の定理群はこれを前提とするが定義を参照する箇所がない
- 付録の Assumption Matrix も `UStar` の定義を与えない

これは単なる説明不足ではなく、定理の前提を閲読者が検証できないという形式的欠陥である。

**要求:** `UStar` の完全な型シグネチャと定義を Section 2 内に明示すること（例：`UStar : SpecSet α` として、その構成が `A(i)` や `proj_i` との関係で定義されるか、あるいは外部から公理的に与えられるかを明確にすること）。

---

**M3. `M.Ui` の未定義使用**

Section 3.4 の Lean 署名抜粋に `yi ∈ M.Ui i` および `yj ∈ M.Ui j` が登場するが、`M.Ui` は Section 2 のモデル定義（Section 2.2–2.3）に存在しない。`M.A i` との関係が不明。

- `Layer β` の定義には `A : SpecSet β` があるが、`Model` に `Ui` フィールドは記載なし
- 抜粋コードと Section 2 の定義との間の齟齬は、証明の機械化状態に疑義を生じさせる

**要求:** `M.Ui` を正式定義するか、`M.layer i |>.A` または等価な accessor であることを明示し、Section 2 のモデル定義と整合させること。

---

### 3) SHOULD

**S1. 新規性の位置づけが不十分**

Section 6 は「Mechanization added beyond textbook identities」を主張するが、関連研究（Section 7）との差分が曖昧である。具体的に：

- Darais & Van Horn (2016) の Constructive Galois Connections との差分：partial map 下での non-adjointness は既知か否か？本論文の `no_left_adjoint_of_partial` はその上で何を追加するか？
- Institution framework（Goguen & Burstall）との差分：heterogeneous carrier の扱いは institutional semantics で既に対応されているが、何が「narrower and complementary」なのかの論証が希薄
- Refinement Calculus（Back & von Wright）との差分：adequacy decomposition の sound/complete split との関係

**要求:** Section 7 を各サブセクションで「既知の結果」「本論文の貢献」を明示的に区別する構造に改訂すること。「Our delta is X」という一文での処理では FM 系の査読水準を満たさない。

---

**S2. 定理の非自明性の論証が不均一**

Section 6 の "Per-theorem hardness summary" は `lifted_transfer` と `preimage_compose` については説得力があるが、adequacy 定理（Section 3.6）については「hold only when one-sided obligations are paired」という説明に留まる。これは adequacy の sound/complete split が既存の abstract interpretation 文献（Cousot & Cousot）と比較して何が新しいかを示していない。

**要求:** Section 3.6 の adequacy 定理について、abstract interpretation の Galois insertion 条件との比較を明示すること。`preimage_eq_semanticPullback` は Galois connection の特殊ケースか否か、partial map の存在がどう変化させるかを示すこと。

---

**S3. `SpecSet α := α -> Prop` の Mathlib との関係**

Section 2.1 に「local alias, not a direct use of Mathlib `Set α`」とあるが、その意図と実際の帰結が不明確：

- Lean4 の `Set α` は `α → Prop` の `def` エイリアスであり、実質的に同一
- local alias を用いる理由（名前空間の分離？Mathlib 非依存性？）が説明されていない
- Axiom audit に `Classical.choice` が `preimage_compose` に現れるが、core Classical 回避を意図しているなら矛盾の説明が必要

**要求:** local alias の動機と Mathlib `Set α` との実際の差異（あれば）を Section 2.1 または Section 4 で明示すること。

---

**S4. `RQ1`, `RQ2` の primary vs. secondary 扱いの不一致**

Section 1.3 で「Primary RQs for this formal paper are RQ3, RQ4, and RQ5」とするが、Section 3.2 の "Explicit RQ linkage" で `RQ1`, `RQ2` の解答を提供している。Secondary であるなら、なぜ Section 1.3 で言及したか、あるいは primary に格上げすべきかを明確化すること。構成として不整合に見える。

---

### 4) MINOR

**m1.** Section 2.5 で `U0 := U0On(λ _, True)` の右辺が `λ _, True` であるが、Lean4 では `fun _ => True` と書くのが通例。記法の一貫性が望ましい（数学表記とコード表記の混在を明示するか統一すること）。

**m2.** Section 3.4 の Lean 署名で `M.Ui` 問題（MUST M3）とは別に、`hA` の引数順序が本文の数学表記（Section 3.4 の formula）と Lean 署名で異なる可能性がある（`yi`, `yj` の出現順）。要確認。

**m3.** Section 4.3 に「`paper/lean/UadfU0` does not use `open Classical`, but some proofs still depend on core axioms through proof terms」とある。これは `Classical.choice` が `preimage_compose` の axiom audit に現れることと整合するが、どの Lean ライブラリ経由で引き込まれているかを説明することが望ましい（例：`List`, `Finset`, `decide` tactic 等の暗黙的な Classical 依存）。

**m4.** References に de Moura et al. (CADE 2015) を挙げているが、Lean4 の主要文献は Moura & Ullrich (CADE 2021) である。更新を推奨する。

**m5.** Theorem Catalog（付録）の `UStar_subset_UAndOn` と本文 Section 3.8 の主要定理リストとの対応が明示されていない（Section 3.8 は `UStar_inter_projDomOn_subset_UAndOn` を key theorem として挙げるが、catalog では両方が列挙されている）。どちらが主定理かを整理すること。

**m6.** Section 5.1 の "5 items" リストの 5 番目（heterogeneous carriers の RQ1 サンプル）は M1 の問題が解決されるまで検証不能。本文の記述は正確であるが、現状では読者が確認する手段がない旨の注記を加えることが誠実である。

---

### 5) Acceptance Readiness（3行）

本論文は形式的に誠実な構成（non-claims の明示、assumption audit、one-sided adequacy の分離）を持ち、partiality-aware な UAD/f カーネルの機械化という明確なスコープを提示している。しかし核心的主張である Lean4 証明の独立検証が現状では不可能であり、`UStar` および `M.Ui` の未定義という本文内の形式的齟齬が存在する。これら MUST 項目を解決し、関連研究との差分論証を精緻化すれば、FM/Formal Aspects 水準での採択可能性は十分にある。
