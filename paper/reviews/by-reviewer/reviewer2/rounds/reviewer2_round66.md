## 総合判定

**条件付き採択可能（Major Revision 相当）**

形式的定義・定理トレーサビリティ・仮定監査の構造は FM/ITP/CPP レベルとして十分に機能している。ただし、Lean ソースの物理的不在という根本的な artifact 検証不能状態が解消されない限り、最終採択には至れない。

---

## 主要懸念

### 1. Lean ソースファイルの物理的不在（Critical）

manuscript_fm.md §4.4 と §9 は以下のパスを参照している：
- `paper/lean/UadfU0/U0Spec/Construction.lean`
- `paper/lean/UadfU0/InterLayer/Transfer.lean`
- `paper/lean/UadfU0/InterLayer/Composition.lean`
- `paper/lean/UadfU0/InterLayer/Adequacy.lean`
- `paper/lean/UadfU0/RelatedWork/Galois.lean`
- `paper/lean/UadfU0/U0Spec/IdealRoot.lean`
- `paper/lean/lake-manifest.json`

**提出パッケージにこれらの Lean ソースが含まれていない。** 査読者は `lake build` を実行できない。`sorry = 0` の claim・theorem count = 59 の claim・manifest hash の claim は、いずれも現時点で機械的に検証不能である。FM/ITP/CPP/TACAS は artifact evaluation で実際に build を走らせることを要求する。

### 2. `lifted_transfer` の axiom 申告と実際の一貫性（High）

§4.3 の axiom audit で `lifted_transfer: no axioms` と記載されている。Lean4 において全ての証明は暗黙的に `propext` 等のコア公理に依存するため、「no axioms」は通常 `#print axioms` の出力が空であることを意味する。一方、同じ系の他定理（`preimage_compose`）では `Classical.choice, Quot.sound` が列挙されている。この非対称性は、`hproj` が全称量化された存在命題を含む `lifted_transfer` で `Classical.choice` が不要である理由の説明が必要である。ソース不在のため確認できないが、もし存在除去に tactics が依存しているなら audit 結果が疑わしい。

### 3. theorem_catalog.md の自動生成・同期保証の欠如（High）

theorem_catalog.md は「Total theorem declarations: 59」と記載し、`rg -n '^theorem ' UadfU0 | wc -l` を検証コマンドとして提示している。しかし：
- catalog が手動記述なのか自動生成なのかが不明
- Lean ソース変更時に catalog が自動更新されるメカニズムが記述されていない
- `^theorem ` の grep はインデントされた theorem 宣言や `private theorem` を拾わない可能性がある

カタログとソースの乖離を機械的に防ぐ仕組みが提出パッケージに存在しない。

### 4. `UStar` の parametricity と実用性のギャップ（Medium-High）

§3.8 の ideal-root linkage theorems（`UStar_inter_projDomOn_subset_UAndOn` 等）は `UStar` を定理パラメータとして受け取る。これは正直な設計だが、theorem_catalog.md を見ると `UStar_subset_UAndOn` および `UStar_subset_UAnd` という stronger-looking な theorem も存在する。manuscript では前者2つのみ解説されており、`UStar_subset_UAndOn`（domain 制限なし）が成立する条件が不明確。この定理が `hNecessaryOnDom` なしで証明されているなら manuscript の説明と齟齬が生じる。

---

## 軽微懸念

### 5. `SpecSet α := α -> Prop` と Mathlib `Set α` の関係（Low-Medium）

§2.1 で「this is a local alias, not a direct use of Mathlib `Set α`」と断っているが、`preimage_eq_semanticPullback` の axiom audit で `Quot.sound` が現れる。Mathlib の funext/set_ext 経由であれば理由は明確だが、local alias を使いながら Mathlib の補題を部分的に使っているなら、依存境界を明示すべき。

### 6. `Option.bind` commutation の前提の強さ（Low-Medium）

§3.5 の `preimage_compose` は `hcomm : ∀ x, M.proj j x = Option.bind (M.proj i x) g` を要求する。§2.8 の decomposition template `proj_i := Option.bind obs_i extract_i` と合わせると、`g` が常に存在する（すなわち `proj_j` が `proj_i` の因子分解を持つ）という強い構造的仮定が必要になる。この前提を満たすシステムの規模・条件について manuscript では言及がない。

### 7. password policy ケーススタディの theorem 内容（Low）

§5.2 の `checkConsistent_iff_allThree` は constrained interval domain 上の具体例として示されている。ただし theorem_catalog.md には `req_projection_adequacy` も含まれており、この定理の manuscript 内での言及が薄い。adequacy theorem の具体例として重要であれば §5 内で展開すべき。

### 8. References の不完全性（Low）

§7.5 で参照している Darais & Van Horn (ICFP 2016) "Constructive Galois Connections" は non-adjointness result との対比として重要だが、具体的にどの定理・補題と対比するかが記述されていない。

---

## 必須修正

| # | 対象 | 修正内容 |
|---|---|---|
| M1 | §9 / submission package | Lean ソース全体（`paper/lean/UadfU0/` 以下）をパッケージに含め、`lake build` が clean checkout から通ることを確認・記録すること |
| M2 | §4.4 / fm_submission_checklist.md | `lake build` の実際の stdout ログ（`Build completed successfully` を含む）を artifact として添付し、checklist の `[x]` が具体的証拠に基づくことを明示すること |
| M3 | §4.3 | `lifted_transfer: no axioms` について `#print axioms` の実出力を footnote または appendix に掲載し、他定理との非対称性を説明すること |
| M4 | theorem_catalog.md | catalog の生成方法（手動/自動）を明記し、ソースとの同期を保証するスクリプトまたは CI ステップを提示すること |
| M5 | §3.8 | `UStar_subset_UAndOn`（domain 制限なし）が成立する条件を manuscript 内で明示し、`UStar_inter_projDomOn_subset_UAndOn` との使い分けを説明すること |
