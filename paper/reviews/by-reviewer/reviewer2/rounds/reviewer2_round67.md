## 総合判定

**条件付き採択可（Major Revision）**

機械検証の骨格は堅牢だが、artifact の build 可能性・定理追跡可能性の独立検証ができない重大リスクが複数存在する。以下に詳述する。

---

## 主要懸念

### 1. `lake build` の独立検証不可能性（§4.4, §9）

- `paper/lean/lake-manifest.json` のハッシュ値（`8c098d78...`）が manuscript に記載されているが、添付ファイルに `lake-manifest.json` 本体が含まれていない。
- `lean-toolchain` ファイルも未添付。toolchain version `leanprover/lean4:v4.27.0` が実際に使用されているか確認不能。
- **結果**: 査読者が clean checkout から `lake build` を実行して `Build completed successfully` を確認する手順が閉じていない。Artifact 採択要件を満たさない。

### 2. theorem catalog の計数と実装の照合不整合リスク（§4.4, §4.5）

- theorem catalog（`theorem_catalog.md`）は合計 59 件と宣言するが、添付 `.lean` ファイルのカウントとの照合が必要。
- `TwoLayer.lean` は添付されているが catalog に **記載がない**（theorem を含む example ファイル扱いだが、証明可能な命題が複数ある）。
- `ArtifactBundleExample.lean` 内の `example :` ブロック（`goodBundle ∈ U0` 等）は `theorem` キーワードを使っておらず、catalog の `theorem count: 1` と実態が合わない可能性。
- **結果**: `rg -n '^theorem ' UadfU0 | wc -l` の結果が 59 になるかどうか添付ファイルだけでは確認できない。

### 3. `sorry` ゼロ宣言の機械確認不可（§4.4）

- 添付 `.lean` ファイルを目視確認した限り `sorry` はないが、`paper/lean` 配下の全ファイルが添付されていない（`Definitions/Model.lean` 以外の `Definitions/` 配下、`lake-manifest.json` 等）。
- `rg -n '\bsorry\b' UadfU0 || true` の実行結果が manuscript に **静的に記録されていない**。コマンドの出力を appendix に収録すべき。

### 4. `Classical.choice` の使用と constructivity 宣言の曖昧さ（§4.3）

- `preimage_compose` が `[propext, Classical.choice, Quot.sound]` に依存すると audit で宣言されているが、§4.1 では「No implicit classical package opening」と主張している。
- `open Classical` を使わなくても Lean 4 のコア経由で `Classical.choice` が入ることは技術的に正しいが、ITP/CPP 投稿では constructivity boundary の説明が不十分。
- §4.3 の説明文「this paper does not claim constructivity-preserving normalization for those proofs」は記載されているが、どの theorem が classical に依存し、どれが依存しないかの**完全な axiom audit 表**が存在しない（7 件のみ記載、全 59 件には及ばない）。

### 5. `UStar` の parametric 性と RQ2 linkage の乖離（§3.8, §1.5）

- RQ-定理対応表で RQ2 は `lifted_subset_preimage_domain` と `U0_witness_projects_to_some_domain` で答えられるとされている。
- しかし `UStar_inter_projDomOn_subset_UAndOn` の `UStar` は theorem の input parameter であり「constructed by this kernel ではない」と §3.8 で明言される。
- これは `U0` / `UAnd` が実際に理想根仕様を近似するという直感的な訴求力を弱める。RQ2 と §3.8 の間に説明上の gap がある。

---

## 軽微懸念

### A. `TwoLayer.lean` の未記載（`theorem_catalog.md`）

- `TwoLayer.lean` に複数の `example` ブロック（事実上の命題証明）が存在するが catalog に列挙なし。
- 59 件カウントに含まれるかどうか不明。

### B. `ArtifactBundleExample.lean` の `UAnd` 使用と `UAndOn` 定義の対応

- `example : goodBundle ∈ artifactBundleModel.UAnd` の証明で `intro i hi` を実行しているが、`UAnd` の定義は `UAndOn (fun _ => True)` であり `hi : True`。
- 証明は正しいが、`hi` を destructure せずに使っており、`cases i` で全 tag を処理する形式が冗長。Lean 4 の type-checking は通るが、読者には分かりにくい。

### C. §3.3 の `UAndOn_empty_eq_univ` の operational 意味論への参照

- 「any consistency interpretation must explicitly enforce ∃ i, active i」と manuscript は述べるが、`UAndOn_empty_eq_univ` が operational pipeline でどう使われるかの具体例がない。
- engineering paper への参照で解決可能だが、formal paper 単体では宙ぶらりん。

### D. `PasswordPolicy.lean` の `native_decide` 使用

- `example : checkConsistent exConsistentReq ...` および反例の `native_decide` は kernel compute に依存し、proof term として記録されない。
- ITP/CPP の artifact 審査では `native_decide` が「証明として受け入れられるか」を明示する必要がある（Lean 4 では accepted だが、論文上で言及がない）。

---

## 必須修正

| 優先度 | 対象 | 修正内容 |
|---|---|---|
| **必須 1** | §9 / artifact package | `paper/lean/lake-manifest.json` と `lean-toolchain` を submission package に含め、ハッシュ照合手順を明示 |
| **必須 2** | §4.4 | `rg -n '\bsorry\b' UadfU0` の実行結果（ゼロ行）を appendix またはコードブロックで静的に記録 |
| **必須 3** | §4.4 / `theorem_catalog.md` | `TwoLayer.lean` の扱いを catalog に記載（含む or 除外の根拠を明示）し、59 件カウントの再確認 |
| **必須 4** | §4.3 | axiom audit を全 core theorem（少なくとも論文内で individually 言及された全定理）に拡張。`Classical.choice` 使用範囲の境界を表で明示 |
| **必須 5** | §1.5 RQ2 行 | `UStar` が parametric input である点を RQ2 linkage の説明に反映。「RQ2 は conditional linkage theorem であり UStar の構成ではない」旨を明記 |
