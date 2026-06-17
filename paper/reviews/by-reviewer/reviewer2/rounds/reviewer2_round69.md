## 総合判定

**条件付き採択（Major Revision）**

ITP/CPP artifact 要件を概ね満たすが、以下の重大リスクが修正なしには採択を推薦できない。

---

## 主要懸念

### 1. ビルド再現性：外部依存ゼロの lake-manifest が未検証

`lake-manifest.json` の `"packages": []` は Mathlib 等外部ライブラリを一切宣言していない。`SpecSet` を `α → Prop` と自己定義しており Mathlib 非依存は整合するが、**clean checkout から `lake build` が実際に通るかのCI証跡が提出物に含まれていない**。manifest hash（`8c098d78...`）も論文内で宣言されているが、hash の計算対象がパッケージ依存0の自明な内容である点で証跡としての価値が低い。

- **必要な修正**: GitHub Actions 等の CI ログ、または `lake build` 成功時の stdout を artifact として添付すること。

### 2. Axiom 監査の不完全性

§4.3 の axiom 監査は `lifted_transfer`（no axioms）から `preimage_compose`（`Classical.choice`）まで主要定理を列挙しているが、**`#print axioms` の対象が定理名のみで、依存する全補題チェーンの監査が確認できない**。特に：

- `checkConsistent_iff_allThree`（PasswordPolicy）は `native_decide` タクティクを使用しており、これは `Lean.Compiler.LLVM` 等の実装依存を呼び込む可能性がある。論文の axiom 一覧にこの定理が含まれていない。
- `UAndOn_empty_eq_univ` および `consistent_iff_exists_UAndOn_pair` の axiom 状況が未開示。

- **必要な修正**: 全 67 定理の `#print axioms` 出力を theorem_catalog に追記、または `native_decide` 使用箇所を明示して「証明カーネル外」と宣言すること。

### 3. カタログ整合性：theorem_catalog と実ソースの乖離リスク

theorem_catalog.md は手動管理されており、**ソースと同期していることの機械的保証がない**。`TwoLayer.lean` が「`example` declarations only; no `theorem` keyword」と注記されているが、`ContradictoryLayers.lean` の `example` 行（`¬ contradictoryModel.Consistent ...`）はカタログに載っていない。これは例示なので問題ないが、カタログが "total theorem declarations: 67" と主張する以上、`example` との境界定義が不明確。

- **必要な修正**: `rg -n '^theorem ' UadfU0 | wc -l` の実行出力をビルドスクリプトの一部として artifact に含め、カタログとの一致を自動検証する手順を §9 に追記すること。

### 4. トレーサビリティ：RQ-to-theorem matrix の参照先不整合

§1.5 の RQ-to-theorem matrix で `RQ1` の Lean anchor として `mem_preimage_iff` と `paper/lean/UadfU0/U0Spec/Construction.lean` を参照しているが、`preimage` 定義自体は `Definitions/Model.lean` にある。matrix の "Main section §2.2, §2.3, §3.1" も §3.1 が「Foundational lemmas」として `Construction.lean` 定理を挙げており、**定義ファイルとの区別がトレーサビリティ上の穴**になっている。

- **必要な修正**: RQ matrix の "Lean anchor" 列に定義と定理を分けて明記（例: `definition in Definitions/Model.lean`, `theorem in U0Spec/Construction.lean`）すること。

---

## 軽微懸念

1. **`Classical.choice` の正当化が薄い**: §4.3 で `preimage_compose` に `Classical.choice` が現れる理由を「witness reconstruction through extensional equality over existential branches」と説明しているが、existential witness を `Option.bind` の `some` branch に限定すれば constructive に書ける可能性がある。constructivity 非主張は明記されているが、ITP 系査読者から「なぜ choice が必要か」の質問が来る可能性が高い。簡潔な正当化を §4.3 に1〜2文追加することを推奨。

2. **`preimageMay` の定義位置**: `preimageMay` は `Construction.lean` 内で定義されているが、`Definitions/Model.lean` の `preimage` と対称的に扱われるべき定義であり、位置の非対称性が論文読者を混乱させる可能性がある。必須ではないが整理を推奨。

3. **§6.1 の "Baseline capabilities" 記述**: standard theorem-library との差分を述べているが、Mathlib の `Set.preimage` との具体的な API 差（例: `carrier : ι → Type` による heterogeneous index が Mathlib にない理由等）の参照が抽象的。査読者が「Mathlib の `MeasureTheory.MeasurableSpace` 等で既存では？」と問う余地がある。

4. **Related work §7 の引用バランス**: Institution theory（Goguen-Burstall 1984）と BX の引用はあるが、Lean4 での mechanized set theory（例: Mathlib `Order.CompleteLattice`）との差分記述がない。ITP/CPP 査読者には Mathlib との差分が重要。

---

## 必須修正

| 優先度 | 項目 | 対応箇所 |
|--------|------|----------|
| P1 | CI/CD または `lake build` 成功 stdout を artifact に添付 | §9 / 提出パッケージ |
| P1 | `native_decide` 使用定理の axiom 状況を明記（カーネル外と宣言するか `decide` に置換） | §4.3 / PasswordPolicy.lean |
| P1 | RQ-to-theorem matrix の定義ファイルと定理ファイルを分離明記 | §1.5 |
| P2 | theorem_catalog を `rg` 出力で自動検証するスクリプトを §9 に追記 | §9 |
| P2 | `Classical.choice` が `preimage_compose` に必要な理由を1〜2文で補足 | §4.3 |
