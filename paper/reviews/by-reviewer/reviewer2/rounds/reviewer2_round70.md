## 総合判定

**条件付き採択（Minor Revision）**

採択水準には到達しているが、以下の懸念事項への対応が必須。

---

## 主要懸念

### 1. ビルド再現性：Mathlib依存なし構成の未説明リスク

`lake-manifest.json` に `"packages": []` とあり、Mathlib を一切使用していない。これ自体は問題ではないが、原稿の §4.3 で `propext`、`Classical.choice`、`Quot.sound` が公理として報告されているにもかかわらず、それらの由来（Lean4コアカーネル固有公理か否か）が説明されていない。審査者は「なぜMathlib不使用でこれらの公理が現れるのか」を問う可能性が高い。

**必須修正**: §4.3 に「これらはLean4コアカーネルに内包される公理であり、外部ライブラリに由来しない」旨を明記すること。

### 2. 公理監査：`Classical.choice` の出現と構成性の主張の整合性

`preimage_compose` に `Classical.choice` が依存していることが開示されているが、§4.1 の機械化原則に「No implicit classical package opening in core files」と記載されている。この原則と `Classical.choice` 依存の整合性について §4.3 の説明（「constructive rewriting is possible in principle」）は曖昧であり、FM/ITP審査基準では不十分。

**必須修正**: `Classical.choice` が `open Classical` を使わずともどのように導入されるか（たとえば `Iff.mp` 経由のterm-mode推論など）を具体的に説明するか、または「コア公理として受容する」と明示的に立場を宣言すること。

### 3. カタログ整合性：定理数67の検証可能性

`theorem_catalog.md` の合計が正しく67であることはファイルをカウントすると確認できる。しかし `TwoLayer.lean` が「`example` declarations only; no `theorem` keyword」と注記されているにもかかわらず、Lean4の `example` は実際に型検査される証明であり、カタログへの不記載がサブミッション評価者に「未検証」と誤認される懸念がある。

**必須修正**: `TwoLayer.lean` の `example` 群が型検査されていることを脚注またはカタログ注記で明示すること。

### 4. トレーサビリティ：`UStar_subset_UAnd` のカタログ不整合

`theorem_catalog.md` の `IdealRoot.lean` セクションに `UStar_subset_UAnd` が6番目として列挙されているが、原稿 §4.5 のトレーサビリティ表では `ideal-root observability-domain linkage` に対して3定理しか挙げられておらず (`UStar_inter_projDomOn_subset_UAndOn`, `UStar_inter_projDomOn_subset_U0On_of_nonempty_active`, `UStar_subset_UAndMayOn`) 、`UStar_subset_UAnd` と `UStar_subset_UAndOn`、`UStar_subset_U0On_of_nonempty_active` が欠落している。

**必須修正**: §4.5 のトレーサビリティ表を `IdealRoot.lean` の全6定理を網羅するよう修正すること。

---

## 軽微懸念

### 5. `build_evidence.md` のCIとの乖離

ビルドエビデンスがローカル実行の snapshot のみであり、外部CI（GitHub Actions等）との接続がない。FM/CPP投稿では再現可能なCI URLまたはアーティファクトハッシュチェーンが期待されることがある。ただし原稿は「not a replacement for external CI」と明記しており、採択妨げにはならない。

### 6. `PasswordPolicy.lean` の `native_decide` 使用

2つの `example` で `native_decide` を使用している。これはLean4のコンパイル済み評価器に依存するため、厳密な形式手法の文脈では `decide` より信頼性が低いと見なされる場合がある。本論文の主張範囲外（sanity layer）であるため軽微だが、一言断りを入れることが望ましい。

### 7. 参考文献の選択的網羅性

Galois接続の機械化に関して Darais & Van Horn (2016) のみが引用されているが、Lean/Coqでの部分写像に関する関連機械化（例：Partial Orders in Mathlib等）への言及がない。査読者が関連研究の網羅性を問う可能性がある。

---

## 必須修正（サマリ）

| # | 対象箇所 | 修正内容 |
|---|---|---|
| M1 | §4.3 | `propext`/`Classical.choice`/`Quot.sound` がLean4コアカーネル由来であることを明記 |
| M2 | §4.3 | `Classical.choice` 導入経路の具体的説明または構成性立場の明示 |
| M3 | `theorem_catalog.md` + §4.4 | `TwoLayer.lean` の `example` 群が型検査済みであることを注記 |
| M4 | §4.5 トレーサビリティ表 | `IdealRoot.lean` の全6定理を表に追加 |
