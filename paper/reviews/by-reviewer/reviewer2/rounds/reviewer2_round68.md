# ITP/CPP 査読レポート（UAD/f Lean4 Mechanization）

---

## 総合判定

**条件付き採択不可（Major Revision Required）**

形式化の技術的内容は健全であり、`sorry` なし・公理監査済みという点は評価できる。しかし、以下に列挙する重大リスクが解消されないまま提出されており、ITP/CPP の採択基準（build 再現性・定理トレーサビリティ・公理監査の厳密性）を満たしていない。

---

## 主要懸念

### M1. Build 再現性：`lake-manifest.json` が依存パッケージを宣言しない

**該当箇所：** `paper/lean/lake-manifest.json`

```json
{"packages": [], ...}
```

`UadfU0.lean` は Lean4 標準ライブラリ（`Init.*`）のみを使用しているように見えるが、`Mathlib` 等への依存がないことは原稿本文では明示されていない。一方 §4.3 で `propext`、`Classical.choice`、`Quot.sound` の使用を報告しており、これらは `Init` に含まれるが、意図的な依存範囲の宣言が欠落している。

**リスク：** 審査員が `lake build` を clean checkout で実行した際、toolchain バージョン（`v4.27.0`）との互換性が保証されない環境では成功しない可能性がある。また `~/.elan/bin/lake` の絶対パス指定は CI 非互換。

**必要対応：** `lakefile.lean` または `lakefile.toml` の内容を開示し、依存パッケージ（または依存なし）を明示すること。ビルドコマンドを `lake build` のみにする形で標準化すること。

---

### M2. 定理カタログ整合：カタログ記載数と実ソースの照合不可

**該当箇所：** `paper/formal-methods/appendix/theorem_catalog.md`、§4.4

カタログは「Total theorem declarations: 63」と主張し、ファイル別内訳も示している。しかし提出ファイルで確認できる `theorem` キーワードの分布と以下の点で齟齬リスクがある：

- `paper/lean/UadfU0/Examples/TwoLayer.lean` はカタログで `theorem count: 0`（`example` のみ）と記載しているが、このファイルには `example` が6個存在し、そのうち一部は証明義務を果たしている。カタログ上の「theorem count」の定義が `theorem` キーワードのみであることは明示されているが、`example` を除外する根拠が原稿内で説明されていない。
- §4.4 の検証コマンド `rg -n '^theorem ' UadfU0 | wc -l` が `63` を返すことを主張しているが、実際にカタログの内訳を合計すると `4+3+1+4+1+1+2+1+0+6+2+3+2+1+19+6+7 = 63` となり数値自体は整合している。ただし、この整合性は提出時点のスナップショットに依存しており、Lean ファイルが変更された場合に自動的に検出される仕組みがない。

**リスク：** カタログが手動管理されており、Lean ソースとの同期ズレが将来生じた場合に検出できない。ITP 採録論文として artifact が永続化される際に問題となる。

**必要対応：** カタログ生成コマンドを再現手順に含めるか、Lean の `#check` / `simp` lemma list 出力などで自動生成できることを示すこと。

---

### M3. 公理監査の不完全性：`Classical.choice` 使用の範囲が不明確

**該当箇所：** §4.3、`paper/lean/UadfU0/InterLayer/Composition.lean`

§4.3 の公理監査では主要定理の `#print axioms` 結果を列挙しているが：

- `preimage_compose` に `Classical.choice` が含まれるとされる一方、`preimage_eq_semanticPullback`（`Adequacy.lean`）には `[propext, Quot.sound]` のみとされている。しかし `Adequacy.lean` は `Construction.lean` を `import` しており、`Construction.lean` の定理が `Classical.choice` を使用しているかが未開示。
- `lifted_transfer` が「no axioms」とされているが、証明内で `rcases`（`Classical.choice` を内部的に使用する可能性）が用いられており、主張との整合を審査員は独立に確認できない。

**リスク：** 「no axioms」の主張が誤っている場合、constructivity に関する §4.3 の開示が虚偽となる。CPP のような constructive proof に厳格な会場では致命的。

**必要対応：** 全63定理について `#print axioms` の結果を appendix に列挙するか、主要定理分についてのみ完全な出力をそのまま掲載すること。

---

### M4. 定理トレーサビリティ：`UAnd` の定義がトレーサビリティ表に欠落

**該当箇所：** §4.5 の定理-ファイル対応表、`paper/lean/UadfU0/U0Spec/Construction.lean`

§4.5 の表では `U0On_monotone`、`UAndOn_antitone`、`UAndOn_subset_U0On`、`UAndOn_subset_UAndMayOn` が `Construction.lean` に帰属されているが、原稿本文 §3.3 で核心的結果として挙げられている `UAndOn_empty_eq_univ` および `consistent_iff_exists_UAndOn_pair` が表に存在しない。

カタログでは `Construction.lean` の theorem count は 19 と記載されており、これら2定理は実際に同ファイルに存在する（Lean ソースで確認済み）。

**リスク：** 原稿の主張（§3.3「Central role-separation result」）と artifact トレーサビリティ表が整合していない。査読者が主張の検証を行う際に参照先が不明確となる。

**必要対応：** §4.5 の表に `UAndOn_empty_eq_univ`、`consistent_iff_exists_UAndOn_pair` を追加すること。

---

## 軽微懸念

### m1. `manifest` ハッシュ値の開示方法

**該当箇所：** §4.3

`lake-manifest.json` のハッシュとして `8c098d788704fb7c279c7004a1f492723bd892acf2500483665ae39e7a00a6e7` が原稿内に記載されているが、このハッシュが何のハッシュ（ファイルの SHA-256 か）であるかの計算方法が未説明。`lake-manifest.json` の内容（`{"packages": [], ...}`）は短く、審査員が独立に確認できる形になっていない。

**必要対応：** ハッシュの計算コマンド（例: `sha256sum paper/lean/lake-manifest.json`）を再現手順に追記すること。

---

### m2. `SpecSet` の Mathlib `Set` との差異説明

**該当箇所：** §2.1

`SpecSet α := α -> Prop` が Mathlib の `Set α` と同型であることは自明だが、なぜ Mathlib を使用せず独自定義にしたかの理由（依存最小化、あるいは設計上の理由）が明示されていない。ITP 審査では依存関係の選択は説明義務がある。

---

### m3. `RQ1`–`RQ5` の評価基準との対応

**該当箇所：** §1.4（評価基準）と §1.5（RQ-定理マトリクス）

§1.4 の評価基準4項目（definition integrity, theorem integrity, mechanization integrity, claim integrity）それぞれについて、最終的な評価結果が原稿のどこにも記述されていない。評価基準を提示した以上、結論節か付録で各基準の達成状況を明示することが望ましい。

---

### m4. `AdequacyCounterexample.lean` の位置づけ

**該当箇所：** §5.3、`paper/lean/UadfU0/Examples/AdequacyCounterexample.lean`

`EPlus1_not_complete` の証明で `Nat.zero_ne_one` を用いているが、この補題は `Init.Data.Nat.Basic` に依存する。他の `example` ファイルと同様に `import UadfU0.InterLayer.Adequacy` のみで import chain が完結しているが、`Nat.zero_ne_one` の axiom 依存は §4.3 の公理監査対象に含まれていない。軽微だが一貫性のため追記が望ましい。

---

## 必須修正

| 優先度 | 対象 | 修正内容 |
|---|---|---|
| **必須** | `lake-manifest.json` / `lakefile` | 依存パッケージ（または依存なし）の明示的宣言と `lakefile` の開示 |
| **必須** | §4.3 公理監査 | 全主要定理の `#print axioms` 完全出力の掲載（少なくとも `lifted_transfer` の「no axioms」主張の独立確認手順） |
| **必須** | §4.5 定理トレーサビリティ表 | `UAndOn_empty_eq_univ`、`consistent_iff_exists_UAndOn_pair` の追加 |
| **必須** | §9 再現手順 | `lake build` コマンドのパスを絶対指定から標準化、manifest ハッシュ計算コマンドの追記 |
| **推奨** | §4.3 | `SpecSet` が Mathlib 非依存である設計理由の一文追記 |
| **推奨** | Appendix | カタログ自動生成手順またはスクリプトの追記 |
