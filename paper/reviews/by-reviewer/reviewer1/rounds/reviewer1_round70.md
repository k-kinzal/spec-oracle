## 総合判定

**条件付き採択可能（Major Revision）**

FM/ITP/CPP水準への提出として技術的完成度は高いが、以下に示す重大懸念が解消されなければ採択困難。

---

## 主要懸念

### W1: 新規性の主張が不明瞭（採択上の最重大問題）

§6および§6.1にて「mathematical identities are not new」と自ら認めつつ、「typed theorem interface layer under partiality」が主貢献と主張する。しかし：

- `Option`モノナドのbind合成による逆像等式（§3.5 `preimage_compose`）は、Mathlib の`Set.preimage_comp`の偏関数版として自明視される可能性が高い
- LUB/GLB特徴付け（`U0_least_upper_bound_iff`、`UAndOn_greatest_lower_bound_iff`、§3.2）は述語集合の包含順序における標準的事実
- **差分（delta）がライブラリ非互換な型構造ゆえの再証明なのか、非自明な新規結果なのかが、査読者に説明されていない**

FM/ITP採択基準では「新規のオートメーション困難性」または「実質的な意味論的洞察」が求められる。§6.1の説明は防御的すぎて積極的な新規性主張になっていない。

### W2: `Classical.choice` の出現と構成的証明主張の不整合

§4.3にて `preimage_compose` に `Classical.choice` が含まれると報告しているが：

- `preimage_compose` の証明（`Composition.lean:74-100`）は `by_cases` を使用しており、これが `Classical.choice` を引き込んでいる
- §4.1で「No implicit classical package opening in core files」と宣言しているが、`by_cases` は暗黙的古典論理依存
- 原稿は「constructive normalization is possible in principle」と述べるが証明は出していない
- **constructivity-sensitive な会議（ITP/CPP）では、この不整合は直接的な却下理由になりうる**

### W3: Adequacy定理の意味論的動機が不足

§3.6で `E`（意味的抽出関係）を `proj` から分離する動機として「separating them allows theorem-level reasoning before committing to a concrete extractor」と述べるが：

- `E = proj` と置いた場合（`hEq : ∀ x y, proj i x = some y ↔ E x y`）の `preimage_eq_semanticPullback` は定義展開で自明
- `AdequacyCounterexample.lean` の `EPlus1` 例（`EPlus1 x y := y = x ∨ y = x + 1`）は `E ≠ proj` の一例だが、**この`E`が実際の仕様抽出でどう発生するかの動機が論文本体に欠けている**
- 抽出器正確性義務（§3.6.1）は「テンプレート」止まりであり、少なくとも1つの具体的充足例（完全に証明された extractor instance）がないと意味論的貢献として弱い

### W4: 67定理のうち核心定理の比率と依存グラフが不明

`theorem_catalog.md` には67定理がファイル別にリストされているが：

- `Definitions/Model.lean` の3定理（`subset_refl`、`subset_trans`、`set_ext`）は順序理論の基礎補題
- `CaseStudy/PasswordPolicy.lean` の4定理はパスワード数値制約の具体例
- **RQ3–RQ5に直接寄与する核心定理は約15–20個程度**であり、「67定理のMechanization」という印象とのギャップを査読者は指摘する可能性がある
- 定理間依存グラフが提供されていないため、どの定理が自明なコロラリーで、どれが実質的な証明労力を要したかが判断できない

---

## 軽微懸念

### M1: §3.7 Related Work が薄い

- BX文献（Xiong et al. 2012）への言及はあるが、近年のδ-lens、Optic、Profunctor-based BX等の発展が参照されていない
- Institution framework との差分（§7.7）は適切に書かれているが、Mossakowski et al. (Hets) は2004年以降に大きく発展しており、最新のHets文献を参照すべき
- Lean4 Mathlib の `Set.preimage` 関連 API との明示的な比較が §6.1 にあると査読者の疑問を先回りできる

### M2: `lake-manifest.json` が空依存

`lake-manifest.json` の `"packages": []` はMathlib非依存を意味するが：

- `#print axioms` 結果に `Quot.sound` が現れる（`preimage_compose`、各adequacy定理）
- これらは Lean4 コアの quotient 型から来るが、SpecSet が `α → Prop` の関数型である場合に `Quot.sound` が必要な経路を §4.3 で説明すべき
- `propext` 依存は `set_ext`（`funext` + `propext`）から来ており説明済みだが、`Quot.sound` の経路説明が欠けている

### M3: §5.2 PasswordPolicy の `req_projection_adequacy` の位置づけ

`req_projection_adequacy` （`PasswordPolicy.lean:54-66`）は `proj i x = some y ↔ E x y` を `y = x` 関係で瞬時に満たすもので、adequacy定理の意義を示す例としては自明すぎる。§5.2 の「not as a general proof of extractor correctness」という断り書きは正しいが、もう少し非自明なインスタンスが欲しい。

### M4: `UAndOn_empty_eq_univ` の operational 含意の記述

§3.3で vacuous-truth edge case として `UAndOn_empty_eq_univ` を挙げているが、「operational interpretation of UAndOn must enforce non-empty active sets」という主張が §8 Limitations に記載されていない。これは実用上の制限であり Limitations 節に明記すべき。

---

## 必須修正

1. **新規性の再記述（W1）**: §6 または §1.3 RQ linkage に、「なぜ既存 Mathlib API をそのまま使えないか」の技術的理由を具体的に示す。異種キャリア型（`carrier : ι → Type`）と `Option` 偏関数を組み合わせた場合に Mathlib の `Set.preimage_comp` が適用不可となる型制約を Lean コードレベルで明示すること。

2. **Classical.choice の扱いの明確化（W2）**: `preimage_compose` の `by_cases` を constructive に書き直すか、または「この定理は古典論理を使用し構成的ではない」と §4.3 に明記する。前者が望ましい（`Option.cases_on` による場合分けで回避可能なはず）。

3. **Adequacy の少なくとも1つの非自明なインスタンス証明（W3）**: §3.6.1 のテンプレートを、具体的な obs/extract 分解を持つ1例で充足させる。`ArtifactBundleExample.lean` の `projFromObsExtract` を用いたインスタンス化が自然な候補。

4. **定理依存グラフまたは「核心定理」の明示（W4）**: `theorem_catalog.md` または論文 §4.5 の traceability 表に、各定理の「論文中での役割（核心/補題/例）」欄を追加すること。
