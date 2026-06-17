## 総合判定

**Major Revision（採択不可、要大幅修正）**

境界は Reject に近い Major Revision。主要な欠陥は定義整合・新規性位置づけ・仮定監査の3点に集中しており、いずれも論文の中核的主張に直接影響する。

---

## 主要懸念

### 1. 定義整合の問題：`UAnd` と `U0` の非対称性（§2.5, §2.3, Model.lean）

`U0` は `Model.lean` に直接定義（`def U0`）されているが、`UAnd` は `U0Spec/Construction.lean:def UAnd` で `UAndOn (fun _ => True)` のエイリアスとして定義されている。  
一方、原稿 §2.5 は両者を「Global forms」として対称的に提示する。

**問題**:
- `U0` と `UAnd` の定義居住ファイルが異なる（`Definitions/Model.lean` vs `U0Spec/Construction.lean`）。原稿の §2.3 コードスニペットには `UAnd`/`UAndOn` の定義が含まれていない。
- `U0On` の定義は `Construction.lean` にあるが、`U0` は `Model.lean` にある。`U0_eq_U0On_all`（`Construction.lean`）で事後的に同一視している。これは「最初から `U0On(True)` として定義すれば済む」構造であり、論文記載の設計理由が不明瞭。
- §1.5 のトレーサビリティ行列で `RQ1` のアンカーとして `mem_preimage_iff` が挙げられているが、`mem_preimage_iff` は Lean 定義の展開補題であり「typed definition」ではない。定義そのものの場所（`def preimage` in `Model.lean`）を指すべき。

### 2. 新規性・位置づけの不十分さ（§6, §7）

§6.1「Concrete delta against baseline theorem libraries」は以下を主張する：
> "we claim this specific partial/heterogeneous/assumption-audited kernel is packaged and machine-checked end-to-end"

**問題**:
- FM/ITP/CPP の査読基準では「パッケージング」は technical contribution として認められない。各定理の証明困難性の主張（§6 "Per-theorem hardness summary"）は散文的主張のみで、対応する反例・相反可能性の排除が insufficient である。
  - `lifted_transfer`：「same-root witness linkage is required」は自明（existential lifting）。Mathlib の `Set.image` + `Set.preimage` + `Function.comp` の組み合わせとの差分が不明示。
  - `preimage_compose`：`Option.bind` の case 分析は教科書的。impossible branch の「constructive elimination」の主張は §4.3 の公理監査（`Classical.choice` が現れる）と矛盾気味。
- `no_left_adjoint_of_partial`（§3.7, `Galois.lean`）は重要な guardrail と説明するが、証明は trivial（`none` 点でのシングルトン集合を代入するだけ）。FoSSaCS/LICS レベルならば Reject、CPP でも novelty claim として提示するには弱い。

### 3. 仮定監査の不整合（§4.3, §3.7）

§4.3 の公理監査表：
```
lifted_transfer: no axioms
preimage_compose: [propext, Classical.choice, Quot.sound]
```

**問題**:
- `lifted_transfer` が「no axioms」である一方、`Transfer.lean` は `Consistency.lean` を import しており、その `Consistency.lean` は `Minimality.lean` を import する。推移的公理汚染の確認が提示されていない（`#print axioms` の範囲が `lifted_transfer` 単体か推移的閉包か不明）。
- `preimage_compose` に `Classical.choice` が必要な理由として「witness reconstruction through extensional equality over existential branches」と説明するが、`Composition.lean` の実際の証明は `by_cases` と `simp` を使っており constructivity の損失を正当化する説明が弱い。
- §4.1「No implicit classical package opening in core files」の主張と `Classical.choice` の使用が surface-level で矛盾に見える。詳細説明が必要。

### 4. `semanticPullback` の index argument の型不整合（Adequacy.lean）

`Adequacy.lean` の定義：
```lean
def semanticPullback {i : ι} (E : α → M.carrier i → Prop) ...
```

対し、`AdequacyCounterexample.lean` の使用：
```lean
oneLayerNatModel.semanticPullback (i := onlyOne) EPlus1 singletonOne
```

**問題**:
- `semanticPullback` は `i : ι` を implicit argument としており、`i` は `E` の型から推論されるはず。しかし `EPlus1 : Nat → Nat → Prop` のとき `M.carrier onlyOne = Nat` なので型推論は成立する。表面上は問題ないが、原稿 §3.6 の説明では `i` が `semanticPullback` のパラメータとして明示されておらず、読者に不整合な印象を与える。原稿の signature 記述の改善が必要。

### 5. `lake-manifest.json` が依存パッケージを持たない（再現性）

```json
{"packages": [], ...}
```

**問題**:
- Lean 4 で Mathlib を使わない場合でも、`lake-manifest.json` が空 packages のとき build 再現性はツールチェーンのみに依存する。原稿 §4.2 で `set_ext` を `funext + propext` で証明しているが、`propext` は core axiom であり問題ない。しかし `lake build` が clean checkout で成功することの外部検証が提出物に含まれていない。
- `paper/lean/lean-toolchain: leanprover/lean4:v4.27.0` は nightly ではなく release 版なので許容されるが、アーカイブの取得可能性に関する記載がない（Zenodo 等）。

---

## 軽微懸念

### 6. 記号の統一性（§2.1 vs Lean）

原稿は `SpecSet α := α -> Prop` を「local alias」と記述するが、§2.1 では「not a direct use of Mathlib `Set α`」と注記するのみ。FM/ITP 読者は `Set α = α → Prop` を知っているので、この distinction の技術的含意（universe polymorphism の扱い等）を一文で説明すべき。

### 7. `UAndOn_empty_eq_univ` の記述（§3.3, Construction.lean:L214付近）

原稿は「vacuous-truth edge case は explicit に theoremize されている」と主張するが、`UAndOn_empty_eq_univ` の型は `M.UAndOn (fun _ : ι => False) = (fun _ : α => True)` であり、等式の右辺が `Set.univ` 相当の記述になっていない。これは `sUniv`（`Galois.lean` で定義）との非統一であり、論文内で `univ` という語を使う場合の定義的裏付けが不明瞭。

### 8. `RQ5` の位置づけ（§0.3 vs §3.6）

§0.3 は「`RQ5` は abstract relation `E` 上の theorem-level decomposition」と述べるが、§3.6 のタイトルは「One-sided adequacy decomposition (must and may)」。  
adequacy ≠ decomposition であり、「adequacy を must/complete に分解すること」が RQ5 の実質的内容だが、原稿の記述は RQ5 の答えが何を主張しているのかを曖昧にしている。

### 9. `IdealRoot.lean` の `UStar_subset_UAndOn`（§3.8）

`UStar_subset_UAndOn` は theorem catalog に記載されているが、原稿 §3.8 の「Representative Lean signature」として `UStar_inter_projDomOn_subset_UAndOn` のみを取り上げている。  
`UStar_subset_UAndOn` は domain restriction なしのバージョンであり、§3.8 の説明との関係（どちらが主定理か）が不明確。

---

## 必須修正

1. **§1.5 トレーサビリティ行列**（`RQ1` 行）：`mem_preimage_iff` を `def preimage` のファイル・行番号参照に修正すること。

2. **§4.3 公理監査**：`lifted_transfer` の `#print axioms` 出力が推移的閉包を含む形で提示されていることを明示すること。`Classical.choice` 使用と §4.1 主張の矛盾について一段落の説明を追加すること。

3. **§6 新規性の再記述**：`no_left_adjoint_of_partial`（§3.7）について、「standaloneな数学的新規性ではない」という §0.2 の non-claim と、§6 での「partiality-specific structural break」の主張が混在している。どちらの文脈でも読める曖昧な記述を除去し、guardrail としての mechanization 価値の記述に一本化すること。

4. **再現性メタデータ**（§9）：`lake build` の外部検証証跡（CI ログ、Zenodo アーカイブ等）への参照を追加するか、その不在を submission checklist に明記すること。現状の checklist は自己申告のみ。

5. **§3.3 U0/UAnd 分離**：`U0` が `Model.lean` で定義され `UAnd` が `Construction.lean` で定義される設計上の理由を原稿に明示すること。または定義を統一した上で traceability matrix を更新すること。
