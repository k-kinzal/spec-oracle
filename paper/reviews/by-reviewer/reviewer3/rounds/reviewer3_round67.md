## 査読報告：UAD/f Two-Operator Kernel under Partial Projections

---

## 総合判定

**条件付き採択圏内（Weak Accept / Minor Revision）**

FM/FASE/CPP の採択ラインに届いており、形式的完全性と再現性の観点では水準を満たしている。ただし後述の主要懸念を解消しなければ、「採択に値する新規性主張」として審査委員会での合意形成が困難になる。

---

## 主要懸念

### 1. 新規性主張の粒度が不明瞭（§1 / §6）

**懸念**: §6 "Concrete delta against baseline theorem libraries" は「assumption-audited packaging」を主たる貢献として挙げる。これは工学的貢献の記述であり、FM/CPP 系で求められる *数学的新規性* の主張とは性格が異なる。  
**具体箇所**: §0.1 Claims 1–4 と §6.1 Claim boundary の「we claim this specific partial/heterogeneous/assumption-audited kernel is packaged」という記述が、アーカイブ（再パッケージ）寄与と区別できない。  
**必要な対処**: 部分写像（`Option`）付き多型担体（`carrier : ι -> Type`）の組み合わせが、既存のどのライブラリにも存在しないことを文献比較によって明示すること。単に「パッケージ化した」ではなく「この型クラス構成は先行研究にない」と言える箇所を特定すること。

### 2. §3.7 非隣接性定理の FM 圏内での位置づけが弱い

**懸念**: `no_left_adjoint_of_partial`（§3.7 / `RelatedWork/Galois.lean`）は証明は正しいが、命題としては自明に近い。「`Option` 型の preimage は右随伴を持つか」はほぼ自明の否定であり、Darais & Van Horn (2016) や Constructive Galois Connections の文脈で暗示される既知事実に近い。  
**必要な対処**: この定理が「なぜ非自明か」を §3.7 の冒頭か §7.5 に 2–3 文で明示する。代替策として、より強い形（例：`preimage` が特定の弱化条件下でも随伴を持たないこと）に強化するか、「この論文での役割はガードレールであり独立した新規性主張ではない」と明記して新規性主張から切り離す。

### 3. `semanticPullback` における抽象関係 `E` の正当化が不十分（§3.6）

**懸念**: §3.6.1 の proof-obligation template では `E` を具体 extractor の代替として使うが、なぜ `proj` と別の抽象を導入する必要があるかの動機付けが §3.6 冒頭の 3 文のみで済んでいる。  
**具体問題**: `proj` があれば `semanticPullback` は `preimage` と同値（§3.6 adequacy theorem 群がそれを証明している）であり、`E` は `proj` の「別名」にすぎない可能性がある。つまり adequacy theorems 群が trivially true になるリスクがある。  
**必要な対処**: 「`E` が `proj` と等価でない場合」（すなわち extractor が `proj` と整合しない場合）の例を§5 か §3.6.1 に追加して、一側面 soundness/completeness が崩れるケースを示すこと。これにより one-sided decomposition の非自明性が担保される。

### 4. §3.8 `UStar` の意味論的地位が曖昧（`IdealRoot.lean`）

**懸念**: `UStar` は theorem parameter として "parametric input" と明示されているが、§3.8 の命題群（特に `UStar_inter_projDomOn_subset_UAndOn`）は「`UStar` の性質を一切仮定せず条件を課すだけ」であるため、`UStar` に何を代入しても成り立つ trivial conditional に見える。  
**具体例**: `UStar = ∅` なら全定理は vacuously true。`UStar = univ` なら `hNecessaryOnDom` が非常に強い仮定になり証明不能に近い。どちらの代入でも論文の内容は変わらない。  
**必要な対処**: `UStar` が「partial projections で observable な部分の近似」であることを type-level constraint または別の公理的前提として固定するか、§3.8 を「単なる条件付き包含定理群」として新規性から切り離す。

---

## 軽微懸念

### 5. 定理数 59 の内訳と novelty 密度（§4.4 / theorem_catalog.md）

定理 59 のうち `Examples/` と `CaseStudy/` に 9 件、`Definitions/Model.lean` に 3 件（`subset_refl`, `subset_trans`, `set_ext`）が含まれる。後者はほぼ基本補題であり、論文本文の novelty カウントに含めると印象が希薄になるリスクがある。審査員向けに「主要定理は X 件、補題・例は Y 件」と分類した一覧を §4.4 か appendix に置くことを推奨する。

### 6. `preimage_compose` の `Classical.choice` 依存（§4.3 axiom audit）

§4.3 で `preimage_compose` が `Classical.choice` に依存することを「normalization は主張しない」と注記しているが、constructivity を重視する ITP/CPP 読者には懸念材料になりうる。依存の具体的原因（existential witness reconstruction の `funext + propext` 経路）が本文に書かれているため説明は足りているが、「Lean4 で構成的に書き直せるか、あるいは依存は本質的か」を 1 文で述べると査読で刺されにくくなる。

### 7. Related Work §7.3–§7.4 の参照文献の薄さ

View consistency（§7.3）と BX（§7.4）の段落が各 2 文で終わっており、引用も [6][7][8] のみ。FASE/MODELS 系の審査員はこのあたりを厳しく見る。最低限 Czarnecki et al. (2009) や 近年の UML 多ビュー整合性研究を 1–2 件追加することを推奨する。

### 8. §5.1 ArtifactBundle example の `UAnd` 証明で `hi` が unused

`paper/lean/UadfU0/Examples/ArtifactBundleExample.lean` の `goodBundle ∈ artifactBundleModel.UAnd` の証明で `intro i hi` としながら `hi` を cases 内で使っていない。警告が出る可能性があり、査読の artifactcheck で指摘されやすい。

---

## 必須修正

1. **§6.1 / §0.1**: 「既存ライブラリとの型レベル差分」を文献比較によって明示し、"packaging" ではなく "typed interface not available in Mathlib/Std4 as a unit" として主張を再記述する。

2. **§3.6 + §5**: `E ≠ proj` となる反例（一側面 soundness は成立するが completeness が崩れる具体例）を mechanized example として追加する。`preimage_eq_semanticPullback` 系 theorem 群の非自明性の根拠となる。

3. **§3.7**: `no_left_adjoint_of_partial` を「独立した novelty ではなくカーネル内部のガードレール定理」として §0.2 Non-claims に明示的に追加するか、命題を強化する。現状では FM 系審査員に「自明では」と指摘されるリスクが高い。

4. **§3.8**: `UStar` に対する制約の欠如（vacuous conditional 問題）を解消する。最低限「`UStar` は `proj`-observable な点で必要条件を満たす想定根拠を持つ」という想定を定理の前提として文章化し、assumption_matrix.md に対応行を追加する。
