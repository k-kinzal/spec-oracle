# 査読結果

---

## 総合判定

**Major Revision（採択不可・大幅修正要求）**

---

## 主要懸念（Major）

### M1: 形式的新規性の欠如・クレームの過少明示化
**Section 6 および Section 7 に関連**

論文は自ら「classical overlap（古典的重複）」として以下を非新規と認める：
- 逆像の単調性
- LUB/GLB 恒等式
- 矛盾/非一貫性の双対性

「機械化特有の価値」として挙げられるのは (1) 仮定の表面化、(2) 部分性の規律、(3) 充足性の片側粒度、(4) 随伴接続の注意、(5) 可観測域制限 の5点だが、**これらが既存の Lean/Coq による形式化作業と何が異なるのかが論証されていない**。

- FM/ITP/CPP 等において「implicit premises を explicit にすること」自体は貢献として認められるが、その程度が軽微であることが論文自身の記述から透けて見える。
- 特に `lifted_transfer`、`preimage_compose` について、Section 6 の "per-theorem hardness summary" は主観的主張に過ぎず、既存文献（abstract interpretation、BX、institutions）と比較した **証明上の困難さの客観的論証** が存在しない。

**必須修正**: 各定理について、既存形式化作業では何が困難だったか、本論文がどう解決したかを技術的に証明せよ。

---

### M2: 「UAD/f モデル」の先行研究との差別化が不十分
**Section 7 に関連**

先行研究セクションが7つのサブセクション（抽象解釈、institutions、ビュー一貫性、BX、Galois接続）に言及するが、**各先行研究との技術的差異が「スコープが違う」「より狭い」という退避的記述に終始している**。

- 例：Section 7.2「Our scope is narrower」、Section 7.4「our theorems isolate minimal one-way conditions」は差異の説明ではなく、単なる範囲限定の言い訳である。
- `Model ι α` の構造は institution の signature/sentence/satisfaction に対応する何らかの制限版に見えるが、その対応関係が明示されていない。
- BX 文献（Xiong et al., SoSyM 2012）との関係も、"one-way reverse-mapping" と言うだけで具体的な形式的差異がない。

**必須修正**: 最低2つの先行形式化（例：institution の機械化、BX formal kernel）に対し、定義レベルで差異を示せ。

---

### M3: Lean ファイルの実在性が検証不可能
**Section 4.4、Section 9 に関連**

論文は以下を主張する：
- theorem count: 59
- sorry count: 0
- LOC: 1502
- manifest hash: `8c098d78...`

しかし、**本査読では `paper/lean/UadfU0/` 下のソースファイルが参照資料として提出されていない**。Theorem catalog（Appendix）は宣言名のリストのみであり、実際の証明本体は含まれない。

FM/ITP/CPP の artifact 評価基準において、build 再現性を「expected」と記述しながらソースを未提出なのは致命的である。

**必須修正**: Lean ソース一式（`paper/lean/UadfU0/` 全体）を artifact として添付し、査読者が `lake build` で検証できる状態にすること。

---

### M4: `UStar` の扱いが理論的に循環に近い
**Section 3.8、定理 `UStar_inter_projDomOn_subset_UAndOn` に関連**

`UStar : SpecSet α` はパラメータであり「このカーネルでは構成されない」と明示される（Section 3.8）。しかし、Section 1.1 で「ideal complete root specification U* is usually unavailable in practice」と問題設定し、Section 3.8 で「UStar は parametric input なので conditional linkage theorem に過ぎない」と後退する。

これは：
- 論文の**動機（U*の不在が問題）と貢献（U*をパラメータとする定理）が対応していない**。
- U* が与えられていれば自明に成り立つ linkage を「定理」として提示していることになりかねない。
- Section 8（Limitations）の記述「If some layer is overly permissive, U0 may become coarse」も U* との関係が不明瞭。

**必須修正**: U* 不在の状況で何が保証されるかを明確化し、U* をパラメータとする定理群の「実用上の意義」を証明または具体例で示せ。

---

### M5: RQ とのアライメントが不完全
**Section 1.3 と Section 3 の対応に関連**

論文は5つの RQ を設定し、Section 1.3 で「Primary RQs for this formal paper are RQ3, RQ4, and RQ5」と限定する。しかし：

- `RQ1`（heterogeneous carriers）の答えは "typed inverse-image definitions" と書かれるが、それが定理として述べられていない（定義に過ぎない）。
- `RQ2`（`A(i) ⊆ D(i)` の lift）の答えとして `lifted_subset_preimage_domain` と `U0_witness_projects_to_some_domain` が挙げられるが、Section 3.2 では「foundational lemmas」として「not novelty claims」と扱われている—RQ への答えが novelty でないとはどういう意図か？
- `RQ5` の答えである one-sided adequacy decomposition（Section 3.6）は、soundness/completeness を分離することの**新規性理由が論証されていない**。

**必須修正**: 各 RQ について、「定義」「補題」「定理（新規主張）」を区別し、それぞれが how it advances the state of the art かを明示せよ。

---

## 軽微懸念（Minor）

### m1: 定理名の命名規則が不統一
`U0On_monotone` と `UAndOn_antitone` は Construction.lean 由来だが、`U0_least_upper_bound_iff` は Minimality.lean 由来。トレーサビリティ表（Section 4.5）と Theorem Catalog（Appendix）の間でファイル参照が冗長。統合するか、Appendix への委譲を明示すべき。

### m2: `consistent_iff_exists_UAndOn_pair` の記述欠落
Section 3.3 で言及されるが、Assumption Matrix に未記載。定理の仮定条件（non-empty active set を必要とするか）が不明。

### m3: References の形式不統一
文献 [9]（Mossakowski et al., CEUR-WS）は publication year なし。[6] Nuseibeh et al. 1994 は doi なし。FM系 proceedings の形式基準を満たしていない。

### m4: `#print axioms` の網羅性
Section 4.3 のアキシオム監査は選抜定理のみ。特に `UStar_inter_projDomOn_subset_UAndOn` が "no axioms" とされているが、これは `propext` を暗黙に使用していないことを意味するのかどうか、Lean 4 の文脈で説明が必要。

### m5: PasswordPolicy case study（Section 5.2）の位置付けが弱い
`checkConsistent_iff_allThree` は constrained interval domain 上の sanity theorem と説明されるが、**どの主定理の instantiation になっているか**が明示されていない。Sec 5.3 の説明も「assumption-level debugging hooks」に留まり、形式的意義が不明。

---

## 採択のための必須修正

1. **M3（最優先）**: Lean ソース artifact を査読パッケージに含め、`lake build` が reviewer 側で再現できることを確認せよ。これなし では ITP/CPP では受理されない。

2. **M1**: Section 6 の "mechanization-specific value" について、既存形式化（Mathlib, abstract-interpretation 機械化、BX formal kernel）と比較した **定理レベルの技術的差異** を明示せよ。主観的な "hardness summary" を客観的な技術的論証に置き換えよ。

3. **M2**: Section 7 の各先行研究に対し、定義レベルの差異（特に institutions との関係、BX formal kernel との one-way 制限の意味）を技術的に記述せよ。

4. **M4**: `UStar` をパラメータとする定理群が、U* 不在の設定（Section 1.1 の問題設定）に対してどのような実用的・形式的価値を持つかを明確化せよ。現状は問題設定と貢献が乖離している。

5. **M5**: RQ 番号と対応する定理・定義・補題のマッピングを revision で整理し、各 RQ が「定義上の貢献」か「定理上の貢献」かを区別せよ。
