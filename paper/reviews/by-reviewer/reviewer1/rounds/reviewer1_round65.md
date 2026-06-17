I now have a thorough understanding of the entire submission. Let me write the formal review.

---

## Review

### 1) Recommendation

**Major Revision**

---

### 2) MUST (採択に必須)

**M1. 新規性の明確化と関連研究の具体的分離**

現状、manuscript §6 で "classical overlap" と "mechanization-specific value" を自己申告で列挙しているが、査読者がそれを検証するための比較が不十分。具体的に：

- Darais & Van Horn (ICFP 2016) の constructive Galois connections は Agda でメカナイズされており、partial map の adjoint 問題を扱っている。`no_left_adjoint_of_partial` が彼らの結果と何が違うか、または補完するかを theorem-level で説明せよ。
- Institution theory (Goguen/Burstall) との関係が「我々のスコープは狭い」で済まされている。「narrower」であることの formal 根拠を示せ（例：satisfaction condition の類似物が Model 内に現れないことの明示）。
- Nuseibeh et al. の ViewPoints との比較で「formal kernel」が何を追加するかが abstract 的記述に留まる。

**M2. `UStar` の意味論的地位の明確化**

`IdealRoot.lean` における `UStar` は「possibly unknown ideal root specification」として free variable 扱いされているが、これは significant な設計選択であり現状説明が不足している。

問題点：
- `UStar` が任意の `SpecSet α` として量化される場合、`UStar_subset_UAndOn` は実質「仮定 `hNecessary` が成立するなら結論が成立する」という tautology に近い。`UStar` が何を代表するかの semantic commitment がない。
- §3.8 で「Interpretation: under partial observability, ideal-root linkage requires domain-restricted assumptions」と書かれているが、`UStar` 自体が arbitrary であれば、この「linkage」はいかなる意味で `U0/UAnd` との関係を語るのか不明。
- FM 系読者は「ideal root の operational meaning は何か」を必ず問う。"possibly unknown" は motivation として了解できるが、形式的に `UStar` が free variable である以上、theorems は `UStar` の identity について何も語らない。これを limitation として明示するか、あるいは `UStar` に最低限の characterization (e.g., 存在性、uniqueness up to equivalence) を加えよ。

**M3. Contribution scope と theorem hardness の釣り合い**

59 theorems、1502 LOC の mechanization として提示されているが、主要 theorems の多くは set-theoretic identities のほぼ直接の Lean 翻訳である。

具体的に：
- `lifted_transfer`：仮定 `hproj`（同一根点でのリンク）と `hA`（許容性輸送）が与えられれば、証明は 5 行の witness extraction で終わる（実際のコード：33行でそのまま確認）。この theorem の "hardness" は仮定の明示化にあると主張されているが、仮定自体が結論を almost directly encode している。
- `preimage_compose`：`Option.bind` の case analysis という partiality-specific 作業は確かに非自明だが、これは Lean の `Option` monad 上の基本補題に近い。
- Minimality theorems (`U0_least_upper_bound_iff` 等)：これらは LUB/GLB の定義を predicates で書き換えたものそのものである。

**要求：** §6 を改訂し、各主要 theorem について「なぜこれが non-trivial か」を先行研究との比較において具体的に示せ。「assumption surfacing」が novelty であるなら、その assumption が事前文献で implicit に扱われてきたことを evidence とともに示せ。

**M4. Lean ファイルの引用一貫性**

manuscript §2.3 のコードスニペットが `Construction.lean` と一部不一致：

- manuscript は `def U0On` および `def UAndOn` を示すが、実際の `Model.lean` では `U0` と `Contradictory`/`Consistent` の定義が含まれ、`U0On`/`UAndOn` は `Construction.lean` にある。manuscript §2.3 の「(Definitions in `paper/lean/UadfU0/U0Spec/Construction.lean`.)」という注釈はあるが、コードが `namespace Model` 内で `M :` を variable として使いつつ def を示す形式は、実際のファイル構造（`variable (M : Model ι α)` が各ファイルにある）と混同される恐れがある。
- `lifted_transfer` の Lean signature 中 `M.Ui j` および `M.Ui i` が使われているが、`Ui` は `Model.lean` で `compatibility alias` と明示されている。manuscript では `Ui = A` であることを明示せよ（または `A` に統一せよ）。

---

### 3) SHOULD

**S1. RQ 評価の明示性**

§1.3 で RQ1–RQ5 が設定され §3.2 で RQ1/RQ2 への回答が述べられているが、RQ3/RQ4/RQ5（primary と明示）への回答が本文中に散在し、まとまった評価節がない。通例の FM 論文に倣い、§3 末または §4 末に "RQ Answers" 小節を設け、各 RQ に対して（a）対応する theorem/lemma 名、（b）answer の要旨、（c）limitation を 1 段落で整理せよ。

**S2. `semanticPullbackMay` の設計選択の正当化**

`semanticPullbackMay E S` は `proj i x = none ∨ ∃ y, E x y ∧ y ∈ S` と定義されており、none ブランチが E-side に反映されていない（none → True ではなく none → passthrough）。§3.6.2 で「operational comparability choice」と説明されるが、この選択が他の設計（例：none を False 扱いにした must-only 版、または none を E-inconclusive として扱う別の may 版）と比較してなぜ適切かを argue せよ。FM 読者は設計の uniqueness を問う。

**S3. 引数の型宇宙整合性**

`Model ι α` は `universe u v w` で index, root, carrier を別々の宇宙に置いている。これは型理論的には適切だが、manuscript 本文の数学記法（`β_i`, `Ω`, 等）とのマッピングが曖昧。表 1 節として「notation-to-Lean mapping」を加え、`α = Ω`、`carrier i = β_i`、`ι = I` といった対応を明示せよ。

**S4. Password policy case study の formal 意義**

`PasswordPolicy.lean` は `proj _ n := some n`（全射）を使っており、partiality の influence が消えている。このケーススタディが partial projection の mechanization の sanity として妥当であることを説明するか、または partiality を持つ case study を追加せよ。現状では「mechanization validates model instantiation consistency」と述べられるが、partial projection の特性が最も重要なこの論文で total projection のみのケーススタディは証明力が弱い。

**S5. Axiom audit の完全性**

§4.3 で主要 theorems の axiom audit を示すが、`preimage_compose` が `Classical.choice` を使う理由が説明されていない。`by_cases` タクティクの利用が原因であれば、それを明示し、`Decidable` 版の証明が可能かどうかを議論せよ（FM 系では constructivity は重要な論点）。

---

### 4) MINOR

**m1.** §0.2 Non-claims #4「No claim that PoC behavior is a direct semantic proof of all formal assumptions」—manuscript 内に PoC への言及が他にほぼなく、この non-claim の対象が不明。削除するか、対象を明示せよ。

**m2.** §2.7 の Pairwise consistency で `Consistent(i,j)` と `Contradictory(i,j)` の定義が示されるが、`Contradictory ↔ ¬ Consistent` は `Consistency.lean` theorem `contradictory_iff_not_consistent` として証明済みである一方、manuscript 本文でその証明への言及が脚注レベルに過ぎない。この duality の formal 意義（例：operational use case での「矛盾検出 → 整合性失敗の証明」への応用）を 2-3 文追加せよ。

**m3.** `theorem_catalog.md` の theorem count (59) と `manuscript §4.4` の theorem count (59) は一致しているが、catalog 中の `TwoLayer.lean` ファイルが catalog に item なし（glob では存在する）。このファイルの内容と catalog への不掲載の理由を確認・説明せよ。

**m4.** §9 Reproducibility で `lake-manifest.json` の hash が示されるが、Lean/Mathlib のバージョン固定（`leanprover/lean4:v4.27.0`）と mathlib4 の commit/tag の両方を manifest から抽出して明示的に記載せよ。現状は `manifest hash` のみで読者が再現性を独立検証するには不十分。

**m5.** `no_left_adjoint_of_partial` の proof で `simp [hnone] at hproj'` が最終ステップとなっている。これは `Option.noConfusion` 的 simplification だが、実際に使われる simp lemma を明示するか、`exact absurd hproj' (by simp [hnone])` のような形で読みやすくすることを検討せよ（論文上の proof sketch として）。

**m6.** References に de Moura et al. (CADE 2015) が Lean 4 の citation として使われているが、Lean 4 自体の公式参考文献は `moura2021lean4` (2021) またはそれに相当するものであり、CADE 2015 は Lean 3 の論文。修正せよ。

---

### 5) Acceptance Readiness (3行)

本論文は Lean4 でのメカナイズされた partial projection kernel という方向性自体は FM 系査読者に受け入れ可能な射程を持ち、sorry-free 59 theorem の mechanization は artifact の信頼性の基盤になり得る。しかし現状では `UStar` の意味論的地位の曖昧さ、主要 theorem の novelty の対先行研究比較不足、および total-projection のみのケーススタディという三点が FM 採択水準に対して不足しており Major Revision が適切である。上記 M1–M4 が誠実に対処されれば採択可能な道筋は存在する。
