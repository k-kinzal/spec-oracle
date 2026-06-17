Verdict: NG

## 致命点

### 1. 層間伝播定理の証明記述の欠落（定理4.1）
本文 §4.1 は次の定理を主張している：

> `R : β_i → β_j → Prop` とし、次を仮定する。
> 1. `∀ x yj, proj_j x = some yj → ∃ yi, proj_i x = some yi ∧ R yi yj`
> 2. `∀ yi yj, R yi yj → yj∈A(j) → yi∈A(i)`
> このとき `lifted(j) ⊆ lifted(i)`。

本文は Lean 実装を `lifted_transfer in paper/lean/UadfU0/InterLayer/Transfer.lean` と指示している。しかし査読対象ファイルに `Transfer.lean` が含まれていない。

**影響**：中核定理の検証可能性が失われる。

---

### 2. 層間合成定理の証明記述の欠落（定理4.2）
本文 §4.2 は次の定理を主張している：

> `g : β_i → Option β_j` に対して  
> `proj_j = bind(proj_i, g)` なら  
> `f^{-1}_{0j}(S)=f^{-1}_{0i}(pullbackVia_g(S)).`

本文は Lean 実装を `preimage_compose in paper/lean/UadfU0/InterLayer/Composition.lean` と指示している。しかし査読対象ファイルに `Composition.lean` が含まれていない。

**影響**：層間合成則の検証可能性が失われる。

---

### 3. 随伴不成立定理の証明記述の欠落（定理4.4）
本文 §4.4 は次の定理を主張している：

> `∃x0, proj_i(x0)=none` なら、`preimage_i` は冪集合上の左随伴を持たない。

本文は Lean 実装を `no_left_adjoint_of_partial in paper/lean/UadfU0/RelatedWork/Galois.lean` と指示している。しかし査読対象ファイルに `Galois.lean` が含まれていない。

**影響**：部分性下での随伴破綻という「暗黙仮定の否定」を謳う中核主張の検証可能性が失われる。

---

## 最小修正案

1. 査読対象ファイルに `Transfer.lean`, `Composition.lean`, `Galois.lean` を追加する。
2. または、それらのファイルが未実装/未完の場合、本文 §4.1, §4.2, §4.4 の該当定理を「今後の課題」または「検証中」に格下げし、本稿の主結果を `Construction.lean`, `Minimality.lean`, `Adequacy.lean` 内の証明済み定理のみに限定する。
3. 再現可能性保証（§7）で「中核定理12」と断言している内訳に、欠落3定理を含むか否かを明確化する。
