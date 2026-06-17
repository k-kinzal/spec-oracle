## 総合判定

**Major Revision**

---

## 主要懸念

### 1. 数学的新規性の位置づけが不明確 (Reject リスク)

§6「What Mechanization Added Beyond Textbook Identities」および§6.1で新規性の境界を示しているが、**実質的な数学的新規性がない**という点を自ら認めている。

- §6.1: "we do not claim these mathematical identities are new"
- 主張しているのは「assumption-audited kernel as one package」

FM/ITP/CPP等のトップ会議は、「既知の数学をLean4で形式化しただけ」に対して査読が厳しい。特に：
- `preimage_monotone`, `preimage_union`: 標準的な逆像の性質
- LUB/GLB characterization: ポセットの基本的事実
- `contradictory_iff_not_consistent`: 定義の展開に過ぎない

**新規性の核心として主張できるのは**「partial `Option` + heterogeneous carriers + assumption-audited packaging」の組み合わせだが、これがFMコミュニティにとって十分な貢献かの論証が弱い。§7の関連研究との差分が「narrower scope」「we do not claim...」という否定的説明に終始している。

### 2. 定理の自明性 (Major)

いくつかの「core theorems」が定義の直接展開に過ぎない：

**`lifted_transfer` (Transfer.lean)**:
```lean
intro x hxj
rcases hxj with ⟨yj, hproj_j, hyjA⟩
rcases hproj x yj hproj_j with ⟨yi, hproj_i, hR⟩
exact ⟨yi, hproj_i, hA yi yj hR hyjA⟩
```
証明は仮定をそのまま繋いだだけであり、仮定 `hproj`・`hA` の内容が定理の内容そのものである。§6が「same-root witness linkage is required and mechanized explicitly」と言うが、これは仮定を定理の引数として与えた場合の自明な帰結である。

**`UStar_inter_projDomOn_subset_UAndOn`**: 同様に仮定の展開のみ。

**`UAndOn_empty_eq_univ`**: `False.elim` で即座に閉じる自明なケース。

### 3. `Classical.choice` の使用と構成性の曖昧な扱い (Major)

§4.3で：
- `lifted_transfer`: no axioms
- `preimage_compose`: `[propext, Classical.choice, Quot.sound]`

「this paper does not claim constructivity-preserving normalization」と断っているが、ITP/CPP系会議では構成性の境界は明示的に論じる必要がある。`Classical.choice` を使う理由が「witness reconstruction through extensional equality」と説明されているが、なぜ構成的に書けないかの分析がない。

### 4. §3.6 adequacy theorems の循環性 (Major)

`preimage_eq_semanticPullback` (Adequacy.lean) の証明:
```lean
hEq : ∀ x y, M.proj i x = some y ↔ E x y
```
という仮定の下で `preimage i S = semanticPullback E S` を証明しているが、`E x y ↔ proj i x = some y` が成立するなら `semanticPullback E S` の定義から直ちに `preimage i S` と等しくなる。これは実質的に同義反復である。

§3.6.1の「concrete extractor proof obligations (template)」はテンプレートに過ぎず、**具体的な抽出器の正しさを一切証明していない**。Non-claimとして明示されているが、そうであればこの定理群の意義が疑われる。

### 5. `no_left_adjoint_of_partial` の証明の問題 (Minor→Major)

§3.7の証明スケッチ：
> 3. From left side (`F S ⊆ T` trivial), derive right side `S ⊆ preimage_i(T)`

`T = sUniv` は全集合なので `F S ⊆ T` は自明。しかしこれは adjunction の左辺を trivial に成立させているだけで、adjunction の本質的な構造を使っていない。具体的には：
- 任意の左随伴 `F` に対して `F S ⊆ ⊤` は常に成立する
- この instantiation は adjunction の実質的な使用ではなく、特殊ケースでの矛盾導出

この証明構造では「partial projection → no left adjoint」の本質的な理由が不明確になっている。全域写像でも `F S ⊆ ⊤` は成立するため、矛盾は `proj i x0 = none` から直接来ているのであり、adjunction 全体の構造から来ているわけではない。

### 6. Related Work の不十分さ (Major)

§7で参照している先行研究との差分説明が全て否定的（「we do not...」）。

特に：
- **Isabelle/HOL, Coq での集合論的逆像の既存の形式化**との比較がない
- **Option モナドを使った部分写像の Lean4 形式化**（Mathlib の `PartialEquiv`, `Option` 関連定理群）との差分がない
- §7.5「Galois-connection mechanization lines」で引用している Darais-Van Horn 2016 との具体的な差分が「partiality-specific boundary theorem」とのみ述べられているが、それが先行研究に存在しない理由の説明がない

---

## 軽微懸念

### 7. 定義の冗長性

`Model.lean` の `Ui` は `A` の alias であり（§2.2で明示）、これが存在する理由が「compatibility alias」とのみ説明されているが、何との互換性かが不明確。

### 8. PasswordPolicy case study の限定的意義

`PasswordPolicy.lean` の `checkConsistent_iff_allThree` は3層の整数区間の整合性チェックに過ぎない。§5.3で「not used to claim broad engineering effectiveness」と認めており、formal paper の事例としては薄い。

### 9. theorem 数の計上の問題

Theorem catalog: 59件と主張しているが、`Definitions/Model.lean` の `subset_refl`, `subset_trans`, `set_ext` はユーティリティ補題であり、これをコアの定理数に含めることで実際の密度が希釈されている。

### 10. §2.3 の Lean excerpt の問題

原稿掲載の excerpt には `UAnd` の定義が欠けているが（`UAndOn` はあるが `UAnd` の global form がない）、実際の `Construction.lean` には `UAnd` が定義されている。原稿の excerpt と実際のコードの乖離。

---

## 必須修正

| 優先度 | 箇所 | 修正内容 |
|---|---|---|
| **高** | §1.3, §6, §7 | FM会議基準での新規性を正面から述べる節を設ける。「既存ライブラリにない理由」を具体的に示すこと（Mathlib の `Option`/`PartialEquiv` との差分を示すなど） |
| **高** | §3.4, §3.6, §3.8 | 各定理が自明でない理由を proof-level で示すか、自明な定理は「infrastructure」として格下げして主張を絞る |
| **高** | §3.7 (`no_left_adjoint_of_partial`) | 証明の本質的な構造（なぜ partiality が adjunction を壊すか）を明示的に論じる |
| **高** | §7 | Lean4/Mathlib における既存の Option/partial map 形式化との差分を具体的に記述する |
| **中** | §4.3 | `Classical.choice` の使用について、constructive alternative が存在するか否か、存在しない理由を説明する |
| **中** | §3.6.1 | adequacy theorems が「同義反復」にならない使用シナリオ（`E` が `proj` と異なる場合）を具体例で示す |
| **低** | §2.3 | manuscript の Lean excerpt を実際のコードと同期させる（`UAnd` 定義の追加など） |
