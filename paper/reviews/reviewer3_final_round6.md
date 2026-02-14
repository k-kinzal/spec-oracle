Verdict: NG

---

## 致命的不整合点（3点）

### 1. RQ5/RQ6 の定義と本文参照の不一致
- **本文（§1, RQ5/RQ6）**:
  - `RQ5 (theory)`: 抽象抽出関係 `E` に対し、抽出適合を sound/complete に分解できるか
  - `RQ6 (practice)`: 実OSS抽出パイプラインの**技術的再実行可能性**を確保できるか

- **本文（§4.3 抽出適合の one-sided 分解）**:
  - "RQ5 (theory): §4.3（sound-only / complete-only / equality）で抽象関係 `E` に対する分解を定式化して解決"
  - "RQ6 (practice): §6.2, §7.5 で source-lock 付き抽出パイプラインの技術的再実行可能性を確認して解決"

- **Lean参照（`InterLayer/Adequacy.lean`）**:
  - `preimage_subset_semanticPullback_of_sound` は RQ5 に対応
  - `semanticPullback_subset_preimage_of_complete` は RQ5 に対応
  - `preimage_eq_semanticPullback` は RQ5 に対応

- **矛盾**:  
  §4.3 の本文記述では「抽出適合の one-sided 分解」が RQ5 を解決し、「実抽出器への適用には抽出層の意味保存証明が別途必要（限界 §9）」と述べている。一方で §6.2/§7.5 は RQ6（技術的再実行可能性）を扱う。しかし本文中で `Adequacy.lean` が RQ6 の証明に直接関与する記述がない。RQ5 は theory（抽象関係）、RQ6 は practice（実装再現）として分離したはずだが、本文とLean参照の対応が明示されていない。

### 2. 型不整合: `lifted_subset_preimage_domain` の依存関係
- **本文（§2.2）**:  
  "`D(i)` を分離する理由: ... `A(i) ⊆ D(i)` を明示することで、root 側証人が `carrier i` のうち domain 述語 `D(i)` を満たすこと（RQ2）を定理として追跡できる"

- **本文（§10 結論）**:  
  "`RQ2`: §4.6 背景補題群（`lifted_subset_preimage_domain`, `U0_witness_projects_to_some_domain`）で解決"

- **Lean（`U0Spec/Construction.lean`）**:
  ```lean
  theorem lifted_subset_preimage_domain (i : ι) :
      M.lifted i ⊆ M.preimage i (M.D i) := by
    have hAD : M.Ui i ⊆ M.D i := (M.layer i).admissible_subset_domain
    exact M.preimage_monotone i hAD
  ```

- **矛盾**:  
  本文は `lifted_subset_preimage_domain` を「背景補題（§4.6）」に分類しているが、Lean実装では `U0Spec/Construction.lean` に配置されている。§4.6 は "基礎補題（背景）" として `preimage_monotone` / `preimage_union` / `U0_least_upper_bound_iff` などを列挙しているが、`lifted_subset_preimage_domain` は **中核定理構成ファイル** に含まれる。本文の「RQ2 解決 = §4.6 背景補題」という主張と、Lean配置（`Construction.lean`）の間に分類矛盾がある。

### 3. 定義未展開: `Contradictory` の型署名欠落
- **本文（§3.3 join と meet の接続）**:
  ```
  Contradictory(i,j) :⇔ ∀x, x∈lifted(i) → x∈lifted(j) → False
  ```

- **Lean（`InterLayer/Consistency.lean` 該当箇所なし）**:
  - 本文で定義した `Contradictory(i,j)` に対応する Lean定義が存在しない。
  - `consistent_iff_exists_UAndOn_pair` は `Consistent` の特性化だが、`Contradictory` の型署名・定義・定理はLeanに現れない。
  - 本文 §3.3 で "双対: `contradictory_iff_not_consistent`" を背景補題として扱う記述があるが、該当定理がLeanに存在しない。

- **矛盾**:  
  本文が形式定義として提示した `Contradictory` が、Lean実装に反映されていない。本文 §4.6 に "`contradictory_iff_not_consistent`（双対）" を背景補題として列挙しているが、該当定理がLeanに存在しない。

---

## 最小修正案

### 修正1: RQ5/RQ6 の分離を本文と Lean参照で統一
- **修正箇所**: §4.3 末尾、§10 結論（RQ対応）
- **修正内容**:
  - §4.3 末尾に以下を追加:  
    > "定理 `preimage_subset_semanticPullback_of_sound` / `semanticPullback_subset_preimage_of_complete` / `preimage_eq_semanticPullback` は抽象関係 `E` に対する RQ5 の解である。RQ6（実抽出パイプライン再実行性）は §6.2/§7.5 の source-lock 付き実行手順で解決するが、`Adequacy.lean` は RQ6 の証明対象ではない（抽出器の意味保存は別課題）。"
  - §10 結論の RQ5 記述を以下に差し替え:  
    > "`RQ5 (theory)`: §4.3（`preimage_subset_semanticPullback_of_sound`, `semanticPullback_subset_preimage_of_complete`, `preimage_eq_semanticPullback`）で抽象関係 `E` に対する分解を定式化して解決。実抽出器への適用には抽出層の意味保存証明が別途必要（限界 §9）。  
    > `RQ6 (practice)`: §6.2, §7.5 で source-lock 付き抽出パイプラインの技術的再実行可能性を確認して解決。抽出正当性（soundness/completeness）は RQ6 の対象外であり、限界 §9 に記載。"

### 修正2: `lifted_subset_preimage_domain` の分類を統一
- **修正箇所**: §10 結論（RQ2 対応）、§4.6 背景補題
- **修正内容**:
  - §10 結論の RQ2 記述を以下に差し替え:  
    > "`RQ2`: §2.2 の `A(i) ⊆ D(i)` 明示、および `paper/lean/UadfU0/U0Spec/Construction.lean` の `lifted_subset_preimage_domain` / `U0_witness_projects_to_some_domain` で解決。"
  - §4.6 背景補題のリストから `lifted_subset_preimage_domain` / `U0_witness_projects_to_some_domain` を削除（これらは中核構成定理）。

### 修正3: `Contradictory` 定義を Lean に追加または本文から削除
- **選択肢A（Lean追加）**:
  - `paper/lean/UadfU0/InterLayer/Consistency.lean` に以下を追加:
    ```lean
    def Contradictory (M : Model ι α) (i j : ι) : Prop :=
      ∀ x : α, x ∈ M.lifted i → x ∈ M.lifted j → False
    
    theorem contradictory_iff_not_consistent (i j : ι) :
        M.Contradictory i j ↔ ¬ M.Consistent i j := by
      constructor
      · intro hContr hCons
        rcases hCons with ⟨x, hxi, hxj⟩
        exact hContr x hxi hxj
      · intro hNotCons x hxi hxj
        exact hNotCons ⟨x, hxi, hxj⟩
    ```

- **選択肢B（本文削除）**:
  - §3.3 の `Contradictory(i,j)` 定義式を削除し、以下に差し替え:  
    > "矛盾は `¬Consistent(i,j)` として定義する（Lean実装では `Contradictory` 述語を導入していない）。"
  - §4.6 背景補題リストから `contradictory_iff_not_consistent` を削除。

**推奨**: 選択肢A（Lean追加）。本文が提示した形式定義を Lean で機械検証することが本稿の目的に整合する。
