Verdict: OK

### 根拠 (3点)

1. **型整合・定義対応が完備**  
   本文 §2.2 の逆像定義 `f^{-1}_{0i}(S) := {x∈Ω | ∃y∈β_i, proj_i(x)=some(y) ∧ y∈S}` が `paper/lean/UadfU0/Definitions/Model.lean:preimage` の `fun x => ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ S` と完全一致。  
   `U0` の join定義（§3.1）と `UAnd` の meet定義（§3.2）はそれぞれ `U0Spec/Construction.lean` の `U0` / `UAndOn` に対応し、記法表（§2.1）の数学記法⇔Lean名の双方向マッピングが整合している。

2. **中核定理群の参照が追跡可能**  
   §4 の主結果は全て対応Leanファイルへの明示的参照を持つ。  
   - §4.1 `lifted_transfer` → `InterLayer/Transfer.lean`  
   - §4.2 `preimage_compose` → `InterLayer/Composition.lean`  
   - §4.3 one-sided adequacy → `InterLayer/Adequacy.lean` (sound / complete / equality の3定理)  
   - §4.4 `no_left_adjoint_of_partial` → `RelatedWork/Galois.lean`  
   - §4.5 GLB三定理群 → `U0Spec/Minimality.lean`  
   
   各主結果が定理名・ファイルパス・行番号パターン (`file_path:line_number`) で機械検証コードと一対一対応し、第三者が追試可能。

3. **RQ5 (theory) と RQ6 (practice) の分離が明示的**  
   - RQ5 (theory): §4.3で抽象関係 `E` に対する sound/complete/equality の3段階分解を定式化。ただし「実抽出器への適用には抽出層の意味保存証明が別途必要」と限界§9に明記。  
   - RQ6 (practice): §6.2で source-lock 付き抽出パイプラインの**技術的再実行可能性**を確認。「抽出正当性（soundness/completeness）はRQ6の対象外」と§6.3で明示分離。  
   
   この分離により、理論定理（RQ5）を実抽出デモ（RQ6）に誤適用する混線を防いでいる。

---

### Minor notes (編集軽微の改善余地)

1. **層間伝播定理（§4.1）の必要条件未証明**  
   本文で「十分条件を与えるが、必要条件は未証明」と限界§9.7に記載済み。今後、「`hproj` / `hA` が成立しない反例ケースで `lifted(j) ⊆ lifted(i)` が破綻する」ことを示す補題を追加すれば、両方向の特徴付けが得られる（optional）。

2. **抽出デモの convenience sample 宣言の位置**  
   §6.2 の `n=3` が convenience sample である説明は現在3箇所（冒頭重要文、選定理由段落、§6.3何が分かったか）に分散。consolidate して冒頭に一度だけ明示し、以降は「前述の通り」で参照する形にすると、読者が反復強調を「弁解」と誤読するリスクを減らせる（stylistic）。

3. **定理番号付与の有無**  
   §4 の中核定理群は現在サブセクション番号（§4.1, §4.2, ...）で識別している。将来的に定理参照の一意性を高めるなら、例えば「Theorem 4.1 (`lifted_transfer`)」のように定理番号を明示してもよい（optional, 現状でも追跡可能）。

---

以上、blocking問題なし。理論定理参照の完全性、RQ対応の明示的分離、再現性保証（Lean build + source-lock 追試手順）により、形式検証・証明整合性の観点から受理可能。
