I'll perform a mechanization review of this paper according to the specified criteria.

---

**VERDICT: NG**

**MAJOR:**

1. **本文主張とLean定理対応の追跡可能性（RQ1-RQ5）に部分的欠損**
   - 対応表（§7.6）は主要定理を列挙しているが、RQ2の中核主張「`A(i) ⊆ D(i)` を root 側の証人妥当性に持ち上げられるか」に対応する定理として `lifted_subset_preimage_domain`, `U0_witness_projects_to_some_domain` が挙げられている。しかし、これらは `A ⊆ D` の前提を使って `lifted ⊆ preimage D` を示すだけであり、「持ち上げ」（逆方向の構成）を証明していない。RQ2が問う「root側証人の妥当性への持ち上げ可能性」に対し、この方向の定理が mechanization に含まれているかが本文から追跡不能。
   - RQ3「join側（`U0`）と meet側（`U∧`）を同一モデル上で整合的に定義できるか」に対し、§7.6は §3 と §4.5 を挙げているが、「整合的に定義」の意味（両演算の well-definedness、または相互関係の形式的性質）を示す定理名が明示されていない。`UAndOn_subset_U0On_of_nonempty_active` などが該当すると推測されるが、追跡が曖昧。

2. **理論（RQ5）と PoC（RQ6）の境界が不明瞭**
   - §6.2 で「本節は RQ6 を対象とし、RQ5 の adequacy 定理（§4.3）を本デモへ直接適用したとは主張しない」と明記しているが、一方で §4.3 の adequacy 定理群（`preimage_subset_semanticPullback_of_sound` 等）は「抽象関係 `E` に対する一般結果」と述べている。しかし、実 regex 抽出器が `E` のどのインスタンスに対応するかの mechanization が存在しないため、RQ5 の理論的主張と RQ6 の実装デモの間に形式的な接続がない。mechanization paper として、この接続の欠如は major issue。

3. **付録Aのコード掲載が不完全**
   - §11 で「中核実装全文」として `Model.lean`, `Construction.lean`, `IdealRoot.lean` の3ファイルを掲載しているが、`IdealRoot.lean` が途中で切れている（"`M.`" で終わっている）。mechanization の完全性検証に必要な `UStar_inter_projDomOn_subset_UAndOn` 以降の証明本体が欠落。
   - RQ4 の中核定理（§4.1 `lifted_transfer`, §4.2 `preimage_compose`）に対応する `Transfer.lean`, `Composition.lean` が付録に含まれていない。

**MINOR:**

1. **Lean build 再現手順の具体性不足**
   - §7.1 で `cd paper/lean; lake build` を示しているが、`lean-toolchain` の内容（`leanprover/lean4:v4.27.0`）と `lakefile.lean` の記述が本文に含まれていない。付録で掲載すべき。
   - `lake-manifest.json` の SHA256 ハッシュ値が記載されていないため、同一バイナリでの再現性が検証不能。

2. **本文-Lean 記法対応の一貫性**
   - §2.1 の記法表で `D_i` → `D i : SpecSet (carrier i)` と記載しているが、`Model.lean` の実装では `D` は `layer` を経由して定義されている（`def D (M : Model ι α) (i : ι) : SpecSet (M.carrier i) := (M.layer i).D`）。この階層構造が記法表に反映されていない。
   - `Ui` が `A` の alias として定義されている理由が本文で説明されていない（§2.1 の表には `Ui` が登場しない）。

3. **定理カウント（59件）の内訳検証不能**
   - §7.4 で「`theorem` 宣言数 59」と報告しているが、これが本文 RQ との対応表（§7.6）の定理数と一致するかが検証できない。対応表には12行しかなく、各行が複数定理を含む場合もあるため、59件の分布が追跡不能。
   - `rg -n '^theorem ' paper/lean/UadfU0 | wc -l` の実行結果（生ログまたはファイルリスト）を補足資料として提供すべき。

**REQUIRED_CHANGES:**

1. RQ2 の「持ち上げ」方向の定理を mechanization に追加するか、RQ2 の文言を「順方向包含のみを証明」と修正する。
2. 付録A に `Transfer.lean`, `Composition.lean`, `Adequacy.lean` の完全掲載を追加（特に §4.1, §4.2, §4.3 の中核定理）。
3. `IdealRoot.lean` の切れた部分を復元し、`UStar_inter_projDomOn_subset_UAndOn` の証明本体を含める。
4. RQ5 の adequacy 定理と RQ6 の regex 抽出器の形式的接続を明示するか、両者が未接続であることを limitation として §9 に明記する（現在は §6.2 の注記に分散しており、読者が見落としうる）。
5. `lakefile.lean`, `lean-toolchain` の内容を付録に掲載し、`lake-manifest.json` の SHA256 を記載する。

**RISK:**

本稿の中核主張（RQ1-RQ5 の定式化と証明）と実装（PoC）の間に形式的な gap があり、mechanization paper として要求される「本文主張 → Lean定理 → 実行可能コード」の一貫した追跡可能性を満たしていない。特に RQ5/RQ6 境界の曖昧さは、査読者が「理論的主張が実装で検証されていない」と判断する major risk である。付録の不完全性（途中で切れた証明）も、再現性評価を阻害する。
