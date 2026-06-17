## 総合判定

**Major Revision（条件付き採録候補）**
FM/ITP/CPP レベルへの投稿は現時点では困難。FASE/Formal Aspects レベルなら Major Revision で条件付き採録の可能性あり。

---

## 主要懸念

### 懸念1：新規性の位置づけが不明確（最重大）

§6.1 で「Mathematical identities は新規ではない」と自己申告しているが、**ではパッケージとしての貢献が何故 FM/ITP 水準の論文たりうるのか**の議論が不足している。

- `preimage_compose`（§3.5）は `Option.bind` のモナド則 + set extensionality の直接適用であり、impossible branch elimination は Lean4 で機械的に処理される範囲に収まる。これをどの意味で "non-trivial" と呼ぶかの正当化が弱い。
- `no_left_adjoint_of_partial`（§3.7、`paper/lean/UadfU0/RelatedWork/Galois.lean`）は Galois 接続の基本的な反例構成であり、「guardrail として位置づける」という説明は査読者を納得させるのに十分でない。
- 論文 §6 の "per-theorem hardness summary" は informal な主張であり、形式的な分離（どの補題が無くなると証明が通らないか）が theorem-level で示されていない。

**必要な対処**：各定理について「標準ライブラリの組み合わせだけでは書けない理由」を定理レベルで明示するか、貢献を "mechanized engineering kernel" に明示的に格下げして適切なベニューに絞る。

---

### 懸念2：定義整合性の問題

**§2.5 と §2.3 の `U0` 配置矛盾**

§2.5 の "Definition-placement note" に：
> `U0` is placed in `Definitions/Model.lean` as core root-side union operator

とあるが、`UAndOn`/`UAndMayOn`/`U0On` は `U0Spec/Construction.lean` に定義されている（同ファイル確認）。`U0` 自体は `Definitions/Model.lean`（確認済み）に存在するが、`U0_eq_U0On_all` は `Construction.lean` に存在する。この分割の根拠と一貫性が原稿から読み取れない。

**§2.2 の `Ui` エイリアス問題**

```
Ui(i) := A(i)  (compatibility alias)
```

`Ui` と `A` が同義であることを "compatibility alias" と呼んでいるが、なぜ両方が必要なのかが説明されていない。読者には冗長な定義に見える。

**§3.6 の `semanticPullback` の `i` の暗黙性**

`Adequacy.lean:30` で `{i : ι}` は implicit だが、§3.6 の数式記法では添字が混在しており、`E : α → M.carrier i → Prop` の `i` が数式中でどう束縛されているか不明瞭。

---

### 懸念3：定理非自明性の機械的検証が不完全

**`lifted_transfer` の "no axioms" 主張**（§4.3）

```
lifted_transfer: no axioms
```

Lean4 の `#print axioms` では推移的依存を追うが、`Transfer.lean` は `Consistency.lean` を import し、`Consistency.lean` は `Minimality.lean` を import している。`Minimality.lean` に `propext` 依存が実際にないことの確認が必要。原稿提出時に `#print axioms UadfU0.Model.lifted_transfer` の出力を appendix に含めるべき。

**`UAndOn_empty_eq_univ` の意味的重要性**（§3.3）

「vacuous-truth edge case」として扱っているが、この定理は実質的に `∀ i, False → P i` の trivial な展開である。これを独立した theorem として提示することの価値の説明が必要。

---

### 懸念4：Artifact 再現性の問題

**`lake-manifest.json` が空パッケージ**

```json
{"packages": [], ...}
```

Mathlib 等の外部依存がゼロであることを意味するが、これは本当に標準ライブラリ（`Init`/`Std`）のみで完結しているということか？`lean-toolchain` に `v4.27.0` が指定されているが、Lean4 の `v4.27.0` は現時点（2026-02）では存在しないバージョン番号であり、**再現性検証が不可能**。

- 実際の toolchain バージョンとビルド成功の証拠（CI ログ等）を appendix に含めることが必須。
- FM/ITP/CPP ではアーティファクト評価（AEC）が必須またはオプションで存在する。空 manifest でのビルド手順が明確でない。

**theorem count の一致検証**

`theorem_catalog.md` の合計：
- ファイル別カウントの合計 = 4+3+1+4+1+1+2+4+1+0+6+2+3+2+1+19+6+7 = **67** ✓

件数は一致するが、原稿 §4.4 の `rg -n '^theorem '` コマンドが `example` や `def` 内の `theorem` を拾わないか確認が必要（`TwoLayer.lean` の "0 theorems" は `example` のみという注記があり矛盾なし）。

---

### 懸念5：RQ5 の境界設定と論文全体の coherence

§0.3 で：
> `RQ5` is a theorem-level decomposition over abstract relation `E`. Concrete extractor correctness remains outside claim boundary.

としているが、§5.4 の adequacy counterexample は「E ≠ proj の場合に一方向のみ成立する」例であり、これが RQ5 の "answer" としてどう機能するのかが不明確。RQ5 への回答は「分解できる」ということだが、「何が分解できることで嬉しいのか」の motivating example が concrete extractor なしでは弱い。

---

## 軽微懸念

1. **§7（Related Work）が薄い**：各 7.x 節が 2-3 行程度。FM 採録水準では Cousot らの抽象解釈との差分、BX 文献（Diskin, Stevens et al.）との差分がより詳細に議論される必要がある。

2. **§2.8 の `Ω_trace`/`Ω_art` 区別**：本文で導入されているが Lean コードに対応する型定義がなく、bridge template の位置づけが曖昧。

3. **PasswordPolicy case study**（`CaseStudy/PasswordPolicy.lean`）の `checkConsistent_iff_allThree` は interval arithmetic の decidability の直接適用であり、これを "mechanized sanity theorem" 以上に位置づけるのは過大評価。

4. **参考文献の形式**：de Moura & Ullrich [10] は CADE 2021 だが、Lean 4 の正式参照は *Lean 4: A Small-Step Formalization* または IJCAR 2024 論文が適切。

5. **§4.2 の "proof-structure discipline"** はスタイル記述であり FM 論文の技術的 contribution に含めるべきではない（節として独立させる価値が低い）。

---

## 必須修正

| 優先度 | 対象箇所 | 必要な修正 |
|---|---|---|
| **P1** | §4.3, Appendix | `lean-toolchain` の実在バージョン確認、`#print axioms` 出力の全定理分を appendix 収録 |
| **P1** | §6, §1.2 | 各主定理が「標準ライブラリの機械的適用では書けない理由」を定理レベルで明示、または貢献範囲を "mechanized kernel survey" に格下げして FASE/Formal Aspects 向けに投稿先変更 |
| **P1** | §9 | `lake build` 再現手順のCI証拠（または AEC 用 Docker/Nix 環境）提供。`v4.27.0` の実在確認 |
| **P2** | §2.5, §2.3 | `U0`/`U0On`/`UAndOn` の定義ファイル配置の根拠を明示（設計判断として §2 に 1-2 段落追加） |
| **P2** | §3.7 | `no_left_adjoint_of_partial` が単なる反例構成以上である理由、あるいは "guardrail theorem" という位置づけの査読者向け説明を強化 |
| **P3** | §7 | Related work を各 7.x 節で最低 5-8 行に拡充（BX/TGG、institution framework との technical delta を定義レベルで） |
| **P3** | §3.3 | `UAndOn_empty_eq_univ` を独立定理として提示する動機を明示（それとも supporting lemma に格下げ） |
