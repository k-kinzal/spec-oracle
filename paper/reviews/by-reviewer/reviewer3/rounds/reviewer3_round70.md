## 総合判定

**条件付き採択可能（Major Revision 相当）**

FM/FASE/CPP 基準において本稿は机上の形式的寄与として一定の完成度を持つが、以下に述べる主要懸念が未解決のまま投稿された場合、査読者が "form over substance" と判定するリスクが高い。

---

## 主要懸念

### 1. 寄与の新規性主張が防御的すぎる（採択阻害リスク：高）

§6 および §7 の随所で「classical overlap (not novelty claims)」と断りを入れている。これ自体は誠実だが、**何が本稿固有の定理レベルの新規性なのかが読者に伝わらない**。

- `lifted_transfer`・`preimage_compose` は逆像の古典的な補題とどう違うのか、**1段落の明示的な hardness argument**（"without partiality this collapses to X, which is trivial"）が §3 本文に必要。
- §6.1 "Concrete delta" の表は箇条書きにとどまり、定理として非自明な部分の証明スケッチが欠ける。

CPP/FM は mechanization per se を寄与として認めるが、「型付き partical projection に特化した仮定監査済みカーネル」が先行ライブラリ（Mathlib の `Set.preimage`、`GaloisConnection` 等）と比較して何を追加するかの **命題レベルの差分** が明示されていない。

### 2. `semanticPullback` / `E` の役割が未動機（誤読リスク：高）

§3.6 で抽象関係 `E` を導入する動機として「proj を具体的な抽出器に先立てる」とあるが、

- `E ≠ proj` が有意なのは extractor が証明義務を果たせない場合のみであり、本稿はその extractor 証明を non-claim としている。
- 結果として `semanticPullback` 定理群は **本稿の claim 境界内では使用されない抽象インターフェース** に見える。
- 査読者は「`preimage_eq_semanticPullback` が `E := proj_equality_rel` を代入すれば trivial ではないか」と問う可能性が高い。AdequacyCounterexample が非自明性を示しているが、その counterexample が **なぜ E-abstraction を justify するのか**の議論が §3.6 本文で不足している。

### 3. `no_left_adjoint_of_partial` の位置付けが曖昧（採択阻害リスク：中）

§3.7 では「guardrail theorem、standalone novelty ではない」と明記しているが、論文の theorem family の一つとして §5 traceability table に並列列挙されている。**guardrail としての使用例**（どの推論ステップを防ぐのか）が具体的に示されていないと、査読者は「既知の事実の mechanization に過ぎない」と処理する。

### 4. 関連研究の差分記述が一方向（採択阻害リスク：中）

§7 の各節は「本稿は X ではない」という否定形で差分を述べており、**「本稿だからこそ言える命題」が提示されない**。

例えば §7.5（Galois connection mechanization 線）では Darais & Van Horn (ICFP 2016) との具体的な定義レベルの差分（constructive vs. classical、total vs. partial）を 1 つの比較表で示すべき。

### 5. `lake-manifest.json` の依存パッケージ空（誤読リスク：中）

```json
"packages": []
```

Mathlib を一切使わず自前実装していることは §2.3 の `SpecSet` 定義から読み取れるが、**なぜ Mathlib を使用しないのかの設計判断**が本文に説明されていない。FM 査読者は「Mathlib の `Set` との整合性がないため再利用性が低い」と指摘する可能性がある。

---

## 軽微懸念

1. **§4.3 axiom audit の説明が不完全**: `preimage_compose` に `Classical.choice` が入る理由として「extensional equality over existential branches」と述べているが、constructive rewrite が可能とも述べており矛盾に見える。「可能だが本稿では採用しない」であれば、その設計選択の理由（proof simplicity vs. constructivity tradeoff）を 1 文で明示するべき。

2. **§5.2 PasswordPolicy の `req_projection_adequacy`**: `reqExtractRel r a c` は実質的に等号関係であり、`preimage_eq_semanticPullback` の trivial instantiation になっている。case study の non-triviality に疑問が生じる。

3. **§2.8 root space instantiation template**: `Ω_trace` と `Ω_art` の区別が以降の定理群で一切使われておらず、この節が floating になっている。削除または §3 定理の具体例に接続するべき。

4. **theorem count 67 の根拠**: appendix の theorem catalog を数えると実際の内訳は確認できるが、`TwoLayer.lean` の `example` 宣言が `theorem count: 0` とされており、 **manuscript 本文の「67 theorems」が投稿パッケージのどのファイル集合を対象とするか**が §9 に明記されていない（`Examples/` と `CaseStudy/` を含むか否か）。

5. **§1.5 traceability matrix**: `RQ1` の Lean anchor が `mem_preimage_iff` と `paper/lean/UadfU0/U0Spec/Construction.lean` を指しているが、定義ファイルは `Definitions/Model.lean` である。ファイルパスの不一致。

---

## 必須修正

| 優先度 | 修正内容 |
|---|---|
| **高** | §3.4/3.5 に hardness argument を追加：total-map 版と partial 版で証明構造がどう変わるかを命題レベルで明示 |
| **高** | §3.6 冒頭に `semanticPullback` / `E` abstraction の必要性の独立した動機付けを追加（non-claim の extractor 証明とは切り離した形で） |
| **高** | §7 各節を「本稿が言える命題 X は先行研究では言えない。なぜなら…」の肯定形式に書き換え |
| **中** | §4.3 の `Classical.choice` に関する constructive rewrite の可否と設計選択を 1 文で明記 |
| **中** | `lake-manifest.json` の Mathlib 非使用の設計判断を §4.1 または §9 に追記 |
| **低** | §1.5 traceability matrix の `RQ1` ファイルパスを `Definitions/Model.lean` に修正 |
| **低** | §2.8 を削除するか §5 examples に接続させる |
