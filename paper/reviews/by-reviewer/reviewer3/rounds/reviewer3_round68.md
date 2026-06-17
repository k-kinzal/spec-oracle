## 総合判定

**弱採択（Minor Revision）相当 — ただし新規性の位置づけと関連研究の記述に実質的な修正が必要**

FM/FASE/CPP 基準では、機械検証済み形式核としての寄与は原則受け入れ可能な範疇にある。しかし以下に述べる懸念が解消されなければ、査読者が「エンジニアリング論文への誤誘導」または「既存ライブラリの再パッケージング」と判断するリスクが高い。

---

## 主要懸念

### 1. 新規性の境界が不明確（§6, §7）

**問題：** §6.1 の "concrete delta" は「one auditable package」として主張するが、CPP/FASE 基準では「パッケージング」単体は採択理由として不十分とみなされることが多い。核心の問いは「なぜ Mathlib の `Set`・`Finset`・`GaloisConnection` ライブラリ群を直接使わず独自 `SpecSet` を定義したか」であり、その正当化が §2.1 の1文（"local alias"）のみで済まされている。

**影響範囲：** `U0_least_upper_bound_iff`（§3.2）・`UAndOn_greatest_lower_bound_iff`（§3.2）は Mathlib `sSup`/`sInf` の特殊化として査読者が即座に読む。これらを "join/meet characterization" と称して§3.3 の役割分離結果の証拠として扱うのは論理的に弱い。

**必要対応：** Mathlib 既存定理との命題レベルの差分を表にして示すか、なぜ Mathlib 上に構築しなかったかを明示する。

---

### 2. `lifted_transfer`（§3.4）の非自明性の主張が不十分

**問題：** 論文は "same-root linkage (`hproj`) and admissibility transport (`hA`) are explicit" を非自明性の根拠とするが、これは述語論理での存在量化と全称量化の素直な組み合わせに過ぎない。査読者が `Transfer.lean` を見れば、証明は7行程度の構造的場合分けで完結しており、"technically central" という表現は誇張に映る。

**影響：** §6 の "Per-theorem hardness summary" の記述と実際の証明の間にギャップがある。

**必要対応：** 「`hproj` なしにはどんな反例が成立するか」を形式的に示す（現状は散文のみ）。`AdequacyCounterexample.lean` と同様のパターンで `TransferCounterexample` を追加するか、あるいは hardness の主張を下げる。

---

### 3. §3.7 非随伴性定理の位置づけ（`no_left_adjoint_of_partial`）

**問題：** この定理は `proj i x0 = none` という単一点の存在から随伴の不在を導く。証明は5ステップで自明に完結し（`Galois.lean` 参照）、定理内容自体は "preimage of partial function lacks left adjoint" という教科書的事実の直接の形式化である。

論文は §7.5 でこれを "partiality-specific boundary theorem" と呼ぶが、`Constructive Galois Connections (ICFP 2016)` や Mathlib の `GaloisConnection` は既に部分写像の扱いを論じている。本定理がそれら先行研究との何を形式的に区別するかが示されていない。

**必要対応：** Darais & Van Horn (2016) の定義と本定理の定義を命題レベルで比較し、先行研究でカバーされない部分を明示する。

---

### 4. `RQ5` の境界宣言（§0.3, §3.6）と Abstract `E` の意義

**問題：** §3.6 は "Motivation for introducing abstract `E`" を述べるが、抽象 `E` は `proj` との等価性（`hEq`）を仮定すれば `preimage_eq_semanticPullback` が成立するという同語反復的な構造になっている。`AdequacyCounterexample.lean` は `E ≠ proj` の場合を示すが、それは "adequacy decomposition is not a tautology" の確認であり、新しい数学的洞察ではない。

**影響：** RQ5 の "answer" として §0.1 claim 3 に対応するが、concrete extractor が義務（obligation）にとどまる限り、theorem の射程が狭い。

**必要対応：** "one-sided adequacy" が工学的に何を可能にするかを、少なくとも1つの具体的シナリオで形式的に示す（PasswordPolicy 程度の事例で可）。現状の §5.2 は consistency check に留まり adequacy は触れていない。

---

## 軽微懸念

### 5. `SpecSet` の重複定義リスク

`abbrev SpecSet (α : Type v) : Type v := α → Prop` は Mathlib `Set α` と定義同値だが意図的に分離している。§2.1 にその理由が1行しかない。CPP では "why not Mathlib `Set`" は標準的な審査項目。

### 6. `lake-manifest.json` がパッケージ依存なし

```json
"packages": []
```
Mathlib 非依存であることは確認できるが、`Classical.choice` と `Quot.sound` が axiom audit に現れる（§4.3）。`propext` + `Classical.choice` を用いる等価証明がある以上、完全に constructive とは言えない。§4.3 はこれを正直に開示しているが、ITP/CPP 系ではこの axiom 使用が採択判断に影響することがある。明示的に "not claiming constructivity" と Abstract に一言追記すると望ましい。

### 7. §5.2 PasswordPolicy と §3.6 の接続欠如

`checkConsistent_iff_allThree`（`PasswordPolicy.lean`）は consistency を証明するが、adequacy theorems（`preimage_eq_semanticPullback` 等）とのリンクが `req_projection_adequacy` の1定理のみ。これを §5 で adequacy 例として積極的に論じるか、例の説明を絞るかどちらかにすべき。

### 8. §8 の制限事項「constraint language focus is parameter-bound centric」が不明瞭

"parameter-bound centric" は論文のどこにも定義されておらず査読者には意味不明。削除するか言い換えが必要。

### 9. 参照文献の年代バランス

Nuseibeh et al. (1994)・Back & Wright (1998) 等の古典は適切だが、2020年以降の FM/ITP コミュニティの Lean4 関連論文（例：Mathlib4 論文 ITP 2024）が未参照。CPP 投稿では Lean4 エコシステムの最新状況への言及が期待される。

---

## 必須修正

| 優先度 | 対象箇所 | 修正内容 |
|--------|----------|----------|
| **高** | §6.1, §7 | Mathlib 既存定理（`GaloisConnection`・`Set` API）との命題レベル差分表を追加 |
| **高** | §3.4 / §6 hardness | `lifted_transfer` の非自明性を反例または境界定理で形式的に裏付ける |
| **高** | §7.5 | Darais & Van Horn (2016) との定義レベル比較を追記し、`no_left_adjoint_of_partial` の位置づけを明確化 |
| **中** | Abstract | "not claiming constructivity for all proofs" を1文追加 |
| **中** | §3.6 / §5 | RQ5 の one-sided adequacy が具体的に何を可能にするか、PasswordPolicy 等で1例示 |
| **低** | §8 | "parameter-bound centric" を削除または定義 |
| **低** | References | Lean4/Mathlib4 関連 ITP 2024 論文を追加 |
