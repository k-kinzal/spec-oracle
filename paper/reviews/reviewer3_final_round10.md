Verdict: OK

---

## 根拠

### 1. 型・論理・定理対応の整合性
本文（`.md`）とLean実装（`.lean`）の追跡は以下の通り完全である。

- §2.2 `preimage` 定義 → `Definitions/Model.lean` L47-49（typed partial projection）
- §3.1 `U0` join → `U0Spec/Construction.lean` L37-38（`∃i, lifted i`）
- §3.2 `U∧` meet → `U0Spec/Construction.lean` L44-45（`∀i, active i → lifted i`）
- §4.1 伝播定理 → `InterLayer/Transfer.lean` L15-30（`hproj`同一点連結仮定明記）
- §4.2 合成則 → `InterLayer/Composition.lean` L20-48（`pullbackVia`定義+合成定理）
- §4.3 adequacy分解 → `InterLayer/Adequacy.lean` L17-42（sound-only/complete-only/両方向の3定理）
- §4.4 非随伴性 → `RelatedWork/Galois.lean` L21-38（`no_left_adjoint_of_partial`）
- §4.5 GLB → `U0Spec/Minimality.lean` L38-56（`UAndOn_lower_bound` / `_greatest_lower_bound_iff`）

型不整合・参照不能な定理は検出されない。

### 2. 仮定明示と証明構造の機械検証
以下の設計判断（§5）が定理仮定として追跡可能である。

- 同一点連結仮定（`hproj`）: `Transfer.lean` L18-21で`∀x yj, proj j x = some yj → ∃yi, proj i x = some yi ∧ R yi yj`と明記
- one-sided adequacy: `Adequacy.lean` L17-26（sound）/ L31-40（complete）で分離定理化
- 部分性と随伴破綻: `Galois.lean` L25で`hnone : proj i x0 = none`を仮定、L33-38で矛盾導出
- 演算分離（join/meet）: `Construction.lean` L37（`U0 := ∃i`）/ L44（`UAndOn := ∀i`）で型レベル区別

これらは**Lean4型検査+定理証明**を通過しており、致命的論理破綻は無い。

### 3. 実行可能性の証跡整備
`RQ6 (practice)` の技術的再実行可能性は以下で担保される。

- §6.2抽出デモ: `external_validation.py` + `source_lock` + `snapshots/*` で版固定再現
- §7.5追試手順: オンライン/オフライン分岐+SHA256検証を記載
- §7.1 Lean再現: `lake build` で依存0（標準ライブラリのみ）
- §7.4定理数43+LOC1103の構成比を定量記録

偽陽性リスク（§4.7 must解釈、§6.4負例）と限界（§9: regex意味保存未証明）を明記しつつ、技術的再実行可能性デモとしてスコープ限定されている。

---

## Minor notes（受理を妨げない改善提案）

1. **抽出器adequacy実証の今後課題化**  
   §4.3定理は抽象関係`E`に対する分解を与えるが、regexや他実装の意味保存証明は§9で明記された通り未完である。  
   今後、具体抽出器への`E`適用評価（ファジング・LLM出力統計など）を追加すると`RQ5(theory)→RQ6(practice)`接続が強化される。

2. **D(i)分離の運用実証**  
   §2.1で`A(i) ⊆ D(i)`分離の意義を説明しているが、§6.2デモは`A(i)`候補生成に主眼があり`D(i)`実運用は未到達と§2.1末尾で正直に記載されている。  
   将来ケースで境界値前提（単位・範囲）を`D(i)`側に明示的に分離すると、定理`lifted_subset_preimage_domain`（L65）の実務有効性が増す。

3. **長期アーカイブ戦略の制度化**  
   §7.5でDOI/Waybackを推奨事項として言及しているが、現時点で制度化していないと§9 L9で認めている。  
   論文アーカイブ提出時に固定DOI取得+source-lockのチェックサム再検証手順を追加すると追試安定性が向上する。

4. **変異試験の解釈強化**  
   §6.3で「変異3件全検出」をsanity checkと正しく位置づけているが、将来的に正例（整合）/負例（矛盾）のバランス評価や自然発生矛盾ケースを追加すると判定器のカバレッジが明確化される。

---

**総評**: 本文と機械検証の対応は追跡可能であり、型/論理の致命的不整合は検出されない。実抽出器adequacy未証明やケース限定（n=3, 数値境界のみ）は§9で明記済みであり、スコープ限定論文として受理妥当。Minor notesは今後の段階的拡張として扱う。
