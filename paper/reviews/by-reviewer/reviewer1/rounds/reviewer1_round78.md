# 査読レポート

**対象投稿先：CPP 2026（Certified Programs and Proofs）**

本論文の貢献は「新代数的同一性」ではなく「assumption-audited theorem-interface library」であると著者自身が明記しており、ライブラリ・方法論トラックを明示的に志向している。CPP はそのような機械検証ライブラリ貢献を第一級とする唯一の主要 FM 系会議であり、最適投稿先と判断する。FM・TACAS は新しい形式モデルや大規模事例を要求し、ITP は同様のライブラリ貢献を受け入れるが CPP より工芸的完成度への要求が高い。

---

## 1. 総合判定（Recommendation）

**Strong Reject**

主論文単体で FM 系トップ会議の採択水準を満たさない。数学的内容は全て古典的であり、Lean4 上の実現も技術的に単純である。「modest novelty by design」という著者の自己申告は誠実だが、査読委員会への根拠ではなく警告として機能する。必須修正チェックリストに列挙する問題は、所定の改訂サイクル内での解決が構造的に困難と見込む。

---

## 2. 強み

1. **assumption 開示の一貫性**：`hproj`/`hA`/`hcomm` を全定理の引数として明示し、`#print axioms` 結果まで報告している。この透明性は手本となる。
2. **sorry ゼロ・再現性基盤**：`reproduce_formal.sh` + `Dockerfile.fm` + SHA256 ハッシュ管理の三重チェック体制は再現性要件を正面から扱っている。
3. **反例主導の設計**：`transfer_fails_without_hproj`・`naive_totalization_adds_spurious_witness`・`EPlus1_not_complete` という対称的な反例群により、各仮定が非冗長であることを機械的に示している点は方法論的に評価できる。
4. **must/may 分岐の明示化**：`Option` の `none` 分岐を `preimageMay` として別系統化し、相互包含定理で関係を明示した設計は、全写像ライブラリとの差分として意味がある。

---

## 3. 主要懸念（Major concerns）

### M1. 数学的内容の新規性欠如

論文が主張する全定理は古典的集合論・順序論の Lean4 翻訳である。

- `U0_least_upper_bound_iff`・`UAndOn_greatest_lower_bound_iff`：`⊆`-順序下での LUB/GLB 特徴付けは教科書命題。
- `lifted_transfer`：`Option`-付き逆像の単調性。Mathlib の `Set.preimage_mono` の型変換版に過ぎない。
- `preimage_compose`：`Option.bind` の結合律から直ちに従う。`none` 分岐の場合分けは Lean4 の `cases` で機械的に処理される。
- `no_left_adjoint_of_partial`：部分写像では全射的 Galois 接続が成立しないという事実は代数学の基本結果であり、CPP での新規性要件を満たさない。

論文自身が §6「Mechanization Added Beyond Textbook Identities」で「classical overlap（novelty claim ではない）」を列挙しているが、「mechanization-specific value」として挙げる 5 項目はいずれも設計方針（explicit assumptions, first-class partiality）であり、定理としての新規性ではない。

### M2. 貢献の核心が構成論証を欠く

「assumption-audited theorem-interface kernel」を主貢献と主張するが、**なぜこのインタフェース設計が他の定式化より優れているか**の形式的議論が存在しない。具体的には：

- `SpecSet α := α -> Prop` という選択（Mathlib `Set α` を避けた）の技術的根拠が「最小依存性」のみ。既存インタフェースとの比較可能性（Proposition）がない。
- `U0`/`UAnd` の分離を「role-separation result for RQ3」と呼ぶが、union と intersection は定義から異なる演算子であり「分離」を証明する必要性自体が自明でない。

### M3. UStar の非構成性が主張を空洞化する

§3.8 の IdealRoot 定理群は `UStar : SpecSet α` を **仮定** として受け取り、`UStar ⊆ UAndOn` 等の条件付き包含を示す。しかし：

- `UStar` は実際には構成されず、「parametric theorem」のまま留まる。
- 従って §3.8 の全定理は「仮定 P が成立すれば結論 Q が成立する」という形であり、P の実現可能性への議論がない。
- 査読基準上、これは「証明されていない補題を仮定する定理」と等価であり、核心的証明義務の延期と見なされる。

### M4. 事例研究が貢献規模に対して不釣り合い

- PasswordPolicy 事例：`proj i n = some n`（恒等写像）で `A` を区間制約にした玩具モデル。74 定理・1807 LOC のライブラリを正当化する規模ではない。
- ArtifactBundleExample：`ReqIR`/`ApiIR`/`CodeIR` の三層モデルだが、実際の仕様管理システムへの適用可能性の論拠がない。
- 著者はこれを「model instantiation consistency, not external validity」と明記しているが、ライブラリ貢献として採択されるには独立した利用事例または非自明な定理への応用が必要である。

### M5. Mathlib 非依存設計の技術的コストが未回収

`lake-manifest.json` を空にする決定により：

1. `Set`・`Finset`・`Order.Lattice` の Mathlib API が使えず、1807 LOC の相当部分は基盤再実装に費やされている。
2. §7 で比較対象として Mathlib スタイル API（`Set.preimage_mono`・`GaloisConnection`）を挙げながら、それらとの相互運用性は皆無。
3. この選択が「仮定面の透明性向上」に実際に貢献しているかを示す比較実験がない。

---

## 4. 中程度の懸念（Medium concerns）

### Me1. `Classical.choice` 利用の非対称性の説明不足

`preimage_compose` が `Classical.choice` を引くが `lifted_transfer` は引かない、という非対称性は §4.3 で言及される。しかし：

- ITP/CPP 文脈では `Classical.choice` の使用は構成的証明不可能性のシグナルであり、非構成的証明が回避できない理由を theorem-level で正当化する必要がある。
- 「concise extensional-equality proof style を選んだ」という説明は工学的選択であり、理論的正当化ではない。

### Me2. RQ の非自明性主張が不十分

RQ1「Can we define induced inverse images consistently with heterogeneous carriers?」への答えは `carrier : ι -> Type` の indexed family 定義であり、Lean4 の依存型が自明に実現する。「negative outcome would force carrier-collapsing encodings」は可能性の議論として正しいが、本論文の構成が non-collapsing である技術的根拠が証明として与えられていない。

### Me3. §7 関連研究の深さ不足

- Hets・BX・Institution の言及はいずれも "definition-level positioning" の 3〜4 文で終わっており、本論文の定理との形式的比較がない。
- 特に Darais/Van Horn の Constructive Galois Connections（ICFP 2016）との差分は `Option`-partiality の扱いだけと読めるが、それ自体は技術的に小さい差分である。具体的な定理レベルの差分が必要。

### Me4. 74 定理のロール分類の客観性

§4.6 で「primary 15 / supporting 34 / example 25」と分類するが、この分類は著者が事後的に定義したものであり外部検証手段がない。特に `UStar_*` 系定理 6 本が「supporting」に分類されているが、§3.8 はメインテキストで major section として扱われており分類と位置付けが不整合。

---

## 5. 軽微修正（Minor / Editorial）

1. **Abstract の「methodological and interface-level」**：何に対して methodological なのか一文で具体化すること。
2. **§0.2 Non-claims の位置**：査読者は Non-claims を先に読むことで論文の射程を過小評価しやすい。序論後半への移動を検討。
3. **References「(selection)」表記**：CPP 等は完全文献リストを要求する。
4. **「Formal Aspects」**：Formal Aspects of Computing（FACo）なのか別誌なのかを明記。
5. **§4.4 "lake job count (46) is a build-graph execution count"**：読者が混乱しやすい。再現性報告としては `theorem count = 74` と `sorry count = 0` のみで十分。
6. **数式の LaTeX 記法**：`\Leftrightarrow` 使用箇所が一部 ASCII 表記と混在（`Contradictory` 定義等）。統一すること。

---

## 6. 必須修正チェックリスト（採択条件）

採択に至るには以下を全て解決する必要がある。

- [ ] **[M1] 数学的新規性の再定義**：既存ライブラリで直接表現できない命題を 1 本以上追加し、新規性として前面に出すこと。または「library contribution」として ITP のアーティファクト評価トラック等、novelty 要件の異なる投稿先に変更すること。
- [ ] **[M2] インタフェース設計の優位性の形式的議論**：代替定式化（例：`Set α` ベース・Mathlib依存版）との比較定理を追加し、本設計の技術的利点を証明レベルで示すこと。
- [ ] **[M3] UStar の構成またはスコープ明確化**：UStar を構成しないならば §3.8 全体を「open assumption template」として明確に付録に移し、主貢献から除外すること。構成する場合は具体モデルにおける構成方法を定理として示すこと。
- [ ] **[M4] 実質的な事例研究の追加**：1807 LOC のライブラリを活用した、非自明な仕様管理問題（最低でも 3 層以上かつ heterogeneous carrier が本質的に必要なケース）への適用を機械検証すること。
- [ ] **[M5] Mathlib 非依存の技術的正当化**：Mathlib 依存版との axiom footprint 比較、または本設計が interoperability を犠牲にして得る具体的な証明工学的利点を定理として示すこと。
- [ ] **[Me1] `Classical.choice` の必然性の論証**：`preimage_compose` の証明を構成的スタイルで再試みるか、構成的証明不可能性の根拠（または避けようとした場合の proof-term 爆発等の技術的障害）を明示すること。
- [ ] **[Me3] 関連研究の定理レベル比較**：Darais/Van Horn との差分を `HasLeftAdjoint` 定義の level で比較し、`Option`-partiality が Constructive Galois Connections の枠組みでは表現できない理由を示すこと。
