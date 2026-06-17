## 査読レポート：Reviewer #2

**対象投稿先（推奨）: CPP（Certified Programs and Proofs）**

理由：貢献の核はLean4による機械検証カーネルの設計・実装であり、ITPも次善の候補。FM/TACASは数学的新規性への要求が高く、著者自身が「定理の同一性はほぼ古典的」と述べているこの投稿には荷が重い。FASE/Formal Aspectsは工学的評価軸が強く、本稿の形式手法寄りの立場とはやや合わない。

---

## 1) 総合判定（Recommendation）

**Major Revision — 条件付きで採択可能**

機械検証の規律・仮定明示の設計姿勢は高く評価できる。しかし、貢献の新規性の定位が不明瞭なまま防衛的記述で補われており、動機づけとなる実例が玩具水準に留まり、関連研究との比較が「位置づけ程度」に過ぎない。以下の主要懸念点を解消すれば採択圏に入る水準と判断する。

---

## 2) 強み

1. **仮定明示設計の徹底**  
   `hproj`・`hA`・`hcomm` を定理の明示的な引数として配置し、落とした場合の反例（`transfer_fails_without_hproj`、`EPlus1_not_complete`、`naive_totalization_adds_spurious_witness`）を機械検証した設計は堅実。仮定を暗黙の散文に埋めず定理シグネチャに露出させる手法は、ライブラリ設計の模範として評価できる。

2. **sorry ゼロの機械検証とトレーサビリティ**  
   §4.4・§4.5 の定理→ファイル対応表、assumption matrix、SHA256 ハッシュによる再現性の記述は FM 系コミュニティが求める水準を満たしている。`reproduce_formal.sh` と Dockerfile の提供は再現性向上に実効的。

3. **スコープ宣言の誠実さ**  
   Non-claims（§0.2）でエクストラクタ正当性・統計的外部妥当性・時相仕様を明示的に除外している点は評価できる。over-claim を避けた丁寧な姿勢である。

4. **must/may の分離とパーシャル性の扱い**  
   Option 型を first-class に扱い、none 分岐の除去を proof obligation として明示した点は、全域写像系のライブラリへの単純な還元ができない理由を`TotalizationCounterexample`で mechanize して示しており、有効。

5. **U0/UAnd の役割分離の明示性**  
   join-side (U0) と meet-side (UAnd) の単調性方向の違い（U0On の単調性 vs UAndOn の反単調性）を一つのモデルで mechanize した点は、実用的な整合性チェックの基盤として意義がある。

---

## 3) 主要懸念（Major concerns）

### M1. 新規性の定位が不十分で査読基準を満たさない

著者自身が §0 で「定理の新規性は控えめ」「新しい集合論ではない」と述べ、§6 で「古典的重複」を列挙している。しかし、**方法論的貢献が査読基準として成立するためには、既存ライブラリでの実現困難を定量的に示す必要がある**。

現在の §6.1「Concrete delta against baseline theorem libraries」は次の問いに答えていない：

- MathLib の `Set.preimage`・`GaloisConnection`・`sSup`/`sInf` を使って同等のカーネルを構築した場合、何の追加作業が必要か、あるいは不可能になるか？
- Isabelle/HOL の Locales や Type Classes を用いた類似の heterogeneous index formalization（例：Ballarin の locale-based algebra）との差分は何か？
- `carrier : ι -> Type` の依存型活用は、Lean4 特有の利点か、それとも Agda や Rocq (Coq) でも同様に実現できるか？

これを回答なしに「explicit assumption-interface design」と述べるだけでは、査読者は「Mathlib で書けたのでは？」という疑問を解消できない。

**要求**: 少なくとも一つの既存ライブラリを使った試みとその困難点を、定理レベルで具体化すること。あるいは、Mathlib `Set.preimage` を Option 型に持ち上げた際に必要となる追加補題の数・種類を明示すること。

### M2. 動機づけとなる実例が玩具水準であり、主張する応用可能性を支持しない

§5.2 の PasswordPolicy ケーススタディは、射影が恒等写像（`proj _ n = some n`）、ドメインが `True`、制約が整数区間という、本論文の partial projection / heterogeneous carrier の本来の難しさが一切登場しない例である。

§5.1 の ArtifactBundleExample も、抽象型 `ReqIR`・`ApiIR`・`CodeIR` を定義しているが、これらが実際のソフトウェア工学的な artifact 構造を反映しているかどうかは不明であり、具体的な工学的文脈がない。

**要求**: 以下のいずれかを追加せよ。
- heterogeneous carrier が実質的に機能する（型が真に異なる、かつ射影が自明でない）中規模の例
- または、同じカーネルを使った別プロジェクトへの適用可能性を示す minimal な証明義務テンプレートの外部検証

### M3. Two-paper strategy が本稿の形式的自己完結性を損なっている

§0 で「engineering paper とは独立して自己完結」と主張するが、文中に「engineering paper の PoC パイプライン（`paper/engineering/manuscript_se.md`）」への参照が多数存在し（§0.2 の非主張 4、§3.6、§3.8、§4.4 等）、形式的論文の動機づけが工学的文脈に依存している。

査読者はそのコンパニオン論文を参照できないため、次の問いが解決不能のまま残る：
- このカーネルが実際のシステム開発の multi-layer specification 問題をどの程度解決するか
- §3.8 の `UStar` パラメトリック前提が現実の工学設定でどのような具体的な形を取るか

**要求**: 本稿単体で「なぜこのカーネルが必要か」を示す完全な動機づけ節を設けること。コンパニオン論文への参照は informational footnote に格下げし、formal claim の根拠として使わないこと。

### M4. 関連研究の比較が表面的で定量化されていない

§7 の各サブセクション（institution・BX・Galois 等）は「このカーネルは〜しない、代わりに〜する」という対比を述べるが、いずれも「定義レベルの位置づけ」に留まると著者自身が認めており（§7 冒頭）、これは査読基準を満たさない。

特に：
- **Institutions（Goguen/Burstall）との差分**: satisfaction condition の preservation を mechanize しないトレードオフを述べるが、同等の「typed root-kernel」を institution 定義の上に構築できないのかどうか、なぜこの選択が正当化されるかを論じていない。
- **BX/TGG**: 一方向性の contract は BX の「stable under composition」条件と何が違うか、またはどのように関係するかが不明。
- **Constructive Galois Connections（Darais/Van Horn）**: §7.5 で言及されているが、彼らの Coq 実装と本稿の Lean4 実装の間で、partial projection 扱いの具体的な差分定理が示されていない。

**要求**: 少なくとも Institution および Constructive Galois Connections の既存 mechanization との定理レベルの比較（「X は証明できるが Y は証明されていない」「X は仮定として必要だが Y では省略されている」等）を 1 節追加すること。

---

## 4) 中程度の懸念（Medium concerns）

### Med1. Primary 定理が 15 件は CPP の水準として狭い

74 件の定理宣言のうち、RQ3-RQ5 に対応する primary は 15 件、supporting は 34 件、example は 25 件（§4.6）。CPP の library-style paper では primary theorem の数よりも depth が問われるが、15 件で 6 RQ（実質的な novelty は RQ3-RQ5 の 3 RQ）をカバーするのは、ボリュームの観点で borderline。

**提案**: supporting lemma のうち、assumption auditing の観点で非自明なものを primary に格上げするか、または supporting lemma の non-triviality を §6 でより明示的に論じること。

### Med2. `Classical.choice` の使用と constructivity の扱い

§4.3 item 7 で、`preimage_compose` における `Classical.choice` の使用を「proof-style choice」として正当化し、「constructivity-preserving re-proof is outside this scope」と述べている。CPP は constructive proof を重視する傾向があり、この選択は弱点になりえる。

**提案**: 最低限、`preimage_compose` の constructive 再証明が原理上可能かどうか、および `Classical.choice` を避けるために何が必要かを 1 段落で論じること。

### Med3. §0「Section 0」の存在が採択ドキュメントとして不適切

「Section 0: Scope, Split, and Quality Bar」は通常の論文フォーマットに存在しない節番号であり、査読者への防衛的なメッセージ性が強い。この内容（スコープ、非主張、RQ）は §1 冒頭または Introduction に統合すべき。現状では「採択されにくいことを著者が知っている」という印象を与える。

**提案**: Section 0 を削除し、内容を §1.1（Problem Statement）と §1.3（Research Questions）に吸収すること。

### Med4. 参考文献が 13 件と少なく、年代が古い

2026 年時点の投稿として、参考文献の最新論文が 2021 年（Lean 4 の CADE 論文）であり、2022-2026 年の Lean4 community の mechanization 事例（例：Mathlib4 への貢献、FMCAD/ITP 2022-2025 の関連 Lean4 論文）がほぼ引用されていない。

**提案**: Lean4 mechanization の関連最新論文（少なくとも ITP 2023-2025 から 3-5 件）を追加すること。

---

## 5) 軽微修正（Minor / Editorial）

1. **英文表現**: "This formal manuscript is self-contained for theorem claims" は "This manuscript is self-contained with respect to theorem claims" が自然。"methodology-style formalization tracks" は表現が不安定。全体的に defense-oriented な文体が散見され、査読前の editorial revision が必要。

2. **Abstract の密度**: Abstract に "One-sided adequacy (sound/complete, must/may)" を列挙しているが、この区別の重要性が abstract 単独では伝わりにくい。なぜ one-sided decomposition が必要かを 1 文追加せよ。

3. **§3.6 の `E ≠ graph(proj)` の動機が遅い**: §3.6 に達するまで `E` を導入する理由が分からない。§2 で予告するか、§1.1 の Problem Statement で「extractor の semantic relation と projection 実装の乖離」に言及すること。

4. **`UAnd_eq_UAndOn_all` のブリッジ**: §2.5 で "Definition-placement note" として列挙されているが、これは prose ではなく定理トレーサビリティ表（§4.5）に掲載すべき。

5. **References 形式の不統一**: [6] Nuseibeh et al. に "ViewPoints" のみで出典（IEEE TSE, 1994）が不完全。正式な論文タイトルと巻号を記載すること。

---

## 6) 必須修正チェックリスト（採択条件）

以下を revision で解消しなければ再採択判定を保留する。

- [ ] **M1 対応**: Mathlib または Isabelle/HOL の既存 preimage/lattice ライブラリを使った場合の limitation を定理レベルで 1 箇所以上具体化すること（「`preimage_compose` の Option 分岐処理は `Set.preimage_comp` に還元できない。なぜなら……」という形式で）。
- [ ] **M2 対応**: heterogeneous carrier が自明でない（射影が恒等でない、型が実質的に異なる）中規模例を 1 件追加するか、または PasswordPolicy の例の limitation を §5 末尾に明示し、より実質的な例の追加を Appendix に置くこと。
- [ ] **M3 対応**: 本稿単体で自己完結する Motivation/Background 節を整備すること。コンパニオン論文への参照は formal claim の根拠から除外し、informational footnote に格下げすること。
- [ ] **M4 対応**: Institution または Constructive Galois Connections の既存 mechanization との定理レベル比較（差分定理 1-2 件）を §7 に追加すること。
- [ ] **Med3 対応**: Section 0 を削除し、内容を §1 に統合すること。
- [ ] **全体**: non-claim の列挙（§0.2）は §1 末尾の 1 パラグラフに圧縮し、査読ドキュメントとしての構造を標準化すること。

---

**付記**: 上記修正が適切に行われれば、CPP の methodology/library track（あるいは ITP の application track）での採択は十分に見込める水準の仕事である。査読者として「できていないことの正直な記述」を評価しており、それを踏まえた revision を期待する。
