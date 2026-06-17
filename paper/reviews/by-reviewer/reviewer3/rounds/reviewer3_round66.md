# 査読レポート：UAD/f Two-Operator Kernel under Partial Projections

---

## 総合判定

**弱採択（Weak Accept）／条件付き採択**

FM/ITP/CPP/TACASのうち、**CPP（Certified Programs and Proofs）またはITPが最も適切なベニュー**。TACASはシステム寄りのため弱い。FACSEは応用寄りで若干ミスマッチ。主張境界の明示と mechanization-specific 価値の分離は誠実であり、CPP 基準では採択圏に入り得る。ただし以下の懸念を修正しなければ採択ラインに届かない。

---

## 主要懸念

### M1. 新規性の位置づけが弱すぎる（§7, §6）

関連研究節（§7）は「我々はより狭い」「我々は機械化しただけ」という後退的な書き方に終始している。CPP/ITPの査読者は「この機械化のどこが難しかったのか、既存のMathlib/Coqライブラリではなぜ不十分なのか」を聞く。

- §6の "Per-theorem hardness summary" はその答えになり得るが、**先行研究との比較が一切ない**。例えば `preimage_compose` の `none` 分岐除去は、Agda/Coq における `Option.bind` の単純なモナド則と何が違うのか？
- **必須修正**: §7に「本稿の機械化が既存Mathlibの集合論的定理だけでは埋められない理由」を1節追加する。具体的には：Mathlibの `Set.preimage` は全域関数を前提としており、部分射影（`Option`）を持つ heterogeneous carrier 上の admissibility 転送を組み合わせた系は既存ライブラリに存在しないことを明示する。

### M2. RQ1–RQ5 と定理の対応が不完全（§1.3, §3.2）

§3.2で "RQ1 is answered by typed inverse-image definitions" と述べるが、RQ1の問いは「consistent に定義できるか」であり、その答えに相当する定理が何か明示されていない。`preimage_monotone` か `mem_preimage_iff` か、対応が曖昧。

- RQ4/RQ5 は §3.4–3.6 と対応しているが、**RQ2とRQ3の対応定理が §3.2 の一段落に押し込まれ、本文中で定理名が見つからない**（`U0_witness_projects_to_some_domain` が RQ2 の答えなら、そこで明記すべき）。
- **必須修正**: 各 RQ に対し「この定理がその答えである（Lean定理名, ファイル）」を表形式で §1.4 または §3.x に配置する。

### M3. 意味論的新規性の核心が論文全体で散逸している

本稿の根幹は「U0（join）とUAnd（meet）の役割分離が、partial projection 設定下でどう非自明になるか」だが、この主張が coherent に現れる節がない。

- §2.5 は定義のみ。§3.3 は "implication" として箇条書き。§6 では触れていない。
- 特に **`UAndOn_empty_eq_univ`（空の active set で meet が宇宙全体になる）** という edge case は、従来の完全写像設定では自明でない振る舞いを示すが、これが novelty として前面に出ていない。
- **必須修正**: §3.3 を独立した "Role-Separation Theorem" 節として昇格させ、total-map 設定との振る舞い差を明示的に比較する段落を追加する。

---

## 軽微懸念

### m1. Axiom audit の解釈が不十分（§4.3）

`preimage_compose` に `Classical.choice` が含まれる理由の説明がない。constructive ITP（CPP）査読者はここを問う。`Classical.choice` の使用が避けられないのか、代替があるのかを1文で述べるべき。

### m2. §3.8（Ideal-root linkage）の `UStar` の地位が不明確

`UStar` が「定理パラメータである」と §3.8 冒頭で述べるが、§1.2 の formal objective には `UStar` が登場しない。読者は「なぜ `UStar` を構成しないのか」という疑問を持つ。Non-claims（§0.2）に明示的に追加するか、§3.8 冒頭に「`UStar` の構成はスコープ外であり、その理由は…」を1文加えるべき。

### m3. §5（Mechanized Examples）と §8（Limitations）の整合

§5 の Password-policy case study は "constrained interval domain" と説明されるが、§8 の Limitation 1 は "constraint language focus is parameter-bound centric" と述べる。これは矛盾に見える（例が limitation を体現している）。意図的ならその旨を書くべき。

### m4. §9 の再現性コマンドに `--quiet` オプション等がない

`rg -n '\bsorry\b' UadfU0 || true` は CI 環境で警告を隠す可能性がある。査読者が手元で実行する際のコマンドとして不親切。補足として `|| echo "no sorry found"` を推奨。

### m5. 参照文献の番号と本文引用の不整合リスク

§7 の各節で "Reference [N]" ではなく著者名引用を使っており、末尾 References との対応が番号なしで書かれている。CPP はしばしば番号引用を要求する。スタイル統一が必要。

---

## 採択のための必須修正

1. **§7 に「既存 Mathlib/Coq ライブラリとの差分」を明示する節を追加する**（M1）。partial + heterogeneous carrier + admissibility の組み合わせが既存ライブラリのギャップであることを具体的なライブラリ名と機能欠如で示す。

2. **RQ–定理対応表を §1.4 または §3 冒頭に配置する**（M2）。各 RQ に対して答えとなる Lean 定理名とファイルパスを明記する。

3. **§3.3 を "Role-Separation Result" として独立節に昇格させ、total-map 設定との差分を比較する段落を追加する**（M3）。特に `UAndOn_empty_eq_univ` と空集合 edge case の非自明性を前面に出す。

4. **`Classical.choice` 使用理由の1文説明を §4.3 に追加する**（m1）。constructivism への立場を明示する。
