# 厳格査読判定: UAD/f U0 構成規則の機械検証論文

## 採否判定
**Borderline** (条件付き採録可能、ただし以下の必須修正を要求)

## 採点（10点満点）

- **新規性**: 6/10
- **技術的妥当性**: 7/10
- **再現性**: 8/10
- **可読性**: 5/10

## 必須修正事項（致命度順）

### 1. 【致命的】実プロジェクト由来データでの外的妥当性欠如
**現状**: 合成データのみで評価（§5.4, §7）。ケーススタディが人工制約のみ。
**要求修正**:
- 最低2件の実OSSプロジェクト（例: OpenSSL/PostgreSQL）から抽出した実アーティファクトで矛盾検出率を実証
- `paper/case-study/` に実プロジェクトベンチマークスクリプトと結果を追加
- 検出された矛盾の質的分析（偽陽性率・見逃し率の評価）

**修正箇所**:
- `paper/manuscript/uadf_u0_spec_proof.md` §5.4（新セクション挿入）
- `paper/case-study/` に `real_project_validation/` ディレクトリ追加
- `paper/lean/UadfU0/CaseStudy/` に実プロジェクト由来の第2ケーススタディ追加

---

### 2. 【重大】抽象解釈理論との関係説明の技術的不正確性
**現状**: §6 で「本稿は Galois 随伴の標準的随伴性を満たさない」と述べるが、随伴性破綻の形式的証明がない。
**要求修正**:
- Lean で `¬∃α, α ⊣ preimage` を示す反例構成（`proj x = none` の場合）
- または、部分 Galois 接続（partial Galois connection）の既存研究との位置づけを明示し、本稿がその変種であることを数学的に証明

**修正箇所**:
- `paper/lean/UadfU0/RelatedWork/GaloisNonAdjunction.lean`（新規ファイル）
- `paper/manuscript/uadf_u0_spec_proof.md` §6（関連研究節の再構成）

---

### 3. 【重大】型理論実装の非自明性主張が補題依存関係で未裏付け
**現状**: §4.1 で「`Option.bind` 正規化は型検証器なしでは見落としやすい」と主張するが、実際の証明で何ステップ使ったか定量化されていない。
**要求修正**:
- `preimage_union`, `preimage_compose`, `lifted_transfer` の各証明で使用した補題を依存グラフで可視化
- 「素朴な集合論証明では不要だが型付き設定で必要になった補題」を明示的にラベル付け（例: `set_ext`, `Option.bind_eq_some`）
- 補題依存グラフを `paper/lean/analysis/lemma_dependency.dot` として提供

**修正箇所**:
- `paper/manuscript/uadf_u0_spec_proof.md` §4.1（定量的エビデンス追加）
- `paper/lean/analysis/` ディレクトリ新設

---

### 4. 【中程度】層間合成則（定理9）の実用性が不明
**現状**: `proj_j = bind(proj_i, g)` の仮定が「実装パイプライン」に対応すると述べるが（§3, Theorem 9）、実際の AST 抽出器でこの形式が成立する事例が皆無。
**要求修正**:
- `paper/lean/UadfU0/Examples/CompositionExample.lean` を現実的抽出器に差し替え（例: JSON パース → 型検証の2段変換）
- または、`bind` 仮定を満たさない抽出器クラスに対する限界を明記し、定理9の適用範囲を論文中で制限

**修正箇所**:
- `paper/lean/UadfU0/Examples/CompositionExample.lean`（現行の mod 2 例を廃止）
- `paper/manuscript/uadf_u0_spec_proof.md` 定理9の記述（適用条件の限定）

---

### 5. 【中程度】再現パッケージの公開不在
**現状**: §5.3 でローカル再現手順のみ。DOI/GitHub リリースタグなし。
**要求修正**:
- Zenodo/Figshare で DOI 付きアーカイブ公開（Lean ツールチェイン固定版含む）
- `README.md` に DOI リンクと SHA-256 チェックサム記載

**修正箇所**:
- `paper/README.md`（DOI セクション追加）
- 外部アーカイブ登録（論文受理後でも可、ただし投稿時に登録予定を明記）

---

## 現版の最大の強み

1. **部分射影の明示的型付き定式化**: `proj : Ω → Option β_i` による `f^{-1}` の誘導定義は、従来の抽象的記法を具体化し、型検証可能にした点で評価できる。

2. **抽出判定器の健全性/完全性証明（定理11）**: パスワード長制約DSLにおいて、閉形式判定式と存在検証の論理的同値性を機械検証した点は、形式手法の実務適用に向けた具体的貢献である。
