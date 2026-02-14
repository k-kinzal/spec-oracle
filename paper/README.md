# paper

このディレクトリは「UAD/fモデルでのU0仕様の証明」関連成果を格納する。

- `manuscript/`: 論文本文
  - `uadf_u0_spec_proof.md`: 読みやすい版
  - `uadf_u0_spec_proof.tex`: 学術誌向け体裁
- `lean/`: Lean4形式証明
  - `UadfU0/Definitions`: 型付きUAD/fモデル定義（`Ω`, `βᵢ`, `Dᵢ`, `Aᵢ`, `projᵢ`）
  - `UadfU0/U0Spec`: U0仕様の主証明
  - `UadfU0/InterLayer`: 層間整合性・矛盾検出の補助証明
  - `UadfU0/CaseStudy`: 具体抽出判定器の健全性/完全性証明
  - `UadfU0/Examples`: 具体例
- `case-study/`: 実証スクリプトとベンチマーク結果
- `reviews/`: Claudeによる教授レビュー・査読ログ
