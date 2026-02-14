# paper

このディレクトリは「UAD/fモデルでのU0仕様の証明」関連成果を格納する。

- `manuscript/`: 論文本文
  - `uadf_u0_spec_proof.md`: 読みやすい版
  - `uadf_u0_spec_proof.tex`: 学術誌向け体裁
- `lean/`: Lean4形式証明
  - `UadfU0/Definitions`: 型付きUAD/fモデル定義（`Ω`, `βᵢ`, `Dᵢ`, `Aᵢ`, `projᵢ`）
  - `UadfU0/U0Spec`: U0仕様の主証明
  - `UadfU0/InterLayer`: 層間整合性・伝播・合成則・抽出適合の証明
  - `UadfU0/RelatedWork`: 既存理論との差分（非随伴性）の形式証明
  - `UadfU0/CaseStudy`: 具体抽出判定器の健全性/完全性証明
  - `UadfU0/Examples`: 具体例
- `case-study/`: 判定式と全探索の一致検証スクリプトと結果
- `reviews/`: Claudeによる教授レビュー・査読ログ
