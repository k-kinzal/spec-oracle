# Session Context

## User Prompts

### Prompt 1

Implement the following plan:

# UAD/f モデル型厳密化プラン

## Context

UAD/f モデル (`spec-core/src/udaf.rs`) の実装が型安全性に欠けており、以下の問題が発生しています：

1. **String ID の多用**: Universe.id, Domain.id などすべて String で、命名規則が強制されていない
2. **HashMap<String, String> metadata**: キーも値も自由形式で、タイプミスが検出されない
3. **参照の整合性なし**: HashSet<String> で ID...

### Prompt 2

はい、コンパイルは通るべきです。通らないということは作業は終わっていません。

