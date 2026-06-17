# Session 142: U0 Reverse Mapping Improvements

## 問題の認識

U0（ルート宇宙）は逆写像によって構築される特別な宇宙である：
```
Code, Tests, Docs, Proto, Contracts, Types, TLA+ → [f₀ᵢ⁻¹] → U0
```

現在の実装状況：
- ✅ 逆写像の構造は適切に設計されている
- ✅ `UDAFModel::construct_u0()` が実装されている
- ✅ `ModelSync::create_inverse_transforms()` が自動的に逆写像を登録
- ✅ RustExtractor（AI使用）がf₀₃⁻¹を実装
- ⚠️ execute_transform()がRust AST分析のみ実装
- ⚠️ ProtoExtractor、DocExtractorが逆写像として統合されていない
- ❌ construct_u0()が自動的に呼ばれない

## 改善タスク

### Task 1: execute_transform()に他の抽出器を統合

現在：
```rust
TransformStrategy::ASTAnalysis { language, .. } => {
    if language == "rust" { /* 実装済み */ }
}
TransformStrategy::TypeAnalysis { .. } => { Ok(Vec::new()) } // 未実装
```

改善：
```rust
TransformStrategy::TypeAnalysis { type_system } => {
    if type_system == "proto" {
        self.execute_proto_extraction(config, graph)
    }
}
TransformStrategy::NLPInference { .. } => {
    self.execute_doc_extraction(config, graph)
}
```

### Task 2: 自動的なU0再構築

現在：明示的にCLIコマンド実行が必要

改善：SpecRepository::ingest()後に自動的にU0を再構築
```rust
impl SpecRepository {
    pub fn ingest_with_u0_update(&mut self, specs: Vec<InferredSpecification>) -> IngestionReport {
        let report = self.ingest(specs);

        // U0を自動的に再構築
        let mut udaf = UDAFModel::new();
        ModelSync::sync_from_repository(&mut udaf, self)?;
        let u0_specs = udaf.construct_u0(self)?;

        // U0仕様をグラフに追加
        self.ingest(u0_specs);

        report
    }
}
```

### Task 3: 逆写像の完全性検証

すべての投影宇宙に対して適切な逆写像が存在するか検証：
```rust
impl UDAFModel {
    pub fn validate_inverse_mappings(&self) -> Result<(), String> {
        for universe_id in self.universes.keys() {
            if universe_id.layer() == 0 { continue; }

            let inverse_id = TransformId::inverse(universe_id);
            if !self.transforms.contains_key(&inverse_id) {
                return Err(format!("Missing inverse mapping for {}", universe_id.as_str()));
            }
        }
        Ok(())
    }
}
```

## 理論的整合性の確認

### U0の特別性

U0は他の宇宙と異なり：
1. **ユーザーが直接書くものではない**：U1〜Unの逆写像から構築
2. **荒めの近似**：完全な根の仕様（定義不可能）の写像
3. **統制の基準**：多層防御を統制する共通参照点

### 現在の実装の妥当性

- `Universe::root()` は「逆写像から構築される」という説明を含む ✅
- `construct_u0()` は理論通り「∪ f₀ᵢ⁻¹(Ui)」を実装 ✅
- 各抽出器は適切な逆写像（f₀₁⁻¹、f₀₂⁻¹、f₀₃⁻¹）を提供 ✅

## 実装優先度

1. **高**: Task 2（自動的なU0再構築）
   - これがないと逆写像エンジンとして機能しない
2. **中**: Task 1（他の抽出器の統合）
   - Proto、Docsなど多様な成果物から抽出できるようにする
3. **低**: Task 3（検証機能）
   - 開発時の品質保証

## 参照

- CLAUDE.md: "specORACLE is a reverse mapping engine"
- docs/motivation.md: 逆写像の必要性と役割
- docs/conversation.md: UDA/f理論
