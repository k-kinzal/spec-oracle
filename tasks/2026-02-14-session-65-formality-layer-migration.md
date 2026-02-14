# Session 65: formality_layer Data Model Migration

**Date**: 2026-02-14
**Status**: ✅ Completed

## Problem

Found data model inconsistency where formality_layer was managed in two places:

1. **Node field**: `formality_layer: u8` - Always 0 (unused)
2. **Metadata**: `metadata.formality_layer: String` - Actual values ("U0", "U1", "U2", "U3")

This created confusion and violated single source of truth principle.

**Before Migration**:
```json
{
  "id": "...",
  "content": "...",
  "formality_layer": 0,  // ❌ Unused, always 0
  "metadata": {
    "formality_layer": "U0"  // ✅ Actual value
  }
}
```

## Solution

Migrated all formality_layer data from metadata to the proper field:

**After Migration**:
```json
{
  "id": "...",
  "content": "...",
  "formality_layer": 0,  // ✅ Proper value (0=U0, 1=U1, 2=U2, 3=U3)
  "metadata": {
    // ✅ formality_layer removed
  }
}
```

### Mapping

- `"U0"` → `0` (natural language requirements)
- `"U1"` → `1` (formal specifications)
- `"U2"` → `2` (interface definitions)
- `"U3"` → `3` (executable implementation)

## Implementation

### 1. Data Migration Script

Created `scripts/migrate_formality_layer.py`:

- Reads metadata.formality_layer ("U0", "U1", etc.)
- Converts to numeric values (0, 1, 2, 3)
- Updates node.formality_layer field
- Removes metadata.formality_layer

**Results**:
- ✅ 122 specs migrated
- ✅ 122 metadata entries removed
- ✅ 0 metadata.formality_layer remaining

### 2. Code Updates

Updated `spec-cli/src/main.rs`:

**Before**:
```rust
fn parse_formality_layer(metadata: &HashMap<String, String>, fallback: u8) -> u32 {
    metadata.get("formality_layer")
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(fallback as u32)
}
```

**After**:
```rust
fn parse_formality_layer(formality_layer: u8) -> u32 {
    formality_layer as u32
}

fn format_formality_layer(formality_layer: u8) -> String {
    match formality_layer {
        0 => "U0".to_string(),
        1 => "U1".to_string(),
        2 => "U2".to_string(),
        3 => "U3".to_string(),
        _ => format!("U{}", formality_layer),
    }
}
```

Created `scripts/fix_formality_layer_code.py` to update all call sites:
- All `parse_formality_layer(&node.metadata, node.formality_layer)` → `parse_formality_layer(node.formality_layer)`
- Removed metadata extraction in specd/src/service.rs

## Results

### Layer Distribution

**Before** (field values):
- U0 (layer=0): 106 (86.9%)
- U1 (layer=1): 0
- U2 (layer=2): 7 (5.7%)
- U3 (layer=3): 9 (7.4%)

**After** (migrated from metadata):
- U0 (layer=0): 69 (56.6%)
- U1 (layer=1): 1 (0.8%)
- U2 (layer=2): 37 (30.3%)
- U3 (layer=3): 15 (12.3%)

The "After" distribution is correct - it reflects the actual layer assignments from Session 64.

### Verification

```bash
$ ./target/release/spec check
✓ No contradictions found
⚠️  1 isolated specification (same as before migration)

$ cat .spec/specs.json | jq '[.graph.nodes[] | select(has("metadata") and (.metadata | has("formality_layer")))] | length'
0  # ✅ All metadata.formality_layer removed

$ ./target/release/spec list-nodes
# ✅ All commands work correctly
```

## Impact

- ✅ **Data model consistency**: Single source of truth for formality_layer
- ✅ **Type safety**: Numeric values (0-3) instead of strings
- ✅ **Code simplification**: Removed metadata fallback logic
- ✅ **Correctness**: Layer distribution now reflects actual assignments

## Files Changed

### Scripts
- `scripts/migrate_formality_layer.py` - Data migration
- `scripts/fix_formality_layer_code.py` - Code updates

### Source Code
- `spec-cli/src/main.rs` - Updated parse_formality_layer(), added format_formality_layer()
- `specd/src/service.rs` - Removed metadata extraction

### Data
- `.spec/specs.json` - All 122 specs migrated

## Theoretical Alignment

This fix aligns with:
- **PROBLEM.md**: Resolves "formality_layerの二重管理" (High priority issue)
- **conversation.md**: U/D/A/f model requires clear layer identity
- **CLAUDE.md**: Single source of truth principle

## Next Steps

- ✅ Migration complete
- ⏳ Remaining: Low-priority UX improvements (see PROBLEM.md Medium/Low sections)
