# Session 67: Show Layer Labels for All Specifications (2026-02-14)

## Objective
Fix the issue where U0 specifications don't show layer labels in `spec find` output.

## Problem (PROBLEM.md)
- **Issue**: "検索結果に層情報が表示されない" (Search results don't show layer information)
- **Symptom**: U0 specs appeared without `[U0]` labels, while U2/U3 specs showed `[U2]`/`[U3]`
- **Root cause**: Code only displayed labels when `formality_layer > 0`, skipping U0

## Solution
Modified `spec-cli/src/main.rs` to display layer labels for all specifications:

**Before:**
```rust
let layer_str = if let Some(l) = node.metadata.get("formality_layer") {
    format!(" [U{}]", l)
} else if node.formality_layer > 0 {
    format!(" [U{}]", node.formality_layer)
} else {
    String::new()  // ← U0 specs got empty string
};
```

**After:**
```rust
let layer_str = if let Some(l) = node.metadata.get("formality_layer") {
    format!(" [U{}]", l)
} else {
    format!(" [U{}]", node.formality_layer)  // ← Now shows [U0] for layer 0
};
```

## Additional Fixes
Fixed type mismatches for proto-based server mode:
- `node.formality_layer` is `u32` in proto
- `parse_formality_layer()` expects `u8`
- Added explicit casts: `node.formality_layer as u8`

## Result

**Before:**
```
1. [b176641e] constraint - The trace command displays...  (no layer label)
2. [8c2c0d20] [U3] constraint - The trace command must...
```

**After:**
```
1. [b176641e] [U0] constraint - The trace command displays...
2. [8c2c0d20] [U3] constraint - The trace command must...
```

## Verification
```bash
$ ./target/release/spec find "trace" | head -5
Found 9 specification(s) matching 'trace':

  1. [b176641e] [U0] constraint - ...
  2. [93651986] [U0] scenario - ...
  3. [88a7937e] [U0] scenario - ...
```

All specifications now show clear layer labels `[U0]`, `[U2]`, or `[U3]`.

## Impact
- **User Experience**: Users can immediately see which formality layer each spec belongs to
- **Layer Filtering**: The existing `--layer` option now makes more sense with visible labels
- **Traceability**: Easier to understand multi-layer specification chains

## Status
✅ **Resolved** - High priority issue from PROBLEM.md
