# Session 137: Lifecycle-Aware Check Command

**Date**: 2026-02-15
**Session**: 137
**Status**: ✅ Complete

## Goal

Implement lifecycle-aware checking functionality to respect specification lifecycle status (active/deprecated/archived) in the `spec check` command. This continues the work from Session 136 on lifecycle management.

## Implementation

### 1. Enhanced Check Command

Modified `spec-cli/src/commands/check.rs` to:

1. **Filter specifications by lifecycle status**:
   - Active: No status metadata or `status = "active"`
   - Deprecated: `status = "deprecated"`
   - Archived: `status = "archived"`

2. **Exclude archived specs from checks**:
   - Contradiction detection only considers active and deprecated specs
   - Omission detection only considers active and deprecated specs
   - Extracted specs percentage calculated based on active specs only

3. **Enhanced summary display**:
   - Shows total specs count (all specs)
   - Shows active specs count
   - Shows deprecated specs count (with ⚠️ warning symbol)
   - Shows archived specs count (with note "excluded from checks")
   - Updated extracted specs percentage (based on active specs)

4. **Deprecated specs warning section**:
   - Lists up to 5 deprecated specifications
   - Shows spec ID (first 8 chars) and content preview (60 chars)
   - Provides recommendation: "Consider updating or archiving these specifications"

### 2. Files Modified

- `spec-cli/src/commands/check.rs`: Enhanced check command implementation

### 3. Testing

Verified functionality with:
```bash
# Initial state: 238 specs (237 active, 1 deprecated)
$ ./target/release/spec check
📊 Summary:
  Total specs:        238
  Active specs:       237
  Deprecated specs:   ⚠️  1
  Extracted specs:    60 (25.3%)
  ...
⚠️  Deprecated specifications:
  1. [b6face50] Scenario: detect semantic contradiction password length
  💡 Consider updating or archiving these specifications

# Test archiving
$ ./target/release/spec archive 5fb5017a
✓ Specification [5fb5017a] marked as archived

# Verify archived exclusion
$ ./target/release/spec check
📊 Summary:
  Total specs:        238
  Active specs:       236
  Deprecated specs:   ⚠️  1
  Archived specs:     1 (excluded from checks)
  Extracted specs:    59 (25.0%)
  ...

# Restore state
$ ./target/release/spec activate 5fb5017a
✓ Specification [5fb5017a] activated
```

## Benefits

1. **Archived specs excluded**: Archived specs don't affect checks (as intended)
2. **Deprecated specs highlighted**: Clear visibility with warning symbol
3. **Accurate statistics**: Percentages based on active specs only
4. **Actionable recommendations**: Suggests updating or archiving deprecated specs
5. **Backward compatible**: Specs without status metadata treated as active

## Implementation Details

### Status Filtering Logic

```rust
// Archived specs
let archived_nodes: Vec<_> = all_nodes.iter()
    .filter(|n| n.metadata.get("status").map(|s| s.as_str()) == Some("archived"))
    .collect();

// Deprecated specs
let deprecated_nodes: Vec<_> = all_nodes.iter()
    .filter(|n| n.metadata.get("status").map(|s| s.as_str()) == Some("deprecated"))
    .collect();

// Active specs (no status or status="active")
let active_nodes: Vec<_> = all_nodes.iter()
    .filter(|n| {
        let status = n.metadata.get("status").map(|s| s.as_str());
        status.is_none() || status == Some("active")
    })
    .collect();
```

### Deprecated Specs Warning

```rust
if !deprecated_nodes.is_empty() {
    println!("\n⚠️  Deprecated specifications:");
    for (i, node) in deprecated_nodes.iter().take(5).enumerate() {
        println!("  {}. [{}] {}", i + 1, &node.id[..8],
            node.content.chars().take(60).collect::<String>());
    }
    if deprecated_nodes.len() > 5 {
        println!("  ... and {} more", deprecated_nodes.len() - 5);
    }
    println!("  💡 Consider updating or archiving these specifications");
}
```

## Next Steps

Remaining work from Session 136:

1. **Status filtering in query commands** (Next priority):
   - `spec find --status active`
   - `spec find --status deprecated`
   - `spec api list-nodes --status archived`

2. **Documentation** (Lower priority):
   - Update README with lifecycle commands
   - Add CLI help text for lifecycle features
   - Document lifecycle workflow

## Related Issues

From PROBLEM.md:
- ✅ 仕様のライフサイクル管理ができない (Solved: Session 136)
- ✅ 古い仕様を識別できない (Solved: deprecated/archived status with check display)
- ⏳ 仕様の変更履歴・バージョン管理がない (Future work)

## Completion Summary

✅ **Session 137 Complete** (2026-02-15)
- ✅ Lifecycle-aware check implementation
- ✅ Enhanced summary display with status breakdown
- ✅ Deprecated specs warning section
- ✅ Archived specs excluded from checks
- ✅ All tests passing (73 tests)
- ✅ One commit created: `f80a013`

**Final State**:
- Total specs: 238 (237 active, 1 deprecated)
- Contradictions: 0
- Isolated specs: 0
- Health: ✅ All checks passed

**Build Status**:
- Cargo build: ✅ Success
- Test suite: ✅ 73 tests passed
- Warnings: 8 (dead code warnings, non-critical)
