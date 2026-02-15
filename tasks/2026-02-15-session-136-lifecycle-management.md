# Session 136: Implement Specification Lifecycle Management

**Date**: 2026-02-15
**Session**: 136
**Status**: ✅ Complete

## Goal

Implement lifecycle management for specifications to enable better long-term maintenance. This addresses multiple issues from PROBLEM.md:
- 仕様のライフサイクル管理ができない
- 古い仕様を識別できない
- 仕様の変更履歴・バージョン管理がない (partially)

## Implementation

### 1. Added Lifecycle Commands

Created three new commands in the CLI:

1. **`spec archive <id>`** - Mark a specification as archived
   - Sets `metadata.status = "archived"`
   - Specification kept for history but excluded from checks

2. **`spec deprecate <id>`** - Mark a specification as deprecated
   - Sets `metadata.status = "deprecated"`
   - Specification still checked but shows warnings

3. **`spec activate <id>`** - Mark a specification as active
   - Sets `metadata.status = "active"`
   - Removes lifecycle restrictions

### 2. Files Modified

- `spec-cli/src/main.rs`: Added command definitions to Commands enum
- `spec-cli/src/commands/lifecycle.rs`: New module with implementation
- `spec-cli/src/commands/mod.rs`: Added lifecycle module export
- `spec-cli/src/commands/dispatcher.rs`: Added command routing

### 3. Implementation Details

The lifecycle status is stored in the `metadata` field of SpecNodeData:
- Uses existing `update_node_metadata()` API
- Status values: "active", "deprecated", "archived"
- Backward compatible (specs without status are treated as active)

### 4. Testing

Verified all three commands:
```bash
$ ./target/release/spec archive 5fb5017a
✓ Specification [5fb5017a] marked as archived

$ ./target/release/spec deprecate b6face50
✓ Specification [b6face50] marked as deprecated

$ ./target/release/spec activate 5fb5017a
✓ Specification [5fb5017a] activated
```

Metadata correctly updated in YAML files:
```yaml
metadata:
  status: archived  # or deprecated, or active
```

## Next Steps

1. **Update `spec check` command** to respect lifecycle status:
   - Skip archived specifications
   - Show warnings for deprecated specifications

2. **Add status filtering** to query commands:
   - `spec find --status active`
   - `spec api list-nodes --status deprecated`

3. **Update summary command** to show status breakdown:
   - Active: N specs
   - Deprecated: M specs
   - Archived: K specs

4. **Documentation** in README and CLI help

## Benefits

- **Old specifications can be archived** instead of deleted
- **Deprecated specifications are marked** for future removal
- **Active specifications are clearly identified**
- **History is preserved** (archived specs kept but not checked)
- **Backward compatible** (existing specs without status work as before)

## Related Issues

From PROBLEM.md:
- ✅ 仕様のライフサイクル管理ができない (Solved: basic lifecycle)
- ⏳ 古い仕様を識別できない (Partially: deprecated/archived status)
- ⏳ 仕様の変更履歴・バージョン管理がない (Future: version tracking)

## Notes

- Status is stored in metadata, not as a dedicated field
- This allows for easy future extension (e.g., adding more statuses)
- No database migration required
- Compatible with existing YAML storage format

## Completion Summary

✅ **Phase 1 Complete** (2026-02-15)
- ✅ Three lifecycle commands implemented and tested
- ✅ Specifications added for self-governance
- ✅ Zero contradictions, zero isolated specs maintained
- ✅ Two commits created:
  1. `0a2ed90`: Implementation
  2. `0be5103`: Self-governance specifications

**Final State**:
- Total specs: 238 (4 new)
- Relationships: 255 edges (4 new)
- Health: ✅ All checks passed

**Remaining Work** (Future sessions):
- Update `spec check` to skip archived specs
- Add status filtering to query commands
- Update summary to show status breakdown
- Add CLI documentation
