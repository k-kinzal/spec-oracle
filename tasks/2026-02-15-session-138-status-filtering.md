# Session 138: Status Filtering in Query Commands

**Date**: 2026-02-15
**Session**: 138
**Status**: ✅ Complete

## Objective

Implement `--status` filtering in query commands to allow users to filter specifications by lifecycle status (active/deprecated/archived).

## Background

Session 136-137 implemented lifecycle management (`spec activate`, `spec deprecate`, `spec archive`). The `spec check` command now respects lifecycle status. However, query commands (`spec find`, `spec api list-nodes`) do not yet support filtering by status.

## Requirements

### 1. `spec find` Command ✅

Add `--status` option to filter search results:
```bash
spec find "password" --status active
spec find "authentication" --status deprecated
spec find "old feature" --status archived
```

### 2. `spec api list-nodes` Command ✅

Add `--status` option to filter node listing:
```bash
spec api list-nodes --status active
spec api list-nodes --status deprecated --full
spec api list-nodes --status archived --kind constraint
```

### 3. Self-Governance Specifications

Add specifications documenting this functionality:
- Find command supports status filtering
- List-nodes command supports status filtering

## Implementation Plan

1. ✅ Create task document (this file)
2. ✅ Modify `spec-cli/src/commands/find.rs`
   - Add `status` parameter to `execute_find_standalone()`
   - Add status filtering logic
   - Update filter display
3. ✅ Modify `spec-cli/src/commands/api.rs`
   - Add `status` parameter to list-nodes execution
   - Add status filtering logic
   - Add "By Status" section to summary
   - Update help text
4. ✅ Update CLI argument parsing in `main.rs`/`dispatcher.rs`
   - Added `status` field to Find command
   - Added `status` field to API::ListNodes command
   - Updated dispatcher to pass status parameter
5. ✅ Test functionality
   - `spec find "password" --status active` ✅
   - `spec api list-nodes --status deprecated --full` ✅
   - Combined filters: `spec find "check" --status active --layer 0` ✅
6. ✅ Add self-governance specifications
   - [0a9c5e9d] Find command status filtering
   - [19bc87a4] List-nodes command status filtering
   - Connected to [4cf50a75] lifecycle spec via Refines edges
7. 🔄 Commit changes

## Expected Outcome

Users can filter specifications by lifecycle status in all query commands, improving usability and allowing focus on active/deprecated/archived specs as needed.

## Testing

```bash
# Test find with status filter
./target/release/spec find "password" --status active
./target/release/spec find "password" --status deprecated

# Test list-nodes with status filter
./target/release/spec api list-nodes --status active
./target/release/spec api list-nodes --status deprecated --full

# Combined filters
./target/release/spec find "authentication" --status active --layer 0
./target/release/spec api list-nodes --status active --kind constraint
```

## Related Issues

- Session 137 Next Steps: Status filtering in query commands
- PROBLEM.md: 仕様のライフサイクル管理 (partial - query filtering)

## Files Modified

- ✅ `spec-cli/src/commands/find.rs` - Added status filtering
- ✅ `spec-cli/src/commands/api.rs` - Added status filtering and "By Status" summary
- ✅ `spec-cli/src/commands/dispatcher.rs` - Updated all dispatchers to pass status
- ✅ `spec-cli/src/main.rs` - Added status field to command definitions
- ✅ `.spec/nodes/` - 2 new specifications
- ✅ `.spec/edges.yaml` - 2 new Refines edges

## Results

### Specification Count
- Before: 240 specs
- After: 242 specs (+2)
- New specs:
  - [0a9c5e9d] Find command status filtering
  - [19bc87a4] List-nodes command status filtering

### Status
- ✅ Zero contradictions
- ✅ Zero isolated specs
- ✅ All tests passed

### Testing Results

```bash
# Find with status filter
$ ./target/release/spec find "password" --status active
Found 2 specification(s) matching 'password':
  1. [5fb5017a] [U0] definition - "Password must be >= 8 chars"
  2. [c2f9b469] [U0] definition - Session 103 verified Z3 integration
(Filtered by: status: active)

# List-nodes with status filter
$ ./target/release/spec api list-nodes --status deprecated --full
Found 1 node(s):
  [U3] [b6face50] Scenario - detect semantic contradiction password length
(Filtered by: status: deprecated)

# Combined filters
$ ./target/release/spec find "check" --status active --layer 0
Found 10 specification(s) matching 'check':
  ...
(Filtered by: layer U0, status: active)

# Summary shows status breakdown
$ ./target/release/spec api list-nodes --status active
📊 Specification Summary
Total: 239 specifications
By Status:
  active: 239
```
