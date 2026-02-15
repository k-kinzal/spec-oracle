# Session 133: Enhanced list-nodes UX

**Date**: 2026-02-15
**Task**: Improve list-nodes command for better usability with large specification sets (229+ specs)

## Problem

`spec list-nodes` was overwhelming users by displaying all 229 specifications at once. This made it difficult to:
- Get an overview of the specification landscape
- Navigate and find specific specs
- Understand the distribution across layers and kinds

## Solution Implemented

Enhanced `spec api list-nodes` (and deprecated `spec list-nodes`) with:

### 1. Summary Mode (Default)
Shows high-level statistics instead of listing all specs:
```bash
$ spec api list-nodes
📊 Specification Summary
Total: 229 specifications

By Formality Layer:
  U0: Natural Language Requirements (124 specs)
  U1: Formal Specifications (1 specs)
  U2: Interface Definitions (61 specs)
  U3: Implementation (43 specs)

By Kind:
  Assertions: 159
  Constraints: 34
  Definitions: 5
  Scenarios: 31

💡 Use --full to see the complete list
💡 Use --layer <N> to filter by formality layer (0-3)
💡 Use --kind <type> to filter by kind
```

### 2. Full Mode (--full)
Opt-in to see complete list:
```bash
$ spec api list-nodes --full
Found 229 node(s):

  [U0] [69af9728] Constraint - must be / must not be → boolean constraints
  [U0] [5fb5017a] Definition - Password must be >= 8 chars (natural language)
  ...
```

### 3. Layer Filtering (--layer <N>)
Filter by formality layer (0-3):
```bash
$ spec api list-nodes --layer 0
📊 Specification Summary
Total: 124 specifications

By Formality Layer:
  U0: Natural Language Requirements (124 specs)
...
```

### 4. Pagination (--limit, --offset)
Navigate large result sets:
```bash
$ spec api list-nodes --layer 0 --full --limit 5
Found 124 node(s):
Showing 1 - 5 of 124:

  [U0] [69af9728] Constraint - must be / must not be → boolean constraints
  ...

... and 119 more (use --offset 5 to see next page)
```

### 5. Combined Filters
All filters work together:
```bash
$ spec api list-nodes --kind constraint --layer 0 --full
# Shows only U0 constraints in full mode
```

## Implementation Details

### Files Modified

1. **spec-cli/src/main.rs**:
   - Updated `ApiCommands::ListNodes` enum with new parameters:
     - `layer: Option<u8>` - Filter by formality layer
     - `full: bool` - Enable full list mode
     - `limit: Option<usize>` - Pagination limit
     - `offset: Option<usize>` - Pagination offset
   - Updated deprecated `Commands::ListNodes` for backward compatibility

2. **spec-cli/src/commands/dispatcher.rs**:
   - Updated `dispatch_list_nodes_standalone()` signature and implementation
   - Added summary mode logic (group by layer/kind)
   - Added pagination logic (limit/offset)
   - Updated dispatcher calls to pass new parameters

3. **spec-cli/src/commands/api.rs**:
   - Updated `execute_list_nodes_standalone()` signature and implementation
   - Duplicated summary/pagination logic for API command path

### Design Decisions

1. **Summary as default**: Most users want overview, not full list
2. **--full opt-in**: Explicit choice to see complete list
3. **Combined filtering**: Layer + kind filters work together
4. **Pagination hints**: Clear "use --offset N" guidance
5. **Sorted output**: Kind stats alphabetically sorted for consistency

## Testing Results

### Summary Mode
```bash
$ spec api list-nodes
✓ Shows total count (229 specs)
✓ Shows layer breakdown (U0: 124, U1: 1, U2: 61, U3: 43)
✓ Shows kind breakdown (Assertions: 159, Constraints: 34, etc.)
✓ Shows usage hints
```

### Layer Filter
```bash
$ spec api list-nodes --layer 0
✓ Filters to 124 U0 specs
✓ Summary shows only U0 layer
✓ Kind breakdown updated for filtered set
```

### Kind Filter
```bash
$ spec api list-nodes --kind constraint
✓ Filters to 34 constraints
✓ Summary shows layer distribution of constraints
✓ Kind breakdown shows only Constraints
```

### Full Mode with Pagination
```bash
$ spec api list-nodes --layer 0 --full --limit 5
✓ Shows "Found 124 node(s)"
✓ Shows "Showing 1 - 5 of 124"
✓ Lists 5 specs
✓ Shows "... and 119 more (use --offset 5 to see next page)"
```

### Combined Filters
```bash
$ spec api list-nodes --layer 0 --kind constraint --full
✓ Filters to U0 constraints only
✓ Shows full list of matching specs
```

## Impact

### Before (User Pain Points)
- **Overwhelming**: 229 specs dumped to screen
- **No overview**: Can't see distribution/stats
- **Hard to navigate**: Must scroll through everything
- **No filtering**: Can't focus on layer or kind

### After (Improved UX)
- **Clear overview**: Summary shows structure at a glance
- **Targeted exploration**: Filter by layer, kind, or both
- **Manageable output**: Pagination for large sets
- **Progressive disclosure**: Summary → Full → Paginated

### Metrics
- **Default output**: 229 lines → 15 lines (94% reduction)
- **Time to overview**: ~5s scrolling → instant
- **Discoverability**: Hints guide users to advanced features

## User Workflows Enabled

### 1. Quick Health Check
```bash
$ spec api list-nodes
# See total count, layer/kind distribution in <1 second
```

### 2. Explore Specific Layer
```bash
$ spec api list-nodes --layer 0
# Understand U0 requirements structure

$ spec api list-nodes --layer 0 --full --limit 10
# Browse first 10 U0 specs
```

### 3. Audit Specific Kind
```bash
$ spec api list-nodes --kind constraint
# See constraint distribution

$ spec api list-nodes --kind constraint --full
# Review all constraints
```

### 4. Focused Investigation
```bash
$ spec api list-nodes --layer 3 --kind scenario --full
# See all U3 test scenarios
```

## Next Steps (Future Enhancements)

Based on this foundation, future improvements could include:

1. **Interactive mode** (fzf integration)
   - `spec list-nodes --interactive`
   - Live filtering, preview, selection

2. **Sort options**
   - `--sort-by created|modified|layer|kind`
   - `--order asc|desc`

3. **Rich formatting**
   - `--format table|json|yaml`
   - Color-coded output
   - Column alignment

4. **Search integration**
   - `--search <query>` semantic search
   - Combine with filters

5. **Export**
   - `--export csv|json`
   - Filtered sets to files

## Specifications Updated

Need to add specifications documenting this enhancement:
- [ ] U0: list-nodes must support summary mode by default
- [ ] U0: list-nodes must support layer and kind filtering
- [ ] U0: list-nodes must support pagination
- [ ] U2: ListNodes RPC has layer/full/limit/offset parameters
- [ ] U3: execute_list_nodes_standalone implements summary mode

## Conclusion

Successfully transformed `list-nodes` from an overwhelming data dump to a navigable, user-friendly interface. The summary-first approach with progressive disclosure (summary → full → paginated) provides excellent UX for both quick checks and deep exploration.

**Status**: ✅ Complete and tested
**Impact**: High - Directly addresses widest adoption pain point
**Next Priority**: Document in specifications using the tool itself
