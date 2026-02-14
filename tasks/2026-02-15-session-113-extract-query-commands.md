# Session 113: Extract Query/Search Commands - CLI Refactoring Phase 2

## Objective

Continue CLI architecture refactoring to resolve the self-detected violation detected by specORACLE's governance system.

## What Was Done

Extracted Query, Find, and Trace commands from main.rs to separate modules, completing Phase 2 of the CLI refactoring roadmap.

## Changes

### Files Created
- `spec-cli/src/commands/query.rs` (95 lines)
  - `execute_query_standalone()` - semantic search in standalone mode
  - `execute_query_server()` - gRPC query implementation
  - AI-enhanced query support

- `spec-cli/src/commands/find.rs` (118 lines)
  - `execute_find_standalone()` - keyword search with layer filtering
  - `execute_find_server()` - server-mode find via Query RPC
  - Layer filtering and result limiting

- `spec-cli/src/commands/trace.rs` (181 lines)
  - `execute_trace_standalone()` - relationship tracing with depth control
  - `execute_trace_server()` - server-mode direct relationship display
  - Short ID resolution support

### Files Modified
- `spec-cli/src/main.rs`: 4046 → 3736 lines (**-310 lines, 7.7% reduction**)
- `spec-cli/src/commands/mod.rs`: Added module exports for query, find, trace
- `PROBLEM.md`: Fixed U/D/A/f model documentation inconsistency

## Impact

**Line Reduction**: 310 lines removed from main.rs in this session

**Cumulative Progress**:
- Session 110-112: -300 lines (Presentation, Persistence, Utils, Contradictions, Omissions)
- Session 113: -310 lines (Query, Find, Trace)
- **Total: -610 lines from original 4046** (15.1% reduction)
- **From initial 4475 lines: -739 lines** (16.5% toward <500 target)

**Module Structure**:
```
spec-cli/src/commands/
├── add.rs (93 lines)
├── check.rs (130 lines)
├── contradictions.rs (128 lines)
├── omissions.rs (53 lines)
├── query.rs (95 lines)
├── find.rs (118 lines)
├── trace.rs (181 lines)
└── mod.rs (21 lines)

Total: 819 lines in commands modules
```

**Separation of Concerns**: Query/search operations now in dedicated modules
- Clear boundaries between search strategies
- Both standalone/server modes supported
- Easier to test in isolation

## Testing

✅ All 71 tests passed
✅ `spec check` works correctly
✅ `spec find "contradiction" --layer 0` works with layer filtering
✅ Commands maintain identical behavior
✅ Zero behavioral changes, pure refactoring

## Technical Details

**Proto Compatibility**:
- No dedicated `FindRequest` or `TraceRequest` in proto
- Server mode reuses `QueryRequest` for Find command
- Server mode uses `ListEdgesRequest` for Trace command (direct relationships only)

**Type Corrections**:
- Fixed `depth` parameter type mismatch (usize vs u32)
- Ensured consistency with Commands enum definitions

**Documentation Fix**:
- Corrected PROBLEM.md entry for U/D/A/f model
- Added verification results showing the model is fully implemented and functional

## Self-Governance Status

Current contradiction detected by specORACLE:
```
⚠️  1 contradiction(s) found
A: [d26341fb] The CLI architecture (spec-cli/src/main.rs at 4475 lines) violates separation of concerns
B: [b706e529] The CLI implementation must separate concerns...
```

**Note**: The violation mentions "4475 lines" but current state is 3736 lines. The specification needs updating to reflect progress.

**Progress toward resolution**:
- Original: 4475 lines
- Current: 3736 lines (16.5% reduction)
- Target: <500 lines (90% reduction needed)
- **Still 3236 lines to extract**

## Next Steps

**Phase 3**: Extract construction commands (350-400 lines estimated)
- Commands::Extract
- Commands::ConstructU0
- Commands::InferRelationships
- Commands::InferAllRelationshipsWithAi

**Phase 4**: Extract utility commands (200-250 lines estimated)
- Commands::Summary
- Commands::Init
- Commands::Watch
- Commands::CleanupLowQuality

**Phase 5**: Extract deprecated API commands (1500+ lines estimated)
- Commands::AddNode, AddEdge, GetNode, ListNodes, ListEdges
- Commands::RemoveNode, RemoveEdge
- Commands::VerifyLayers, ResolveTerm, etc.

**Phase 6**: Final cleanup and verification
- Extract remaining command handlers
- Verify self-governance: run `spec check` to confirm violation resolved
- Update the CLI architecture specification

## Commit

```
03bf663 Session 113: Extract Query, Find, and Trace commands
```

## Status

✅ **Phase 2 Complete** - Query/search commands extracted
📍 **Next**: Phase 3 - Construction commands
