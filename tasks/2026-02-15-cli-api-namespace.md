# Session 101: Introduce `spec api` Namespace for Low-Level Commands

**Date**: 2026-02-15
**Goal**: Implement specification [c6119c42] - CLI coherent layered command structure

## Problem

The CLI had 40+ commands all at the same level, mixing intent-level commands (add, check, find, trace) with low-level graph operations (add-node, get-node, list-nodes, add-edge, etc.). This violated specification [c6119c42]:

> The CLI must provide a coherent, layered command structure where intent-level commands (add, check, find, trace) are primary and low-level graph operations (add-node, add-edge) are isolated under 'spec api' namespace

## Solution

Introduced `spec api` namespace to isolate low-level graph API operations:

### 1. Created `ApiCommands` enum

Moved 15 low-level commands to `ApiCommands`:
- `add-node`, `get-node`, `list-nodes`, `remove-node`
- `add-edge`, `list-edges`, `remove-edge`
- `set-universe`, `filter-by-layer`
- `generate-contract`, `check-compliance`
- `query-at-timestamp`, `diff-timestamps`, `node-history`, `compliance-trend`

### 2. Added `Api` subcommand to `Commands`

```rust
Commands::Api(ApiCommands)
```

### 3. Deprecated old commands

- Marked old top-level commands as `#[command(hide = true)]`
- Added deprecation warnings when used
- Preserved backward compatibility

### 4. Implemented for both modes

- **Standalone mode**: Direct FileStore access
- **Server mode**: gRPC client calls
- Unified behavior across both modes

## Results

**Before**:
```bash
$ spec --help
Commands:
  add, add-node, get-node, list-nodes, remove-node, add-edge, list-edges, ...
  (40+ commands in flat structure)
```

**After**:
```bash
$ spec --help
Commands:
  add         Add a specification (high-level)
  api         Low-level graph API operations (for advanced users)
  check       Check specifications for issues
  find        Find specifications by semantic search
  trace       Trace specification relationships
  ...
  (Intent-level commands primary)

$ spec api --help
Commands:
  add-node, get-node, list-nodes, remove-node, add-edge, list-edges, ...
  (Low-level operations isolated)
```

**Deprecation warning**:
```bash
$ spec list-nodes
⚠️  WARNING: 'spec list-nodes' is deprecated. Use 'spec api list-nodes' instead.
   The command will still work but may be removed in a future version.
```

## Verification

```bash
# New API namespace works
$ spec api list-nodes --kind constraint
Found 29 node(s):
  [U0] [81afa3f5] constraint - The system must detect contradictions...

# High-level commands still work
$ spec check
✅ All checks passed! No issues found.

# Deprecated commands show warning
$ spec list-nodes
⚠️  WARNING: 'spec list-nodes' is deprecated. Use 'spec api list-nodes' instead.
```

## Implementation Details

**Files modified**:
- `spec-cli/src/main.rs`:
  - Added `ApiCommands` enum (line 25-110)
  - Added `Commands::Api` variant
  - Implemented handlers for standalone mode (line 705-825)
  - Implemented handlers for server mode (line 2317-2602)
  - Deprecated old commands with warnings

**Technical challenges**:
1. **Borrow checker issues**: Fixed by cloning values before saving graph
2. **Method API differences**: Used `list_edges(Option<&str>)` instead of separate methods
3. **Type casting**: Added `as u8` casts for `formality_layer`

## Alignment with Specifications

This implementation satisfies:
- ✅ **[c6119c42]**: CLI coherent layered structure achieved
- ✅ **[c6920b06]**: Human-friendly UX - minimum input for goal achievement
- 🔄 **[b706e529]**: Separation of concerns - partial (command structure improved, but main.rs still large)

## Next Steps

**Phase 2** (Future): Separate concerns within main.rs
- Extract command handlers to separate modules
- Separate presentation layer
- Isolate persistence routing
- Modularize AI integration

**Phase 3** (Future): UX improvements
- Add interactive mode for complex operations
- Improve error messages with actionable guidance
- Add command suggestions when user makes mistakes

## Metrics

- **Commands reorganized**: 15 commands moved to `spec api`
- **User impact**: Cleaner help text, better discoverability
- **Backward compatibility**: 100% preserved (with deprecation warnings)
- **Code size**: No significant change (~4035 lines, structure improved)
