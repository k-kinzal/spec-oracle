# Session 67: Show Layer Labels for All Specifications in Search Results

**Date**: 2026-02-14
**Status**: ✅ Completed

## Problem

**Issue from PROBLEM.md (High Priority)**:
- **検索結果に層情報が表示されない** (Search results don't show layer information)
- **詳細**: `spec query "omission"`で24件ヒットするが、自然言語仕様（U0）とコード仕様（U3）が混在していて区別できない。

Users couldn't distinguish specifications at different formality layers (U0/U1/U2/U3) when viewing search results or listing specifications.

## Solution

Added formality layer labels `[U0]`, `[U1]`, `[U2]`, `[U3]` to all specification output commands:

### Changed Commands

1. **query command** (server mode) - `/spec-cli/src/main.rs:1796-1806`
   - Before: `[id] kind - content`
   - After: `[U0] [id] kind - content`

2. **list-nodes command** (server mode) - `/spec-cli/src/main.rs:1730-1742`
   - Before: `[id] kind - content`
   - After: `[U0] [id] kind - content`

3. **list-nodes command** (standalone mode) - `/spec-cli/src/main.rs:576-593`
   - Before: `[id] kind - content`
   - After: `[U0] [id] kind - content`

4. **find command** - Already had layer labels, verified working

### Implementation Details

Used existing `format_formality_layer(u8) -> String` function:
- Maps `0 → "U0"`, `1 → "U1"`, `2 → "U2"`, `3 → "U3"`
- Consistent with conversation.md U/D/A/f model
- Works for both `proto::SpecNode` (server) and `SpecNodeData` (standalone)

## Results

### Before
```
Found 122 node(s):
  [257745aa] assertion - Test specification for standalone mode
  [9e1a2dce] assertion - specORACLE manages multi-layered specifications...
  [141cf3b5] constraint - DetectContradictions RPC returns...
```

### After
```
Found 122 node(s):
  [U0] [257745aa] assertion - Test specification for standalone mode
  [U0] [9e1a2dce] assertion - specORACLE manages multi-layered specifications...
  [U2] [141cf3b5] constraint - DetectContradictions RPC returns...
```

### Find Command Example
```
$ spec find "contradiction"
Found 10 specification(s) matching 'contradiction':
  1. [81afa3f5] [U0] constraint - The system must detect contradictions...
  2. [141cf3b5] [U2] constraint - DetectContradictions RPC returns...
  3. [386b1821] [U3] constraint - The detect_contradictions function...
```

Users can now clearly see:
- **U0** = Natural language requirements
- **U2** = gRPC interface specifications
- **U3** = Implementation specifications

## Files Changed

- `spec-cli/src/main.rs` (3 locations updated)

## Build Notes

Build requires Z3 headers and libraries:
```bash
Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h \
RUSTFLAGS="-L /opt/homebrew/lib" \
cargo build --release -p spec-cli
```

## Specification Added

Added spec to track this implementation:
```
[ab5e4dd1] assertion - Search result output (query and list-nodes commands)
displays formality layer labels [U0], [U1], [U2], [U3] to help users
distinguish specifications at different abstraction levels
```

## Impact

- ✅ Resolves high-priority issue from PROBLEM.md
- ✅ Improves UX for multi-layer specification management
- ✅ Consistent with conversation.md theoretical model
- ✅ Works in both server and standalone modes
- ✅ No breaking changes (only adds information to output)

## Next Steps

This addresses one of the high-priority UX issues. Remaining high-priority issues:
- spec-cliが継ぎ足し実装の集合になっており体系化された操作モデルとHuman Friendlyな体験が崩壊している
- 仕様からドキュメントを生成・可視化できない
- 仕様の検索・探索機能が貧弱
