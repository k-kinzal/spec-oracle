# Session 128: Enhance list-edges Command to Show Node Content

**Date**: 2026-02-15
**Status**: ✅ Completed

## Problem

The `spec api list-edges` command only displayed shortened UUIDs (8 characters) without showing what the nodes actually contain. This made it difficult for users to understand relationships between specifications.

**Before**:
```bash
$ spec api list-edges --node <id>
Found 21 edge(s):
  81afa3f5 --[Refines]--> f6953636
  41052fda --[DerivesFrom]--> 81afa3f5
  ...
```

Users had to manually look up each UUID to understand what specifications were being connected.

## Solution

Enhanced `execute_list_edges_standalone` function in `spec-cli/src/commands/api.rs` to show:
- Formality layer ([U0], [U1], [U2], [U3])
- Node kind (Constraint, Assertion, Scenario, etc.)
- Content preview (50 characters with "..." if truncated)
- Clear edge direction (source → edge → target)

**After**:
```bash
$ spec api list-edges --node <id>
Found 21 edge(s):

  [U0] [81afa3f5] Constraint - The system must detect contradictions between spec...
    --[Refines]-->
  [U0] [f6953636] Scenario - Specifications can be refined across layers using ...

  [U2] [41052fda] Constraint - AddNode RPC accepts content, kind, and metadata to...
    --[DerivesFrom]-->
  [U0] [81afa3f5] Constraint - The system must detect contradictions between spec...
```

## Implementation

Modified `spec-cli/src/commands/api.rs`:
- Lines 167-186: `execute_list_edges_standalone` function
- For each edge:
  1. Retrieve source node from graph
  2. Display source with layer, kind, and content preview
  3. Display edge kind
  4. Retrieve target node from graph
  5. Display target with layer, kind, and content preview

## Results

**Usability improvement**:
- Users can now understand relationships at a glance
- No need to manually look up UUIDs with `get-node`
- Multi-layer relationships are clearly visible
- Edge direction is unambiguous

**Example output showing multi-layer formalization**:
```bash
  [U0] [81afa3f5] Constraint - The system must detect contradictions...
    --[Formalizes]-->
  [U3] [386b1821] Constraint - The detect_contradictions function must...
```

This clearly shows U0 (requirement) being formalized into U3 (implementation).

## Verification

Tested with multiple nodes:
- Node with 21 edges: ✅ Shows all edges with full context
- All edges (274 total): ✅ Works correctly
- Node with 0 edges: ✅ Shows "Found 0 edge(s)"

## Compliance

- ✅ CLAUDE.md: Smallest possible commit unit
- ✅ CLAUDE.md: Work recorded in tasks directory
- ✅ PROBLEM.md: Resolves "list-edges がUUIDしか表示せず、内容が分からない"
- ✅ No ad-hoc scripts committed
- ✅ Behavior verified through testing

## Impact

This enhancement significantly improves the usability of the `list-edges` command, making it practical for users to explore and understand specification relationships. The improved output format is consistent with other high-level commands like `get-node` and `trace`.

## Related

- Issue: PROBLEM.md - "list-edgesがUUIDしか表示せず、内容が分からない" (Medium priority)
- Files modified: `spec-cli/src/commands/api.rs`
- Builds on: Session 123's `get-node` enhancement (used as design reference)
