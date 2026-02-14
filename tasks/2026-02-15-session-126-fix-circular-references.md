# Session 126: Fix Circular References in Specification Graph

**Date**: 2026-02-15
**Status**: Completed
**Type**: Bug Fix

## Objective

Fix circular references (self-referencing edges) in the specification graph to ensure graph consistency.

## Context

While investigating remaining issues in PROBLEM.md, discovered that the "circular reference" problem actually manifested as self-referencing edges (nodes pointing to themselves) rather than bidirectional cycles between different nodes.

## Investigation

### Initial Analysis

```bash
$ ./target/release/spec check
Total specs: 247
Contradictions: 0
Isolated specs: 0  # Before fix
✅ All checks passed!
```

### Circular Reference Detection

Found 13 self-referencing edges:
- 11 Formalizes edges (nodes formalizing themselves)
- 2 Refines edges (nodes refining themselves)
- 0 bidirectional cycles (A↔B pattern)

Example invalid edges:
```
ee97d8f2 --[Refines]--> ee97d8f2     (Edge operations)
0e01afc7 --[Refines]--> 0e01afc7     (Node operations)
3c7619aa --[Formalizes]--> 3c7619aa  (RPC spec)
... (10 more)
```

### Root Cause

Proto extraction (Session 97) incorrectly created self-referencing edges for some RPC specifications. These edges are semantically invalid - a specification cannot refine or formalize itself.

## Implementation

### 1. Created Cleanup Script

**File**: `scripts/remove_self_referencing_edges.py`

```python
# Loads .spec/edges.yaml
# Identifies self-referencing edges (source == target)
# Removes them and saves cleaned edges
```

### 2. Executed Cleanup

```bash
$ python3 scripts/remove_self_referencing_edges.py
Total edges: 275
Self-referencing edges to remove: 13
Edges after cleanup: 262
Removed: 13 edges
✅ Self-referencing edges removed successfully!
```

### 3. Validated Graph Integrity

```python
# Check for bidirectional cycles
Refines: No bidirectional cycles ✓
Formalizes: No bidirectional cycles ✓
DerivesFrom: No bidirectional cycles ✓
Contradicts: No bidirectional cycles ✓
```

## Results

### Before Fix
- Total edges: 275
- Self-referencing edges: 13
- Bidirectional cycles: 0
- Isolated specs: 0 (hidden by invalid self-references)

### After Fix
- Total edges: 262
- Self-referencing edges: 0 ✅
- Bidirectional cycles: 0 ✅
- Isolated specs: 9 (revealed by cleanup)

### Side Effects

9 RPC specifications became isolated after removing self-references:
- ListNodes
- RemoveNode
- RemoveEdge
- DetectLayerInconsistencies
- FindFormalizations
- FindRelatedTerms
- GetTestCoverage
- DetectInterUniverseInconsistencies
- SetNodeUniverse

These nodes had ONLY self-references, revealing a data quality issue. They are legitimate specifications that need proper relationships inferred.

## Verification

```bash
$ ./target/release/spec check
Total specs: 247
Contradictions: 0
Isolated specs: 9  # Previously hidden
❌ Critical issues found!
```

The 9 isolated specs are a separate data quality issue, not a regression from this fix.

## Artifacts

- **Script**: `scripts/remove_self_referencing_edges.py`
- **Updated**: PROBLEM.md (marked circular reference issue as resolved)
- **Cleaned**: `.spec/edges.yaml` (262 edges, was 275)

## Next Steps

1. ✅ **Completed**: Remove self-referencing edges
2. ✅ **Completed**: Validate no bidirectional cycles
3. ⏳ **Future**: Infer proper relationships for 9 isolated RPC specs (separate session)

## Lessons Learned

1. **Self-reference vs Bidirectional Cycles**: The original problem description mentioned "A --Refines-> B and B --Refines-> A", but the actual issue was simpler self-references (A -> A).

2. **Hidden Isolation**: Invalid self-references masked a data quality problem - specs that had no valid connections at all.

3. **Proto Extraction Bug**: The proto extractor (Session 97) needs validation to prevent creating self-referencing edges.

## Commit Message

```
Fix circular references: Remove 13 self-referencing edges

- Found 13 self-referencing edges (11 Formalizes, 2 Refines)
- Created cleanup script: scripts/remove_self_referencing_edges.py
- Reduced edge count: 275 → 262
- Validated: No bidirectional cycles in any edge type
- Side effect: 9 RPC specs now isolated (were only connected via invalid self-refs)
- Updated PROBLEM.md: Mark circular reference issue as resolved

Resolves: Circular reference validation issue
Related: Session 97 proto extraction (root cause)
```

## References

- **PROBLEM.md**: "推論結果に循環参照がある" (now resolved)
- **Session 97**: Proto extraction automation (introduced the bug)
- **Session 121-122**: Directory storage implementation (enables per-file validation)
