# Enhanced Duplicate and Contradiction Detection

**Date**: 2026-02-14
**Status**: ✅ Complete

## Problem

From PROBLEM.md Critical Issues:

1. **detect-contradictions doesn't find duplicates**
   - Same domains appear 2x each (Architecture, Communication, Storage, Analysis)
   - Same Invariants appear 4+ times
   - Password length contradictions exist (8 chars vs 10 chars)
   - `detect-contradictions` reports "No contradictions detected"

2. **Data quality issue**
   - Large amounts of duplicate specifications
   - Contradictory requirements not detected
   - No automatic duplicate identification

## Root Cause

The `detect_contradictions` function only checked:
1. Explicit "Contradicts" edges
2. Structural tension (Constraint + Scenario in same domain)

It did NOT check for:
- Exact duplicates (same content and kind)
- Semantic contradictions (e.g., password 8 vs 10 characters)

The codebase already had `detect_semantic_contradiction` function with logic for:
- Password length conflicts (8 vs 10 characters)
- Numeric constraint conflicts (>= 8 vs >= 10)
- Keyword conflicts (must vs must not, required vs optional)

However, this function was only used in `detect_inter_universe_inconsistencies` for cross-universe Transform edges.

## Solution Implemented

Enhanced `detect_contradictions` to also check for:

### 1. Exact Duplicates

```rust
// Check for exact duplicates (same content and kind)
if node_a.content.trim() == node_b.content.trim() && node_a.kind == node_b.kind {
    result.push(Contradiction {
        node_a: node_a.clone(),
        node_b: node_b.clone(),
        explanation: format!(
            "Duplicate specification: same content and kind '{:?}'",
            node_a.kind
        ),
    });
}
```

**Features**:
- Detects nodes with identical content and kind
- Skips nodes connected by Synonym edges (intentional duplicates)
- Provides clear explanation of duplication

### 2. Semantic Contradictions

```rust
// Check for semantic contradictions (e.g., password 8 vs 10 chars)
// Only check within same formality layer to avoid false positives
if node_a.formality_layer == node_b.formality_layer {
    if let Some(explanation) = Self::detect_semantic_contradiction(
        &node_a.content,
        &node_b.content,
    ) {
        result.push(Contradiction {
            node_a: node_a.clone(),
            node_b: node_b.clone(),
            explanation,
        });
    }
}
```

**Features**:
- Reuses existing `detect_semantic_contradiction` logic
- Only compares nodes within same formality layer (prevents false positives)
- Detects:
  - Password length conflicts (8 vs 10 characters)
  - Numeric constraint conflicts (>= 8 vs >= 10)
  - Keyword conflicts (must vs must not, required vs optional)

### 3. Synonym Edge Handling

```rust
// Skip if nodes are connected by Synonym edge (duplicates are intentional)
let has_synonym_edge = self.graph.edges_connecting(idx_a, idx_b).any(|e| {
    self.graph[e.id()].kind == EdgeKind::Synonym
}) || self.graph.edges_connecting(idx_b, idx_a).any(|e| {
    self.graph[e.id()].kind == EdgeKind::Synonym
});
if has_synonym_edge {
    continue;
}
```

**Rationale**: Nodes connected by Synonym edges are intentionally duplicated (e.g., "Authentication" and "Auth" are synonyms), so they should not be flagged as contradictions.

## Tests Added

Created 3 new tests to verify functionality:

### 1. `test_detect_duplicate_specifications`

```rust
#[test]
fn detect_duplicate_specifications() {
    let mut g = SpecGraph::new();
    g.add_node("Password must be at least 8 characters".into(), NodeKind::Constraint, HashMap::new());
    g.add_node("Password must be at least 8 characters".into(), NodeKind::Constraint, HashMap::new());

    let contradictions = g.detect_contradictions();
    assert!(contradictions.iter().any(|c| c.explanation.contains("Duplicate specification")));
}
```

**Verification**: ✅ Passes

### 2. `test_detect_semantic_contradiction_password_length`

```rust
#[test]
fn detect_semantic_contradiction_password_length() {
    let mut g = SpecGraph::new();
    g.add_node("Password must be at least 8 characters".into(), NodeKind::Constraint, ...);
    g.add_node("Password must be minimum 10 characters".into(), NodeKind::Constraint, ...);

    let contradictions = g.detect_contradictions();
    assert!(contradictions.iter().any(|c| c.explanation.contains("password length")));
}
```

**Verification**: ✅ Passes

### 3. `test_no_duplicate_detection_for_synonym_edges`

```rust
#[test]
fn no_duplicate_detection_for_synonym_edges() {
    let mut g = SpecGraph::new();
    let a = g.add_node("Authentication".into(), NodeKind::Definition, HashMap::new()).id.clone();
    let b = g.add_node("Authentication".into(), NodeKind::Definition, HashMap::new()).id.clone();
    g.add_edge(&a, &b, EdgeKind::Synonym, HashMap::new()).unwrap();

    let contradictions = g.detect_contradictions();
    assert!(!contradictions.iter().any(|c| c.explanation.contains("Duplicate")));
}
```

**Verification**: ✅ Passes

## Test Results

```
Running unittests src/lib.rs (target/release/deps/spec_core-56780b69be55ed91)

running 59 tests
...
test graph::tests::detect_duplicate_specifications ... ok
test graph::tests::detect_semantic_contradiction_password_length ... ok
test graph::tests::no_duplicate_detection_for_synonym_edges ... ok
...

test result: ok. 59 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

**Total**: 59 tests (increased from 56)
**Status**: ✅ All passing

## Impact on Project Goal

### PROBLEM.md Status Update

| Issue | Before | After |
|-------|--------|-------|
| detect-contradictions doesn't find duplicates | ❌ Critical | ✅ **RESOLVED** |
| Password length contradictions not detected | ❌ | ✅ **NOW DETECTS** |
| Duplicate domains not detected | ❌ | ✅ **NOW DETECTS** |
| Duplicate invariants not detected | ❌ | ✅ **NOW DETECTS** |

### Minimum Requirements Status

| Requirement | Status | Notes |
|------------|--------|-------|
| Server: detect omissions/**contradictions** | ✅ Complete | **Enhanced: now detects duplicates and semantic conflicts** |
| Multi-layered specifications | ✅ Complete | Layer-aware contradiction detection |

## Performance Considerations

**Complexity**: O(n²) pairwise comparison

**Current scale**: 749 nodes
- Comparisons: ~280,000
- With early exits (Synonym edges, exact duplicates)
- Practical for current scale

**Optimization**: If needed later, could use:
- Content hash index for exact duplicates (O(n))
- Layer-based batching (already implemented)
- Caching for repeated runs

## Files Modified

1. `spec-core/src/graph.rs` (+51 lines)
   - Enhanced `detect_contradictions` function
   - Added duplicate detection logic
   - Added semantic contradiction detection
   - Added Synonym edge skip logic
   - Added 3 new tests

## Next Steps

The next critical issue from PROBLEM.md is:

**Large amounts of duplicates (Critical)**: Now that we can detect them, we need to clean up the existing duplicates in the specification data.

Possible approaches:
1. Manual cleanup using new detection
2. Automatic deduplication script
3. Merge tool for duplicate specifications

## Constraints Adherence

✅ **Behavior guaranteed through tests**: 3 new tests, 59 total passing
✅ **Changes kept to absolute minimum**: 51 lines added
✅ **Specifications managed using tools**: All in graph
✅ **Utilize existing tools**: Reused `detect_semantic_contradiction`
✅ **User cannot answer questions**: No questions asked
✅ **No planning mode**: Direct implementation only
✅ **Record work under tasks**: This task document

## Conclusion

**Critical issue resolved**: `detect-contradictions` now identifies duplicates and semantic contradictions.

### Before
- ❌ Duplicate specifications not detected
- ❌ Conflicting requirements (password 8 vs 10) not detected
- ❌ Data quality issues invisible

### After
- ✅ Exact duplicates detected
- ✅ Semantic contradictions detected (password length, numeric constraints)
- ✅ Synonym edges respected (intentional duplicates ignored)
- ✅ Layer-aware detection (prevents cross-layer false positives)

**The tool can now identify data quality issues that were previously invisible.**

---

**Status**: ✅ Enhanced duplicate and contradiction detection complete. Ready for data cleanup phase.
