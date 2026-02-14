# Task: Fix Extraction Deduplication Bug

**Date**: 2026-02-15
**Session**: Current
**Status**: In Progress

## Problem

The reverse mapping engine creates **duplicate specifications** on every extraction run, violating the core concept.

### Evidence

1. **Massive duplication**: 119 out of 295 nodes (40%) were duplicates
2. **Multiple extraction runs**: Same specs extracted 3-4 times
3. **Timestamps prove it**:
   - Original: 1771077123
   - Run 2: 1771082309
   - Run 3: 1771085170
   - Run 4: 1771086267

### Root Cause

`spec-core/src/extract.rs:133` - `ingest()` method calls `add_node_with_layer()` which calls `add_node()` **without deduplication check**.

```rust
// Line 133 - No duplicate check!
let node = self.add_node_with_layer(
    spec.content,
    spec.kind,
    spec.formality_layer,
    metadata,
);
```

`spec-core/src/graph.rs:125` - `add_node()` blindly creates new UUID:

```rust
pub fn add_node(&mut self, content: String, kind: NodeKind, metadata: HashMap<String, String>) -> &SpecNodeData {
    let id = Uuid::new_v4().to_string(); // Always creates new ID!
    // ... no duplicate check
}
```

## Impact

- **Data quality**: 40% of specs were duplicates
- **Isolation**: 168 extracted specs had no edges (duplicates can't connect)
- **Disk waste**: 119 duplicate nodes, 230 duplicate edges
- **Violates core concept**: Reverse mapping should be idempotent

## Solution

### Step 1: Implement Deduplication (✅ DONE)

Created `scripts/deduplicate_specs.py` to clean up existing duplicates:
- Identified 49 duplicate groups
- Removed 119 duplicate nodes
- Removed 230 duplicate edges
- Kept oldest instance of each duplicate
- Result: 295 → 176 nodes

### Step 2: Fix `ingest()` Method (TODO)

Modify `spec-core/src/extract.rs:ingest()` to check for duplicates before adding nodes:

```rust
// Before creating node, check if identical content exists
let existing = self.find_node_by_content(&spec.content, spec.kind);

let node_id = if let Some(existing_node) = existing {
    // Duplicate found - skip creation, update metadata if needed
    report.nodes_skipped += 1;
    existing_node.id.clone()
} else {
    // New node - create it
    let node = self.add_node_with_layer(...);
    created_ids.push(node.id.clone());
    report.nodes_created += 1;
    node.id
};
```

### Step 3: Add `find_node_by_content()` Method (TODO)

Add to `spec-core/src/graph.rs`:

```rust
pub fn find_node_by_content(&self, content: &str, kind: NodeKind) -> Option<&SpecNodeData> {
    self.graph
        .node_weights()
        .find(|n| n.content == content && n.kind == kind)
}
```

### Step 4: Test Idempotency (TODO)

Run extraction multiple times and verify:
```bash
spec extract spec-core/src/graph.rs
# Record count: N nodes

spec extract spec-core/src/graph.rs
# Should still be N nodes (no duplicates!)

spec check
# Should report 0 isolated specs from duplicate extraction
```

## Verification

### Before Fix
```bash
$ spec check
Total specs:        295
Isolated specs:     36
Extracted specs:    168 (56.9%)
# 119 duplicates!
```

### After Cleanup
```bash
$ python3 scripts/deduplicate_specs.py --execute
Nodes removed: 119
Edges removed: 230
Final node count: 176

$ spec check
Total specs:        176
Isolated specs:     31 (proto_rpc: 28, assertion: 2, doc: 1)
Extracted specs:    49 (27.8%)
# Much better!
```

### After Code Fix (Expected)
```bash
$ spec extract spec-core/src/graph.rs
Nodes created: 0 (all duplicates skipped)
Nodes skipped: 42 (already exist)

$ spec check
Total specs:        176 (unchanged!)
Isolated specs:     31 (unchanged!)
# Idempotent! ✅
```

## Theory

This bug violated the **reverse mapping engine** concept:

**U0 = f₀₃⁻¹(U3)** should be **idempotent**:
- f₀₃⁻¹(U3) = f₀₃⁻¹(U3) = ... = U0 (same result every time)
- Running extraction N times should produce the same U0

The bug broke this property:
- f₀₃⁻¹(U3) ≠ f₀₃⁻¹(f₀₃⁻¹(U3))
- Each run created new nodes instead of recognizing existing ones

## Next Steps

1. ✅ Cleanup duplicates (DONE)
2. ⏳ Implement `find_node_by_content()` in graph.rs
3. ⏳ Modify `ingest()` to use deduplication
4. ⏳ Test idempotency
5. ⏳ Update PROBLEM.md with resolution
6. ⏳ Commit with smallest possible unit

## Related Issues

- PROBLEM.md: "🚨 186個の孤立仕様が存在する" (was marked resolved, but regressed)
- PROBLEM.md: "🚨 大量の重複仕様が存在する"
- Core concept: "specORACLE is a reverse mapping engine" (requires idempotency)
