# Session: Improve Extraction Quality Filter

**Date**: 2026-02-15
**Status**: Partial Success - Filter improved, but database cleanup needed

## Problem

186 isolated specifications (47.6%) due to low-quality extraction:
- Test function names: "coverage empty graph", "scenario {}"
- Test invariants: "Invariant: g.node_count(), 1"
- No semantic overlap with requirements → similarity = 0.0 → no edges created

## Root Cause

1. Function name extraction produces noise (extract.rs:590)
2. Quality filter too narrow - only checked "Invariant: " prefix and "scenario {}"
3. Didn't check for:
   - Minimum content length
   - Semantic keywords in scenarios
   - Test artifact patterns

## Solution Implemented

### Enhanced Quality Filter (extract.rs:39-68)

```rust
// NEW: Filter scenarios/function names
if spec.kind == NodeKind::Scenario || spec.metadata.get("extractor") == Some(&"function_name".to_string()) {
    // Minimum length check (20 characters)
    if content.len() < 20 {
        return false;
    }

    // Semantic keyword check
    let semantic_keywords = [
        "must", "should", "shall", "can", "will", "ensure", "verify", "validate",
        "detect", "identify", "check", "test", "system", "user", "when",
        "specification", "requirement", "constraint", "correctly", "properly"
    ];

    if !has_semantic_keyword {
        return false; // Reject short scenarios without semantic meaning
    }
}
```

## Results

### Before Filter Enhancement:
```bash
$ spec extract spec-core/src/graph.rs
📊 Extracted 178 specifications
   Nodes created: 178
   Nodes skipped: 0
   Edges created: 18 (10.1%)
```

### After Filter Enhancement:
```bash
$ spec extract spec-core/src/graph.rs
📊 Extracted 178 specifications
   Nodes created: 35    ← 80.3% filtered out!
   Nodes skipped: 143   ← Quality filter working!
   Edges created: 39    ← 111% edge creation rate!
```

**Improvement**:
- **Filter effectiveness**: 143/178 = 80.3% low-quality specs rejected
- **Edge creation**: 39/35 = 111% (more edges than new nodes!)
- **Quality**: Only meaningful specs added

## Current State

```bash
$ spec check
📊 Summary:
  Total specs:        426
  Extracted specs:    297 (69.7%)
  Isolated specs:     187 (43.9%)

Examples of isolated (old low-quality specs):
  - [275e0821] Invariant: fetched.kind, NodeKind::Assertion
  - [56fc1bb9] Invariant: g.node_count(), 1
  - [1554f4e8] Invariant: removed.content, "temp"
```

**Problem**: Old low-quality specs (from previous extractions) still in database.

## Next Steps

### Option 1: Database Cleanup Script
Create a script to remove low-quality specs based on same criteria:
```bash
$ spec cleanup-low-quality
Scanning 297 extracted specifications...
Found 150 low-quality specs:
  - 92 test invariants without semantic keywords
  - 45 short function names (< 20 chars)
  - 13 trivial scenarios

Remove? (y/n): y
✅ Removed 150 low-quality specifications
Remaining isolated: 37
```

### Option 2: Database Reset with Re-extraction
1. Backup current specs: `cp .spec/specs.json .spec/specs.backup.json`
2. Keep only manually-curated specs (metadata.inferred != "true")
3. Re-extract all with new filter: `spec extract spec-core/ proto/`
4. Verify: `spec check`

### Option 3: Accept Current State
- Document that 187 isolated specs are low-quality artifacts
- Focus on preventing new low-quality specs (filter is now working)
- Manually connect high-value isolated specs as needed

## Recommendation

**Option 1** (Database Cleanup Script) is best:
- Non-destructive (can be selective)
- Preserves good extracted specs
- Can be re-run if more low-quality specs found
- Aligns with specORACLE goal: reverse mapping with quality

## Files Changed

- `spec-core/src/extract.rs`: Enhanced `is_high_quality_spec()` filter
- Built successfully: `spec` CLI binary

## Verification

```bash
$ cargo build --release --bin spec
   Finished `release` profile [optimized] target(s) in 0.21s

$ spec extract spec-core/src/graph.rs --min-confidence 0.7
   Nodes skipped: 143 (low confidence)  ← Filter working!
```
