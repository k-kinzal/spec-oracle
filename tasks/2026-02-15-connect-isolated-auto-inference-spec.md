# Task: Connect Isolated Auto-Inference Specification

**Date**: 2026-02-15
**Session**: 103

## Problem

The specification graph had 1 isolated specification:
- [e9c466e9] U0 constraint: "The spec add command must automatically infer relationships for newly added specifications and create high-confidence edges without manual intervention"

This was a requirement specification without a corresponding implementation specification.

## Investigation

Found that the implementation exists:
- `spec-cli/src/main.rs` line 693-701: Auto-infer relationships in `spec add` command
- `spec-core/src/extract.rs` line 251-282: `auto_connect_node()` method

The method:
1. Calls `infer_relationships_for_node` to find potential relationships
2. Auto-creates edges with confidence >= 0.8
3. Suggests edges with confidence 0.5-0.8 for human review

## Solution

1. Created U3 specification for the implementation:
   - ID: [dc8ca253]
   - Content: "The auto_connect_node method in SpecGraph automatically infers relationships for a newly added node by calling infer_relationships_for_node, auto-creating edges with confidence >= 0.8 and suggesting edges with confidence 0.5-0.8 for human review"
   - Layer: U3 (implementation)

2. Manually set formality_layer to 3 (implementation layer)

3. Created Formalizes edge:
   - From: [e9c466e9] U0 requirement
   - To: [dc8ca253] U3 implementation
   - Edge ID: [8b243319]

## Result

- **Before**: 190 specs, 1 isolated (0.5%)
- **After**: 191 specs, 0 isolated (0%)
- **Achievement**: Zero omissions maintained

## Verification

```bash
$ spec check
✅ All checks passed! No issues found.
  Total specs:        191
  Isolated specs:     0
```

## Technical Details

**Implementation location**: `spec-core/src/extract.rs:251-282`

**Confidence thresholds**:
- >= 0.8: Auto-create edge
- 0.5-0.8: Suggest for human review
- < 0.5: Ignore

**Method signature**:
```rust
pub fn auto_connect_node(&mut self, node_id: &str) -> IngestionReport
```

## Relation to specORACLE Goals

This task demonstrates the reverse mapping engine in action:
- U3 (implementation) exists: `auto_connect_node()` method
- U0 (requirement) exists: "must automatically infer relationships"
- Connection established: Formalizes edge from U0 → U3
- Result: Complete traceability across layers

This is a micro-example of f₀₃⁻¹: from implementation (U3) we can reverse-map to the requirement (U0).
