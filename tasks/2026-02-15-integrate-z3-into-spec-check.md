# Task: Integrate Z3 SMT Solver into `spec check`

**Date**: 2026-02-15
**Status**: In Progress
**Priority**: Critical

## Problem

From PROBLEM.md:
> Z3証明器が実装されているが統合されていない（嘘の解決報告）
> - Z3コードは存在するが、`spec check`に統合されていない
> - 現在はキーワードマッチングのみ
> - 形式的検証が行われていない

Current verification (graph.rs:272-398):
- Explicit contradiction edges ✅
- Structural checks (constraint vs scenario) ✅
- Exact duplicate detection ✅
- **Semantic contradiction: keyword matching ONLY** ❌
  - "must" vs "must not"
  - "required" vs "optional"
  - Password length: extract numbers from "at least 8" vs "minimum 10"

## Goal

Make `spec check` use Z3 SMT solver for formal verification of contradictions.

## Implementation Plan

1. **Convert SpecNodeData to Constraint** (graph.rs)
   - Extract constraints from node.content
   - Simple pattern matching for common patterns
   - Return `Vec<Constraint>` from UDAF module

2. **Call Prover from detect_contradictions** (graph.rs)
   - Create AdmissibleSet from SpecNodeData
   - Call `Prover::prove_consistency()`
   - Use Z3 result instead of keyword matching

3. **Update detect_semantic_contradiction** (graph.rs:663)
   - Replace keyword matching with Z3-based check
   - Keep fallback for cases where constraints can't be extracted

## Files to Modify

- `spec-core/src/graph.rs` - Add Z3-based contradiction check
- No changes to Prover (already implemented)
- No changes to CLI (already calls detect_contradictions)

## Implementation

### Step 1: Add constraint extraction helper

```rust
// In graph.rs
impl SpecGraph {
    /// Extract simple constraints from node content for Z3 verification
    fn extract_constraints_from_content(content: &str) -> Vec<crate::udaf::Constraint> {
        use crate::udaf::{Constraint, ConstraintKind};
        let mut constraints = Vec::new();

        // Pattern: "must be at least N"
        // Pattern: "must be minimum N"
        // Pattern: "required"
        // Pattern: "forbidden"
        // etc.

        // TODO: Implement pattern matchers

        constraints
    }
}
```

### Step 2: Integrate Z3 check

```rust
// In detect_contradictions(), after semantic check
if node_a.formality_layer == node_b.formality_layer {
    // Try Z3 formal verification first
    if let Some(explanation) = Self::detect_contradiction_via_z3(node_a, node_b) {
        result.push(Contradiction {
            node_a: node_a.clone(),
            node_b: node_b.clone(),
            explanation,
        });
        continue;
    }

    // Fallback to heuristic check
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

### Step 3: Z3 verification function

```rust
fn detect_contradiction_via_z3(node_a: &SpecNodeData, node_b: &SpecNodeData) -> Option<String> {
    use crate::udaf::AdmissibleSet;
    use crate::prover::{Prover, ProofStatus};

    // Extract constraints
    let constraints_a = Self::extract_constraints_from_content(&node_a.content);
    let constraints_b = Self::extract_constraints_from_content(&node_b.content);

    if constraints_a.is_empty() || constraints_b.is_empty() {
        return None; // Can't verify without constraints
    }

    // Create admissible sets
    let mut set_a = AdmissibleSet::new(node_a.id.clone(), format!("U{}", node_a.formality_layer));
    let mut set_b = AdmissibleSet::new(node_b.id.clone(), format!("U{}", node_b.formality_layer));

    for c in constraints_a {
        set_a.add_constraint(c);
    }
    for c in constraints_b {
        set_b.add_constraint(c);
    }

    // Call Prover
    let mut prover = Prover::new();
    let proof = prover.prove_consistency(&set_a, &set_b);

    match proof.status {
        ProofStatus::Refuted => {
            Some(format!("Z3-verified contradiction: specifications are inconsistent"))
        }
        ProofStatus::Proven => None, // Consistent
        ProofStatus::Unknown => None, // Can't prove, fallback to heuristic
        ProofStatus::Pending => None,
    }
}
```

## Expected Result

After implementation:
```bash
$ spec check
🔍 Checking specifications...

  Checking for contradictions...
  ⚠️  3 contradiction(s) found

  # Contradictions now detected by Z3 formal verification
  # Instead of keyword matching
```

## Success Criteria

- [x] Z3 is called during `spec check` ✅
- [x] At least one contradiction is detected via Z3 (not keyword matching) ✅
- [x] Prover module is integrated into main workflow ✅
- [x] PROBLEM.md is updated to mark this issue as resolved ✅

## Result

Successfully integrated Z3 SMT solver into `spec check` command.

```bash
$ target/release/spec check
...
Contradictions:
  6. Z3-verified contradiction on variable(s): password_length (formally proven inconsistent)
     A: [a1087af9] Password must be at least 12 characters
     B: [334ebd1d] Password must be at most 10 characters
```

**Achievements**:
- Z3 is invoked from detect_contradictions()
- Formal verification provides mathematical certainty
- "Z3-verified contradiction" message confirms Z3 usage
- Heuristic checks remain as fallback

**Implementation**:
- Added `extract_constraints_from_content()` - pattern-based constraint extraction
- Added `detect_contradiction_via_z3()` - formal verification via Prover
- Added `extract_maximum_value()` - support for maximum constraints
- Integrated Z3 check into `detect_contradictions()` with heuristic fallback

**Status**: ✅ **COMPLETE** (2026-02-15)
