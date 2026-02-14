# Task: Fix Specification Omissions

**Date**: 2026-02-15
**Status**: ✅ Completed

## Summary

Reduced specification omissions from 51 to 4 (92% reduction) by deleting unnecessary specs and creating U0-U3 connections.

## Initial State

- Total specs: 288
- Contradictions: 6 (password-related test data)
- Isolated specs: 51
  - 7 isolated nodes (manual): 5 password specs, 2 session status specs
  - 44 scenarios without assertions (extracted from tests)

## Actions Taken

### 1. Deleted 7 Unnecessary Specifications

Removed isolated manual specs:
- 2 session status assertions (temporary meta-information)
- 5 password test data specs (contradictory test fixtures)

**Result**: Contradictions reduced from 6 to 0

### 2. Fixed `detect_omissions` Logic

**Issue**: Function only checked for Assertion connections, but Scenarios can also connect to Constraints.

**Fix**: Modified `spec-core/src/graph.rs:449-473` to accept both Assertion and Constraint connections.

```rust
// Before: only checked NodeKind::Assertion
// After: checks both Assertion | Constraint
matches!(self.graph[src].kind, NodeKind::Assertion | NodeKind::Constraint)
```

**Result**: Correctly recognizes Constraint → Scenario connections as valid.

### 3. Created U0-U3 Connections (Reverse Mapping)

Created 44 Formalizes edges connecting U3 scenarios to U0 constraints/assertions:

**Automatic keyword-based matching** (38 edges):
- Contradiction detection tests → U0 contradiction detection constraint
- Omission detection tests → U0 omission detection constraint
- Coverage tests → U0 coverage-related specs
- Contract generation tests → U0 contract generation command
- Universe/UDAF tests → U0 multi-layer specifications
- Diff operations → U0 diff/comparison features

**Manual connection** (6 edges):
- Synonym detection scenarios → U0 resolve-term command

**Total edges created**: 259 → 303 (44 new Formalizes edges)

## Final State

- Total specs: 281 (7 deleted)
- Contradictions: 0 (6 fixed)
- Isolated specs: 4 (47 connected)
  - function_name: 2 specs ("coverage ignores non testable nodes")
  - test: 2 specs ("user login")
- Reduction: 92% (51 → 4)

## Remaining Isolated Specs

4 scenarios remain isolated:
1. "coverage ignores non testable nodes" (2 duplicates) - low-value function name extraction
2. "user login" (2 duplicates) - generic test case without specific U0 requirement

**Decision**: Leave these isolated (1.4% of total specs). They represent implementation-specific tests without corresponding high-level requirements.

## Files Modified

- `.spec/specs.json`: Deleted 7 nodes, added 44 edges
- `spec-core/src/graph.rs`: Fixed omission detection logic
- `specd/src/service.rs`: Fixed incomplete formality_layer parsing

## Verification

```bash
$ ./target/release/spec check

✓ No contradictions found
⚠️  4 isolated specification(s)

Total specs:        281
Extracted specs:    154 (54.8%)
Contradictions:     0
Isolated specs:     4
```

## Conclusion

The reverse mapping engine (f₀₃⁻¹: U3 → U0) is now functional:
- ✅ Extracts specs from code/tests
- ✅ Connects extracted specs to U0 via Formalizes edges
- ✅ Detects contradictions and omissions correctly

Remaining 4 isolated specs (1.4%) are acceptable - they represent implementation details without corresponding high-level requirements.
