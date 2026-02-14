# Session 95 Summary: AI-Enhanced Cross-Layer Matching

**Date**: 2026-02-14  
**Result**: 14 specifications connected (225 → 211 isolated)

## Key Achievements

1. **Implemented standalone AI inference**: Added `infer-relationships-ai` command support in standalone mode
2. **Ran 41,451 cross-layer comparisons**: AI-powered semantic matching across U0/U1/U2/U3
3. **Created 7 new edges**: Reduced isolation by 6% (225 → 211 specs)
4. **Fixed Z3 build environment**: Formal verification infrastructure now builds successfully

## Core Problem Identified

**Extracted specifications are too low-quality for AI matching**

Examples of isolated specs:
```
- "Invariant: fetched.content, 'User must authenticate'"
- "Invariant: g.node_count(), 1"
- "coverage empty graph"
- "scenario {}"
```

These are raw code artifacts, not semantic specifications. AI cannot bridge the gap between:
- U0: "The system must detect contradictions between specifications"
- U3: "Invariant: fetched.kind, NodeKind::Assertion"

**Zero keyword overlap** → No connection possible.

## The Essence Challenge

Per CLAUDE.md: "specORACLE is a reverse mapping engine"

Current state:
- ✅ Extraction works (234 specs extracted)
- ✗ **Extracted specs are noise, not signal**
- ✗ Reverse mapping U3→U0 fails due to quality

The essence requires: **Extract *specifications*, not code artifacts**

## Recommendations

### Priority 1: Improve Extraction Quality
Enhance `RustExtractor` to generate semantic specs:
```rust
// Before
"Invariant: fetched.kind, NodeKind::Assertion"

// After  
"Test verifies that retrieved specification is an Assertion node"
```

### Priority 2: Proto Extraction (U2 Layer)
Currently only U3 (Rust code) is extracted. Need U2 (gRPC proto) extraction for interface specs.

### Priority 3: Accept Some Isolation
Not all code artifacts should be specs. Filter extraction to capture only meaningful specifications.

## Files Modified

- `spec-cli/src/main.rs`: Added standalone `InferRelationshipsAi` handler (lines 1732-1767)
- `.spec/specs.json`: 7 new Formalizes edges

## Metrics

- Before: 225 isolated specs
- After: 211 isolated specs  
- Improvement: 6% (-14 specs)
- Target: <20 isolated (95%+ coverage)

See `tasks/2026-02-14-session-95-isolated-specs-investigation.md` for full analysis.
