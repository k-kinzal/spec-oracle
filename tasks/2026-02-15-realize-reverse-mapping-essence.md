# Session: Realize specORACLE's Core Essence - Reverse Mapping to U0

**Date**: 2026-02-15
**Goal**: Face and realize the core essence of specORACLE as a reverse mapping engine

## Problem Statement

CLAUDE.md states:
> "specORACLE is a reverse mapping engine. It does NOT manage specifications written by humans. It constructs U0 from diverse artifacts through reverse mappings: Code, Tests, Proto → [f₀ᵢ⁻¹] → U0"

But reality:
- **U0 is 98.75% manually written** (79/80 specs)
- **31 specs are isolated** (16.8% of total)
- **Reverse mapping doesn't construct U0** - it just extracts U2/U3 specs

## Root Cause Analysis

### Issue 1: AI Semantic Matching is Bypassed

**File**: `spec-core/src/extract.rs:536-564`

```rust
fn calculate_semantic_similarity_with_ai(...) {
    let simple_sim = self.calculate_semantic_similarity(text1, text2);

    if simple_sim > 0.8 { return simple_sim; }      // Trust keywords
    if simple_sim >= 0.4 { /* Use AI blend */ }     // AI only for 0.4-0.8
    simple_sim  // < 0.4: "too expensive, low probability"
}
```

**The fatal flaw**: Cross-layer specs have low keyword overlap!

Example:
- U0: "The system must provide access to specification history"
- U2: "RPC: GetNodeHistory"
- **Keyword overlap**: 0.1 (only "history")
- **Semantic equivalence**: 0.9 (they're the same requirement!)
- **Result**: AI is never called (overlap < 0.4)

This is why `spec infer-relationships-ai` created 0 edges:
```
Total comparisons: 10893
AI cache size: 0 entries  ← AI was never called!
Formalizes edges created: 0
```

### Issue 2: No U0 Generation from Patterns

Current extraction:
- Code tests → U3 specs ✓
- Proto RPCs → U2 specs ✓
- Doc comments → U0 specs ✓

**Missing**: Infer U0 from U2/U3 patterns
- Cluster: Multiple U3 tests about "contradiction detection"
- Cluster: U2 RPC "DetectContradictions"
- **Should generate U0**: "The system must detect contradictions between specifications"
- **Currently**: Nothing. No U0 spec is inferred.

## Current State

Total specs: 184
- U0: 80 specs (79 manual, 1 extracted from doc)
- U1: 1 spec
- U2: 65 specs (37 manual, 28 extracted from proto)
- U3: 38 specs (15 manual, 23 extracted from tests)

Isolated: 31 specs (16.8%)
- U0: 6 isolated (meta-requirements about specORACLE)
- U2: 24 isolated (proto RPCs with no U0 connection)
- U3: 1 isolated (test scenario)

Edges: 161

## Solution: Two-Phase Approach

### Phase 1: Fix AI Threshold for Cross-Layer Matching

**Change**: `spec-core/src/extract.rs:calculate_semantic_similarity_with_ai()`

Remove the "< 0.4 skip AI" bypass for cross-layer comparisons:

```rust
fn calculate_semantic_similarity_with_ai(..., layer1: u8, layer2: u8, ai: &AISemantic) -> f32 {
    let simple_sim = self.calculate_semantic_similarity(text1, text2);

    // For cross-layer comparisons, ALWAYS use AI if available
    // (keyword overlap is meaningless across layers)
    if layer1 != layer2 {
        if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
            // Trust AI more for cross-layer
            return simple_sim * 0.2 + ai_sim * 0.8;
        }
    }

    // Same-layer: use original logic
    if simple_sim > 0.8 { return simple_sim; }
    if simple_sim >= 0.4 {
        if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
            return simple_sim * 0.3 + ai_sim * 0.7;
        }
    }

    simple_sim
}
```

**Expected result**: The 24 isolated proto RPCs should connect to existing U0 requirements.

### Phase 2: Implement U0 Generation from Patterns

**New function**: `SpecGraph::infer_u0_from_patterns()`

Algorithm:
1. **Cluster U2/U3 specs** by semantic similarity
   - Group: All specs mentioning "contradiction"
   - Group: All specs mentioning "omission"
   - Group: All specs mentioning "history"

2. **Generate U0 requirement** for each cluster
   - Use AI: "Given these implementation specs, what's the high-level requirement?"
   - Example cluster: ["RPC: DetectContradictions", "Scenario: detect contradiction", "Scenario: semantic contradiction"]
   - **AI generates**: "The system must detect contradictions between specifications"

3. **Create U0 spec** with metadata
   - `inferred: true`
   - `generated_from: "pattern_cluster"`
   - `source_specs: [list of U2/U3 IDs]`

4. **Create edges**: U0 spec `derives_from` each source spec

**Integration**: Run this as part of `construct-u0 --execute`

## Implementation Steps

1. ✅ Clean up malformed invariants (2 removed, 186 → 184 specs)
2. ⏳ Fix AI threshold for cross-layer matching
3. ⏳ Test: Re-run `spec infer-relationships-ai`
4. ⏳ Implement U0 pattern-based generation
5. ⏳ Test: Run `spec construct-u0 --execute`
6. ⏳ Verify: U0 should grow from 1 extracted to 20+ extracted
7. ⏳ Verify: Isolated specs should drop from 31 to < 5

## Success Criteria

- [ ] U0 extracted specs: 1 → 20+ (from pattern inference)
- [ ] Isolated specs: 31 → < 5 (from AI cross-layer matching)
- [ ] U0 manual ratio: 98.75% → < 80% (more extraction, less manual)
- [ ] **Core essence realized**: U0 is constructed from reverse mappings, not written by humans

## Current Progress

- [x] Investigation complete - root cause identified
- [x] Malformed specs cleaned up
- [ ] AI threshold fix (Phase 1)
- [ ] U0 generation implementation (Phase 2)
- [ ] Integration and testing

## Notes

The key insight: **specORACLE's essence is not about managing manually-written specs. It's about constructing U0 through reverse mapping.**

Current state is a "specification management tool". Target state is a "reverse mapping engine that constructs root specifications from artifacts".

This is the paradigm shift mentioned in PROBLEM.md: "手動入力から自動抽出へ" (From manual input to automatic extraction).
