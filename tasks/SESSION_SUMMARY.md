# Session Summary: Realizing specORACLE's Core Essence

**Date**: 2026-02-15
**Focus**: Understanding and beginning to realize the reverse mapping engine essence

## Starting State

Total specifications: 186
- U0: 80 specs (79 manual / 1 extracted) - **98.75% manual**
- U1: 1 spec
- U2: 65 specs (37 manual / 28 extracted from proto)
- U3: 38 specs (15 manual / 23 extracted from tests)

Isolated specifications: 34 (18.3%)
Edges: 161

## Core Problem Identified

**CLAUDE.md states**:
> "specORACLE is a reverse mapping engine. It does NOT manage specifications written by humans. It constructs U0 from diverse artifacts through reverse mappings."

**Reality**: U0 is 98.75% manually written. specORACLE is a "specification management tool", not a "reverse mapping engine".

## Root Cause Analysis

### Issue 1: AI Semantic Matching Bypassed for Cross-Layer

**File**: `spec-core/src/extract.rs:536-564`

The AI similarity check skips cross-layer pairs with low keyword overlap (<0.4), assuming "too expensive, low probability". But cross-layer specs have different vocabularies:

- U0: "The system must provide access to specification history"
- U2: "RPC: GetNodeHistory"
- Keyword overlap: 0.1 (only "history")
- Semantic equivalence: 0.9 (same requirement!)
- **AI was never called** → 0 edges created

Result from `spec infer-relationships-ai`:
```
Total comparisons: 10893
AI cache size: 0 entries  ← AI never called!
Formalizes edges created: 0
```

### Issue 2: No U0 Generation from Patterns

Extraction works:
- Code tests → U3 specs ✓
- Proto RPCs → U2 specs ✓
- Doc comments → U0 specs ✓

**Missing**: Infer U0 from U2/U3 patterns:
- Multiple U3 tests about "contradiction detection"
- U2 RPC "DetectContradictions"
- **Should generate U0**: "The system must detect contradictions"
- **Currently**: Nothing

## Work Completed

### 1. Investigation and Documentation ✅

- [x] Analyzed current specification distribution
- [x] Identified why U0 is 98.75% manual
- [x] Discovered AI threshold bypass for cross-layer
- [x] Documented findings in `tasks/2026-02-15-realize-reverse-mapping-essence.md`
- [x] Created task tracking (#1, #2)

### 2. Cleanup ✅

- [x] Removed 2 malformed invariants (garbage extraction)
- [x] Created cleanup script: `scripts/cleanup_malformed_invariants.py`
- [x] Reduced specs: 186 → 184
- [x] Isolated specs: 34 → 31 (cleanup removed some)

### 3. AI Threshold Fix ✅

**Commit**: c34f338 "Fix AI semantic matching for cross-layer specifications"

**Changes**:
```rust
// NEW: Always use AI for cross-layer comparisons
if layer1 != layer2 {
    if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
        // Trust AI heavily (0.8 weight) over keywords (0.2 weight)
        return simple_sim * 0.2 + ai_sim * 0.8;
    }
}
// PRESERVED: Original conservative logic for same-layer
```

**Expected impact**: 24 isolated proto RPCs should connect to U0 via AI semantic matching.

## Current State (Post-Fix)

Total specifications: 184
- Cleaned up 2 malformed specs
- AI threshold fix applied and committed
- Tests passing (71/71)

Isolated specifications: 31 (awaiting AI inference test)

## Next Steps

### Immediate: Verify AI Fix ⏳

Run `spec infer-relationships-ai --min-confidence 0.6` to test if cross-layer matching now works.

**Expected**:
- AI cache size > 0 (AI is called)
- Edges created > 10 (connections found)
- Isolated specs: 31 → < 15 (50% reduction)

### Phase 2: Implement U0 Generation ⏳

**Goal**: Construct U0 from U2/U3 patterns (the true "reverse mapping")

**Approach**:
1. Cluster U2/U3 specs by semantic similarity
2. For each cluster, use AI to generate high-level U0 requirement
3. Create U0 spec with `derives_from` edges to sources
4. Integration: Part of `spec construct-u0 --execute`

**Example**:
- Cluster: ["RPC: DetectContradictions", "Scenario: detect contradiction", "Scenario: semantic contradiction"]
- **AI generates U0**: "The system must detect contradictions between specifications"
- Create edges: U0 `derives_from` each U2/U3 spec

### Success Metrics

Target state:
- [ ] U0 extracted specs: 1 → 20+ (from pattern inference)
- [ ] Isolated specs: 31 → < 5 (from AI cross-layer + pattern inference)
- [ ] U0 manual ratio: 98.75% → < 80% (more extraction, less manual)
- [ ] **Core essence realized**: U0 constructed from reverse mappings

## Key Insights

### The Paradigm Shift

**From**: "Specification management tool" (humans write U0)
**To**: "Reverse mapping engine" (system constructs U0)

This is what PROBLEM.md called: "手動入力から自動抽出へ" (From manual input to automatic extraction)

### The Essence

specORACLE's value is NOT in managing manually-written specs. Its value is in:
1. **Observing** implementation artifacts (code, tests, proto)
2. **Inferring** high-level requirements from patterns
3. **Constructing** U0 as the union of reverse mappings
4. **Detecting** contradictions and omissions across layers

This addresses the core problem from `motivation.md`:
> "Multi-layered defense is essential, but governing it is extremely difficult. specORACLE provides the baseline (U0) that coordinates all layers."

### Why This Matters

Without true reverse mapping:
- U0 becomes another layer humans must maintain
- Multi-layered defense has no common reference point
- Contradictions between layers go undetected
- The tool becomes "yet another spec format" instead of "the oracle that brings order to chaos"

With reverse mapping:
- U0 emerges from implementation artifacts
- Humans focus on implementation (what they know)
- System infers requirements (what's hard to articulate)
- Multi-layered defense has automatic baseline

## Files Modified

```
.spec/specs.json                                   # Cleaned up specs
scripts/cleanup_malformed_invariants.py            # New cleanup tool
spec-core/src/extract.rs                           # AI threshold fix
tasks/2026-02-15-realize-reverse-mapping-essence.md # Investigation docs
```

## Commits

- `c34f338` Fix AI semantic matching for cross-layer specifications

## References

- CLAUDE.md: Core concept and constraints
- PROBLEM.md: Issue tracking and resolution status
- docs/motivation.md: Why specORACLE is needed
- docs/conversation.md: U/D/A/f theoretical model
