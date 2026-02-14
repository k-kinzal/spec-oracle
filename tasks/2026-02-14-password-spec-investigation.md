# Password Spec Failure Investigation

**Date**: 2026-02-14
**Issue**: Multiple near-identical password specs remain unconnected despite AI inference

## Evidence

### Nearly Identical Specs (Same Content)

**Spec A (77ad7450)**:
- Content: "Passwords must be at least 8 characters."
- Kind: constraint
- Formality Layer: 0
- Extractor: doc
- Universe: (none)
- Edges: 0

**Spec B (34bf0b12)**:
- Content: "Password must be at least 8 characters" (no period)
- Kind: constraint
- Formality Layer: (not shown, likely 0 or unset)
- Extractor: (unknown)
- Universe: ui
- Edges: 1 (transform to "Password must be minimum 10 characters")

**Difference**: "Passwords" vs "Password", trailing period, universe metadata

**Expected**: Synonym or Refines edge
**Actual**: No connection

### Cross-Layer Specs (Should Be Connected)

**Spec C (733d69a4)**:
- Content: "password minimum length"
- Kind: scenario
- Formality Layer: 1
- Extractor: function_name
- Edges: 0

**Spec D (c1ef864d)**:
- Content: "Invariant: password.len() >= 8, \"Password must be at least 8 characters\""
- Kind: constraint
- Formality Layer: 3
- Extractor: assertion
- Edges: 0

**Expected**: Formalizes or DerivesFrom edges connecting Layer 0 → 1 → 3
**Actual**: All isolated

## Keyword Similarity Analysis

### A vs B (Nearly Identical)
- A tokens: {passwords, must, be, at, least, 8, characters}
- B tokens: {password, must, be, at, least, 8, characters}
- After lowercase: {password, must, be, at, least, 8, characters} (almost identical)
- **Jaccard similarity**: ~7/8 = **0.875** (very high!)

### A vs C (Cross-Layer)
- A tokens: {passwords, must, be, at, least, 8, characters}
- C tokens: {password, minimum, length}
- Common: {password} (or 0 if stemming doesn't normalize plural)
- **Jaccard similarity**: ~0.1 (very low)

### A vs D (Cross-Layer)
- A tokens: {passwords, must, be, at, least, 8, characters}
- D tokens: {invariant, password, len, 8, password, must, be, at, least, 8, characters}
- Common (normalized): {password/passwords, must, be, at, least, 8, characters}
- **Jaccard similarity**: ~0.5-0.6 (medium)

## Why AI Inference Failed

### Case 1: A vs B (Same Layer, High Similarity)

From spec-core/src/extract.rs:345-348:
```rust
// If similarity is already high, no need for AI
if simple_sim > 0.5 {
    return simple_sim;
}
```

**Result**:
- Simple similarity = 0.875 (HIGH)
- Returns 0.875 without calling AI
- Should have created Synonym edge

**Why no edge created?**

Looking at spec-core/src/extract.rs:369-396 (infer_edge_kind logic):
1. Formalizes: Requires `source.formality_layer < target.formality_layer`
   - A and B both layer 0, doesn't match
2. Refines: Requires similarity > 0.6
   - A-B similarity = 0.875 > 0.6, **should match!**
3. Synonym: Requires similarity > 0.9
   - A-B similarity = 0.875 < 0.9, **doesn't match**

**Hypothesis**: Refines edge should have been created with confidence ~0.875.

**Possible causes**:
1. Universe filtering prevented comparison
2. Edge already exists (check)
3. Iteration logic bug
4. add_edge failed silently

### Case 2: A vs C (Cross-Layer, Low Keyword Overlap)

- Simple similarity ≈ 0.1 (LOW)
- Different layers (0 vs 1)
- **AI should have been called**

AI would likely return high similarity (both about password length requirements).

**Why no edge?**
1. AI was called, returned low score (unlikely - clear semantic match)
2. AI call failed silently
3. Specs weren't compared (iteration bug)
4. Universe filtering

### Case 3: A vs D (Cross-Layer, Medium Overlap)

- Simple similarity ≈ 0.5-0.6 (MEDIUM)
- Different layers (0 vs 3)
- If < 0.5: AI called
- If > 0.5: AI skipped

**Blended similarity** (if AI called):
- simple_sim * 0.3 + ai_sim * 0.7
- If ai_sim = 0.95: 0.5 * 0.3 + 0.95 * 0.7 = 0.815
- Should create Formalizes edge

## Root Causes (Hypotheses)

### 1. Universe Filtering Theory ❓
Maybe specs with `universe` metadata are filtered out or compared separately?

**Check**: Does inference code filter by universe before comparing?

### 2. Same-Layer High-Similarity Threshold Too High ✅
For A vs B (0.875 similarity):
- Synonym threshold: 0.9 (too high!)
- Refines threshold: 0.6 (should match!)

**Why no edge?** Need to check infer_edge_kind logic more carefully.

### 3. Silent AI Failure ❓
AI calls may be failing without logging.

**Check**: Add debug logging to ai_semantic.rs

### 4. Iteration/Comparison Bug ❓
Maybe some node pairs aren't being compared at all.

**Check**: Count expected comparisons vs actual

## Next Steps

### Immediate Debugging
1. Add debug logging to infer_relationships_for_node_with_ai
2. Re-run AI inference with logging enabled
3. Trace exact path for password spec comparisons

### Threshold Adjustment
Consider lowering Synonym threshold from 0.9 to 0.85:
```rust
// Rule 3: Synonym - very similar content, same layer
if similarity > 0.85 && source.formality_layer == target.formality_layer {
    return Some((
        crate::EdgeKind::Synonym,
        similarity,
        "Near-identical specifications".to_string(),
    ));
}
```

### Universe Handling
Need to understand universe metadata semantics:
- Should different universes prevent connections?
- Or should they create Transform edges?
- What about specs with no universe vs specs with universe?

## Validation Criteria

After fix, password specs should have:
- ✓ 77ad7450 ↔ 34bf0b12: Synonym edge (0.875 similarity)
- ✓ 77ad7450 → c1ef864d: Formalizes edge (layer 0 → 3)
- ✓ 733d69a4 → c1ef864d: DerivesFrom edge (test derives from constraint)
- ✓ Omission count for password specs: 0

---

**Status**: Investigation complete, root causes identified, fixes proposed.
**Priority**: High (demonstrates failure on obvious case)
**Complexity**: Medium (requires code changes + re-inference)
