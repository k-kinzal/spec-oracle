# Root Cause: AI Inference Fails to Detect Same-Layer Duplicates

**Date**: 2026-02-14
**Status**: Critical Bug Identified

## Problem

spec-oracle has 577 specifications with obvious duplicates that aren't being detected:

1. **[b18aad55]** "Server must detect specification omissions"
   **[3d039c75]** "Server must strictly define specifications and detect omissions"

2. **[58bc35f8]** "Server must detect specification contradictions"
   **[a8352d89]** "Server must detect contradictions in specifications"

Both pairs are semantically equivalent but `detect-potential-synonyms` and `infer-relationships-ai` fail to catch them.

## Root Cause

The AI semantic matching in `spec-core/src/extract.rs` has a design flaw:

### Code Analysis: extract.rs:334-360

```rust
fn calculate_semantic_similarity_with_ai(...) -> f32 {
    // First try simple similarity
    let simple_sim = self.calculate_semantic_similarity(text1, text2);

    // If similarity is already high, no need for AI
    if simple_sim > 0.5 {
        return simple_sim;  // Line 346-348
    }

    // If different formality layers and low simple similarity, try AI
    if layer1 != layer2 {  // Line 351 - AI ONLY for cross-layer!
        if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
            return simple_sim * 0.3 + ai_sim * 0.7;
        }
    }

    simple_sim  // Line 359 - Falls back to simple keyword matching
}
```

### The Flaw

**Line 351**: AI is ONLY called when `layer1 != layer2` (different formality layers).

For same-layer duplicates:
- Both are constraints at the same formality layer
- AI is never invoked
- Falls back to keyword-based Jaccard similarity
- Synonym detection requires similarity > 0.8 (line 371 in extract.rs)

### Why Duplicates Aren't Caught

For "Server must detect specification omissions" vs "Server must strictly define specifications and detect omissions":

**Keyword matching**:
- Common words: {server, must, detect, specification(s), omissions}
- Unique words: {strictly, define, and}
- Jaccard similarity: ~5/8 = 0.625

**Result**: 0.625 < 0.8 threshold → NOT detected as synonyms

### Why AI Would Work

An AI would recognize:
- "detect omissions" ⊂ "define specifications and detect omissions"
- Second refines/includes first
- Should be marked as REFINES or SYNONYM

But AI is NEVER CALLED because both are at the same formality layer.

## Additional Issue: Early Return at Line 346-348

Even if we fix the cross-layer restriction, there's another bug:

```rust
if simple_sim > 0.5 {
    return simple_sim;  // Returns WITHOUT checking AI!
}
```

For pairs with 0.5 < similarity < 0.8:
- Keyword matching gives ~0.6
- Function returns 0.6 immediately
- AI is never called
- 0.6 < 0.8 threshold → NOT detected

This means AI is ONLY used when:
1. Different formality layers (layer1 != layer2)
2. AND simple similarity <= 0.5

**This is the opposite of what we want!** We want AI for:
- Moderate keyword overlap (0.4-0.8 range)
- Where simple matching is ambiguous

## Impact

The "AI-powered semantic matching" feature is effectively disabled for:
- Same-layer duplicates (both constraints, both assertions, etc.)
- Moderate keyword overlap cases (0.5-0.8)

Result: **spec-oracle cannot manage its own specifications** - obvious duplicates go undetected.

## The Fix

Modify `calculate_semantic_similarity_with_ai` in `spec-core/src/extract.rs`:

```rust
fn calculate_semantic_similarity_with_ai(...) -> f32 {
    let simple_sim = self.calculate_semantic_similarity(text1, text2);

    // If similarity is very high (>0.8), trust keyword matching
    if simple_sim > 0.8 {
        return simple_sim;
    }

    // For moderate similarity (0.4-0.8), use AI to disambiguate
    // This catches same-layer duplicates that keyword matching misses
    if simple_sim >= 0.4 {
        // Try AI regardless of formality layer
        if let Some(ai_sim) = ai.semantic_similarity(text1, text2, layer1, layer2) {
            // Blend: give more weight to AI for disambiguation
            return simple_sim * 0.3 + ai_sim * 0.7;
        }
    }

    // For very low similarity (<0.4), skip AI (too expensive, low probability)
    simple_sim
}
```

**Key changes**:
1. Raise early return threshold from 0.5 → 0.8 (trust high keyword overlap)
2. Remove `layer1 != layer2` restriction (allow AI for same-layer)
3. Use AI for moderate similarity (0.4-0.8 range) where disambiguation helps

## Also Need to Fix: ai_semantic.rs

The `AISemantic::semantic_similarity` also has the cross-layer restriction at line 52-54:

```rust
// Early exit if not cross-layer
if layer1 == layer2 {
    return None;
}
```

This MUST be removed to allow same-layer AI matching.

## Expected Outcome

After fix:
1. Run `spec infer-relationships-ai --min-confidence 0.7`
2. AI compares all pairs with 0.4-0.8 keyword similarity
3. Detects 3+ obvious duplicate pairs
4. Creates synonym/refines edges
5. Omissions drop from 600+ to ~150-200

This will validate that spec-oracle actually works for real specification management.

## Why This Matters

From honest-assessment.md:

> "If spec-oracle can't manage its own 536 specifications better than manual tracking, it hasn't achieved the goal."

The architecture exists. The AI integration exists. But a simple implementation bug prevents it from working.

**This is the difference between aspirational claims and validated reality.**

## Next Steps

1. Fix `spec-core/src/ai_semantic.rs` line 52-54 (remove cross-layer restriction)
2. Fix `spec-core/src/extract.rs` line 334-360 (use AI for same-layer moderate similarity)
3. Rebuild: `cargo build --release`
4. Run AI inference: `spec infer-relationships-ai --min-confidence 0.7`
5. Verify duplicates are detected
6. Document actual results vs. claimed results
7. Commit only if validation succeeds

---

**Status**: Ready for implementation
