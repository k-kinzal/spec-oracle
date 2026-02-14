# Password Spec Connection Failure - Root Cause Analysis

**Date**: 2026-02-14
**Status**: Root cause identified
**Issue**: Password specs not connected despite obvious semantic equivalence

## Summary

Password-related specifications remain isolated after AI inference due to **confidence threshold being too high** (0.7), which filters out valid REFINES edges that have confidence scores in the 0.5-0.7 range.

## The Problem

### Expected Behavior
These password specs should be connected:
- `[77ad7450]` Layer 0: "Passwords must be at least 8 characters."
- `[34bf0b12]` Layer 0: "Password must be at least 8 characters"
- `[c1ef864d]` Layer 3: "Invariant: password.len() >= 8, ..."
- `[5fdeafb2]` Layer 0: "Specification: Password must be at least 8 characters long"

### Actual Behavior
Only 1 edge exists:
- `[34bf0b12] --[transform]--> [5237d0e8]` (Password 8 chars -> Password 10 chars)

All other password specs remain isolated.

## Root Cause

### Confidence Calculation

From `spec-core/src/extract.rs:414-417`:
```rust
if source.kind == target.kind {
    return Some((
        crate::EdgeKind::Refines,
        similarity * 0.75,  // <-- Confidence multiplier
        "Similar specifications (potential refinement)".to_string(),
    ));
}
```

### The Math

**Case: 34bf0b12 <-> 5fdeafb2**
- Keyword similarity: **0.7778**
- Edge kind: REFINES (same kind, sim > 0.6)
- **Confidence: 0.7778 × 0.75 = 0.5833**
- min_confidence threshold: **0.7**
- **Result: 0.5833 < 0.7 → edge NOT created** ❌

**Case: Cross-layer specs (e.g., 77ad7450 <-> c1ef864d)**
- Keyword similarity: 0.3846
- AI would be called (cross-layer, sim < 0.5)
- Assume AI returns 0.9 (high semantic match)
- Blended similarity: 0.3846 × 0.3 + 0.9 × 0.7 = **0.745**
- Edge kind: FORMALIZES (cross-layer, blended > 0.5)
- **Confidence: 0.745 × 0.9 = 0.6705**
- min_confidence threshold: **0.7**
- **Result: 0.6705 < 0.7 → edge NOT created** ❌
- **Fallback: Added to suggestions for human review** (confidence >= 0.5)

## Why This Happens

### Confidence Multipliers
Different edge types have different confidence multipliers:
- **Synonym**: similarity × 0.95 (highest)
- **Formalizes**: similarity × 0.9
- **DerivesFrom**: similarity × 0.85
- **Refines**: similarity × **0.75** (lowest)

### Threshold Impact
Running AI inference with `--min-confidence 0.7` means:
- **Refines edges need similarity > 0.93** (0.93 × 0.75 = 0.6975 ≈ 0.7)
- **Formalizes edges need similarity > 0.78** (0.78 × 0.9 = 0.702)
- **Synonym edges need similarity > 0.74** (0.74 × 0.95 = 0.703)

This is **extremely high** and filters out most valid relationships.

## Evidence

### Diagnostic Results
```
[34bf0b12] Layer 0 <-> [5fdeafb2] Layer 0
  Keyword similarity: 0.7778
  ⚠️  Would create REFINES edge (sim > 0.6, same kind)
  BUT: confidence = 0.7778 × 0.75 = 0.5833 < 0.7 threshold
```

### Current State
```bash
$ ./target/release/spec list-edges --node 34bf0b12-1e8a-4b8e-979a-bf25adc81568
Found 1 edge(s):
  [75044b15] 34bf0b12 --[transform]--> 5237d0e8
```

Only 1 edge exists (transform), not the expected REFINES edge to 5fdeafb2.

## Why Transform Edge Exists

The transform edge `34bf0b12 -> 5237d0e8` is anomalous:
- Similarity: 0.4444 (< 0.6)
- No rule in `infer_edge_kind` returns Transform
- **Likely manually created** for testing inter-universe consistency

## The 200 Suggestions

From ai-inference-on-self.md:
> **200 suggestions** for human review (confidence 0.5-0.7)

**These likely include the password specs!** The connections exist but were filtered into the suggestion queue instead of being auto-created.

## Solutions

### Option A: Lower Confidence Threshold
```bash
spec infer-relationships-ai --min-confidence 0.5
```

**Pros**: Would create more edges, including password specs
**Cons**: Higher false positive rate

### Option B: Adjust Confidence Multipliers
Increase REFINES multiplier from 0.75 to 0.85:
```rust
crate::EdgeKind::Refines,
similarity * 0.85,  // Was 0.75
```

**Pros**: Better balance between precision and recall
**Cons**: Requires code change

### Option C: Review Suggestions
The 200 suggestions (confidence 0.5-0.7) likely contain valid edges.
Manual review could approve password spec connections.

**Pros**: High precision, no code changes
**Cons**: Requires human time

## Recommendation

**Option A + C** (hybrid approach):
1. Re-run AI inference with lower threshold: `--min-confidence 0.5`
2. Auto-create edges with confidence >= 0.5
3. Review the results to measure false positive rate
4. Adjust threshold based on data

## Impact Assessment

### Current System (min-confidence 0.7)
- **1166 edges created** (high precision)
- **200 suggestions** (require review)
- **168 omissions** remaining (75% reduction from 674)
- **Password specs isolated** (false negative example)

### With min-confidence 0.5
- **Estimate: ~1300-1400 edges** (+100-200 edges)
- **Estimate: ~100-150 omissions** (80-85% reduction)
- **Password specs connected** ✓
- **Potential false positives: ~20-40 edges** (estimated)

## Verification

To verify this hypothesis, check if password specs are in the 200 suggestions:
```bash
# This would require implementing a suggestion review command
spec review-suggestions | grep -i password
```

## Conclusion

**Root cause**: Confidence threshold (0.7) too high for REFINES edges (multiplier 0.75).

**Evidence**: Mathematical calculation shows 34bf0b12 <-> 5fdeafb2 would have confidence 0.5833, which is below threshold but valid.

**Fix**: Lower threshold to 0.5 or adjust multipliers to better balance precision/recall.

---

**Next steps**:
1. Re-run AI inference with --min-confidence 0.5
2. Measure false positive rate
3. Document actual vs. expected results
4. Consider adjusting code if threshold tuning insufficient
