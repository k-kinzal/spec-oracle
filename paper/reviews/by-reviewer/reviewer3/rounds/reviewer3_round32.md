VERDICT: NG

## Major Blockers

### 1. **Code-Manuscript Inconsistency: `classify_layer_status` Logic**
**Location**: `external_validation.py:315-323` vs Manuscript §6.2

**Code**:
```python
def classify_layer_status(
    layer: LayerBounds,
    *,
    layer_has_parse_issue: bool,
    ) -> LayerStatus:
    if layer_has_parse_issue:
        return "unknown"
    if layer.lower is not None and layer.upper is not None:
        return "supported" if layer.lower <= layer.upper else "refuted"
    return "supported"
```

**Problem**: The final `return "supported"` contradicts manuscript's definition of layer status. When `layer.lower is None OR layer.upper is None` (partial bounds), the code returns `"supported"`, but manuscript §6.2 states:

> `supported_i(x) :⇔ ∃y, proj_i(x)=some(y) ∧ y∈A(i)`

With partial bounds (e.g., only upper exists), the layer should return `"unknown"` (because `proj_i` effectively returns `none` for incomplete extraction), not `"supported"`.

**Expected**: `return "unknown"` when bounds are incomplete.

---

### 2. **JSON-Manuscript Mismatch: zlib Mutation Detection Claims**
**Location**: `external_validation_results.json` line 261 vs Manuscript §6.2

**JSON**:
```json
{
  "project": "zlib compression level",
  "mutation_id": "unit_mismatch_upper_scale_down_1024",
  "expected_outcome": "intersection_upper_at_most_floor_baseline_div_1024",
  "expected_upper_threshold": 0,
  "detected_expectation": true,  // ← CLAIMED DETECTED
  "policy_judgement": "consistent",  // ← BUT CONSISTENT!
  "judgement": "consistent",
  "mutated_intersection_lower": -1,
  "mutated_intersection_upper": 0
}
```

**Problem**: 
- Manuscript §6.2 states mutation should detect "upper bound change" (`upper' <= floor(upper/1024)`)
- JSON shows `detected_expectation: true` BUT `policy_judgement: "consistent"`
- This is **logically contradictory**: if mutation was detected as expected, why is it still consistent?
- The threshold check (`upper' <= 0`) is satisfied, but this doesn't mean the mutation *detection* worked—it means the bounds still happen to overlap at `[-1,0]`.

**Expected**: Either clarify that "detection" means "threshold met" (not "inconsistency introduced"), OR fix the detection logic to require `judgement != baseline_judgement`.

---

### 3. **Code-Manuscript Inconsistency: `U0_support_membership` Definition**
**Location**: `external_validation.py:562-576` vs Manuscript §6.2 PoC definitions

**Code** (line 562):
```python
u0_membership_must = any(lifted_must.values())
u0_membership_may = any(lifted_may.values())
# ...
support_count = status_count(layer_status, "supported")
# ...
"u0_support_membership": support_count > 0,
```

**Manuscript** (§6.2):
> `U0_support(x)` (`u0_support_membership`) is `∃i, supported_i(x)`

**Problem**: The code computes `support_count > 0` **after** already computing `u0_membership_must` which is `any(lifted_must.values())`. These should be **identical** by manuscript's definition, but they're calculated from different sources:
- `u0_membership_must` uses `status_to_membership(..., "must")`
- `u0_support_membership` uses raw `support_count`

The manuscript claims they're the same (`∃i, supported_i(x)`), but the code has two separate paths that could diverge.

**Expected**: Unify or prove equivalence, or clarify why two separate calculations exist.

---

## Summary
Three **major inconsistencies** block acceptance:
1. Layer status logic returns `"supported"` for partial bounds (should be `"unknown"`)
2. zlib mutation claims "detected" while remaining "consistent" (contradictory)
3. `U0` support membership calculated twice via different paths (redundant/unclear)

These are **semantic blockers**, not typos. Fix required before acceptance.
