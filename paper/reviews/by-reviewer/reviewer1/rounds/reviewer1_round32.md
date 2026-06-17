VERDICT: OK

## Summary
All major blockers have been resolved. The manuscript now provides:

1. **Formal definitions** with clear separation of `supported/refuted/unknown` layer states (§6.2)
2. **U0 indicator separation** into support-based (`u0_support_membership`) and unknown-based (`u0_unknown_only`) metrics
3. **Quantitative mutation criterion** with explicit `/1024` threshold in `unit_mismatch_upper_scale_down_1024`

## Minor Suggestions (non-blocking)

### 1. Terminology Consistency (§6.2)
Current text uses both "support system" and "support coverage" interchangeably. Consider standardizing:
- `u0_support_membership` → "support system indicator" 
- `u0_unknown_only` → "coverage gap indicator"

This clarifies that the first tracks "layers providing support" while the second tracks "coverage holes."

### 2. Mutation Detection Table Enhancement (§6.2)
The mutation results table on page showing `detected_expectation` could benefit from an additional column showing the **delta** between baseline and mutated values. For example:

```
| mutation_id | baseline_upper | mutated_upper | delta | detected |
|-------------|----------------|---------------|-------|----------|
| stale_req   | 63             | 63            | +1    | true     |
| unit_mismatch | 63           | 0             | -63   | true     |
```

This would make the quantitative impact immediately visible.

### 3. Extraction Pattern Documentation (§6.2)
The `extraction_patterns` object in the JSON shows actual regex matches. Consider adding a brief note in the text explaining that these are stored for:
- Reproducibility (what text was actually matched)
- Debugging (when patterns fail)
- Future pattern evolution tracking

### 4. PoC Scope Reminder (§6.3)
The "What we learned" section could benefit from a single-sentence reminder upfront:

> "This PoC validates **technical execution** (source-lock + deterministic replay) rather than general applicability."

This preempts reader confusion about the n=3 sample size.

---

All substantive issues from previous rounds are now addressed. The paper provides a solid mechanization with appropriate scope disclaimers.
