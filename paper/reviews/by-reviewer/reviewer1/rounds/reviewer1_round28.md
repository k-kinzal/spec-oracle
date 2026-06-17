# Journal-Style Review: VERDICT

**VERDICT: OK**

---

## Summary

The revised manuscript and PoC outputs successfully address the three blocking concerns raised in prior rounds. The work is now ready for acceptance with only minor refinual suggestions remaining.

### Resolution of Blocking Issues

1. **U0 evaluation informativeness (RESOLVED)**
   - §6.2 now outputs `u0_membership_must/may`, `coverage_count_must/may`, `coverage_ratio_must/may`, and `u0_support_layers_must/may` for both baseline and mutation cases
   - `external_validation_results.json` demonstrates concrete usage: baseline shows `coverage_ratio_must = 1.0` (all 3 layers), while mutations show `mutated_coverage_count_must = 2` (e.g., PostgreSQL stale requirement mutation: `u0_support_layers_must: ["api", "code"]`)
   - This quantitative tracking makes U0's role as "root coverage baseline" empirically observable rather than definitional

2. **3-valued vs policy judgement separation (RESOLVED)**
   - §4.7 and §6.2 now cleanly separate `judgement ∈ {consistent, contradictory, inconclusive}` from `policy_judgement` (must/may projection)
   - `external_validation.py:classify_uand` returns raw 3-valued judgement; `apply_none_policy` is explicitly separate
   - Results JSON records both: `"judgement": "consistent"` and `"policy_judgement": "consistent"` independently
   - §6.4's negative example demonstrates practical impact: same drift input yields `judgement=inconclusive` in both modes, but `policy_judgement=contradictory` (must) vs `consistent` (may)

3. **Mutation expected outcome definition (RESOLVED)**
   - §6.2 now defines two mutation types with explicit expectations:
     - `stale_requirement_lower`: `expected_outcome = "policy_judgement=contradictory"`, detected via `policy_judgement == "contradictory"`
     - `unit_mismatch_upper_scale_down_1024`: `expected_outcome = "policy_or_interval_or_coverage_change"`, detected via multi-field diff (`detection_basis` list)
   - Results show 6/6 detected with explicit basis tracking (e.g., `"detection_basis": ["policy_judgement_changed", "raw_judgement_changed", "intersection_changed", "coverage_count_must_changed", "coverage_count_may_changed"]`)
   - This is no longer a circular "mutation → change → detected" but a pre-declared expectation with falsifiable detection criteria

---

## Residual Minor Suggestions

1. **§0.1 "root specification" terminology**  
   Line: "It constructs U0 (the root specification) from diverse artifacts..."  
   Issue: "root specification" might suggest U0 is *the* root spec, conflating it with U*.  
   Suggestion: "It constructs U0 (the root **coverage baseline**) from diverse artifacts..." to align with §3.1's explicit framing.

2. **§4.3 adequacy theorem scope boundary**  
   Lines: "The following theorem is **an abstract relation E** result..."  
   Issue: Helpful, but could be clearer about what's missing for practical use.  
   Suggestion: Add one sentence: "Applying these theorems to a specific extractor (regex/LLM) requires a separate proof that the extractor satisfies the soundness/completeness premises for relation E."

3. **§6.2 mutation "sanity check" framing**  
   Line: "...sensitivity confirmation (sanity check)..."  
   Issue: "Sanity check" might downplay the empirical contribution.  
   Suggestion: "...sensitivity confirmation (**boundary behavior validation**)..." — frames it as purposeful validation of detection logic, not just a throwaway check.

4. **§9 limitation #13 trace instantiation gap**  
   Line: "PoC is `Ω_art` (artifact bundle) ... `Ω=Trace` extension unverified."  
   Issue: Correct, but could note which theorem would need re-instantiation.  
   Suggestion: Append: "Re-instantiation would require reproving theorems in §4.1–4.3 for `proj_i : Trace → Option β_i` rather than `ArtifactBundle → Option β_i`."

5. **Appendix B §12.1 `apply_none_policy` docstring**  
   Code block has clear logic but no inline comment explaining the vacuous truth case.  
   Suggestion: Add comment:
   ```python
   def apply_none_policy(judgement: Judgement, none_semantics: NoneSemantics) -> Judgement:
       if judgement != "inconclusive":
           return judgement
       # inconclusive + must → strict (contradictory); inconclusive + may → permissive (consistent)
       return "contradictory" if none_semantics == "must" else "consistent"
   ```

---

## Confirmation of Non-Blocking Status

- **Scope declarations**: §0.3, §6.2, §9 clearly bound the PoC to `n=3` convenience sample, numeric constraints only, and technical reproducibility (not statistical inference). No overreach.
- **Assumption tracking**: §2.4–2.7, §4.1–4.3 explicitly label which premises are assumed vs. proven. RQ5/RQ6 boundary is crisp.
- **Reproducibility artifacts**: `source_lock` with SHA256, offline replay mode, `reproduce.sh` multi-mode script — all present and documented.
- **Mechanization completeness**: 59 theorems, 1502 LOC, `lake build` succeeds, no `open Classical`, §13 full provenance — audit trail complete.

All blocking concerns are now resolved. The above suggestions are refinual polish, not gates to acceptance.
