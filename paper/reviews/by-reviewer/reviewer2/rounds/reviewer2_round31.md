VERDICT: OK

## Rationale

### Prior Blocker Resolution

1. **May-side coverage meaning (Blocker #1)**  
   - §4.7 now rigorously distinguishes must/may as **運用ポリシー** (operational policy) projections from three-valued judgement, not as semantic baseline change.
   - `preimageMay` definition + inclusion theorems (`UAndOn_subset_UAndMayOn`, `UAndMayOn_empty_implies_UAndOn_empty`) are mechanically verified in Lean.
   - §6.4 negative example (regex drift) concretely demonstrates must/may divergence with actual PoC logs (`graceful_must.log` vs `graceful_may.log`), eliminating abstract hand-waving.

2. **Mutation expectation rigor (Blocker #2)**  
   - §6.2 mutation results now record **pre-fixed criterion** (`judgement == contradictory` for stale, `upper' <= floor(upper/2)` for unit_mismatch) alongside detection_basis field.
   - Expectation evaluation logic is explicit: `detected_expectation: stale_judgement == "contradictory"` for contradiction-type, `unit_expectation_detected = unit_upper is not None and unit_upper <= expected_upper_threshold` for change-type.
   - JSON output preserves `expected_outcome` + `detected_expectation` + `detection_basis` as separate fields, cleanly separating expectation declaration from actual result evaluation.

### Conservative Acceptance Gate

Both prior major issues are now resolved with formal rigor (Lean mechanization) + concrete demonstration (PoC logs). No new major-level blockers detected in current draft.

### Minor Polish Opportunity (Non-blocking)

- §6.2 table "区間交差判定" could add one-line caption clarifying it's baseline (pre-mutation) intersection results.
- §4.8 table "定理適用境界" might benefit from explicit "PoC検証状況" = "未検証（RQ6再実行性のみ対象）" for all theory rows except §4.7, to prevent reader from inferring adequacy theorems were PoC-validated.

---

**Overall**: draft achieves conservative acceptance threshold. Proceed to final polishing without structural revision.
