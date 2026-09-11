/**
 * Frozen failed production baseline measured on 2026-07-16 against
 * spec_oracle_validation_20260714 (5,161 Specifications, 103,378 retained
 * affinity edges). This remains a historical comparison for diagnosing how a
 * candidate changes factual-neighbor retention; it is not a completion
 * threshold.
 * neighborhood scale; this file is not regenerated during candidate tuning.
 */
export const FAILED_ACTUAL_NEIGHBORHOOD_RECALL = {
  10: 0.1354663971003732,
  20: 0.12228296305793539,
  50: 0.13584685722302478,
} as const satisfies Readonly<Record<number, number>>;
