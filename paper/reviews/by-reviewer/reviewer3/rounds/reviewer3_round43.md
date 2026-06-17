# Reviewer 3 Round 43

- Role: Round 43 External Validation Reproducibility Reviewer
- Recommendation: Accept
- Pass Gate: true

## Summary
Round 43 demonstrates publication-grade reproducibility infrastructure. The external_validation_results.json exhibits: (1) deterministic offline snapshot replay with SHA-256 source locking eliminating network dependency, (2) complete automation evidence via extraction_patterns showing regex-based field derivation with match citations, (3) consistent graceful_may semantics (failure_policy=none, none_semantics=may) applied uniformly across 3/3 real projects with 100% detection of 6/6 mutation expectations, and (4) comprehensive jq-reproducible metrics (avg_support_ratio=0.778, mutation detection 100%). All acceptance criteria met without publication-blocking issues.

## Strengths
- Deterministic replay architecture: network_required=false with SHA-256 source_lock array providing cryptographic verification of 9 snapshot files
- Automation transparency: extraction_patterns field documents every regex match (e.g., 'max_identifier_length is 63 bytes' → requirement.upper=63) enabling full audit trail
- Graceful degradation consistency: failure_policy=none + none_semantics=may implemented uniformly across manuscript/README/logs with explicit lifted_membership.may showing code layer tolerance
- Mutation testing validation: 6/6 expected outcomes detected (3 stale_requirement_lower contradictions + 3 unit_mismatch scale-down detections) proving sensitivity
- Interval algebra robustness: all 3 real projects show interval_intersection consistency with explicit lower/upper bounds (PostgreSQL [1,63], zlib [-1,9], SQLite [512,65536])
- Zero parse issues: parse_issue_count=0 with explicit parse_issues=[] demonstrating stable extraction pipeline
- Layer-stratified metrics: support_frequency/unknown_frequency broken down by requirement/api/code enabling granular U0 coverage analysis

## Required Fixes
- None

## Optional Fixes
- Consider adding extraction_patterns.*.retrieved_at field linking patterns to source_lock timestamps for provenance completeness
- Document regex escaping convention in extraction_patterns (e.g., why '\\\\s+' vs standard '\\s+' - appears to be JSON double-escaping)
- Add mutation_results.*.baseline_intersection field showing pre-mutation interval for easier diff comparison
- Include snapshot file size metrics in source_lock to detect truncated downloads in future replay
- Consider parameterizing unit_mismatch scale factor (currently hardcoded 1024) for broader applicability testing
