# Reviewer 3 Round 39

- Role: Artifact/Reproducibility Reviewer (Round 39)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The external validation results demonstrate strong reproducibility infrastructure with deterministic replay conditions, comprehensive snapshot locking (9 sources with SHA256 hashes), and clear none-semantics="may" policy. The mutation validation (6/6 detected expectations) provides robustness evidence. However, minor clarifications are needed: (1) explicit documentation of the "may" semantics interpretation in the manuscript, (2) clearer mapping between extraction_patterns and the automatic_regex_no_manual_edit claim, and (3) human-readable summary of deterministic replay guarantees. The offline snapshot replay architecture is sound and the 100% mutation detection rate suggests the validation is robust. With these documentary improvements, the artifact meets publication standards.

## Strengths
- Comprehensive source locking with SHA256 hashes for all 9 external sources, enabling deterministic offline replay without network dependency
- Clear failure_policy='none' with none_semantics='may' explicitly documented in results JSON, providing unambiguous interpretation of unknown intervals
- Strong mutation validation: 6/6 expected outcomes detected (3 contradictory mutations + 3 scale-down mutations), demonstrating robustness of the consistency detection mechanism
- Extraction patterns are documented per project with concrete regex matches, enabling verification of the 'automatic_regex_no_manual_edit' claim
- Lifted membership semantics (must/may) correctly distinguish supported vs unknown layers, avoiding false claims about U0 support

## Required Fixes
- Add explicit explanation of none_semantics='may' interpretation to manuscript Section 5 or Appendix: clarify that unknown intervals (null bounds) are treated as 'may belong to U0' rather than falsification, and justify why this is conservative for external validation
- Document deterministic replay guarantees in README.md: state that reproduction requires (1) Python 3.x with regex, (2) snapshot files in snapshots/ directory, (3) no network access, and (4) results should be byte-identical to external_validation_results.json
- Map extraction_patterns in results JSON to automatic extraction claim: either show how all patterns are programmatically derived from artifact structure, or clarify if any patterns were manually crafted and why that still satisfies 'no_manual_edit_offline_snapshot_replay'

## Optional Fixes
- Add mutation validation explanation to manuscript: the 100% detection rate (6/6) strengthens confidence in consistency mechanism, worth mentioning as validation meta-property
- Consider adding a one-line hash verification command to reproduce.sh: e.g., 'sha256sum -c snapshot_checksums.txt' to make verification explicit
- Add timestamp range or version note: external sources were retrieved 2026-02-14; note if/when snapshot refresh is needed to maintain external validity
