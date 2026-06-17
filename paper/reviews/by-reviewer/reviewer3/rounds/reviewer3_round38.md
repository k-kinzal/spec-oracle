# Reviewer 3 Round 38

- Role: Artifact Evaluation Committee (Round 38 Final Review) - Reproducibility & Claims Validation
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This artifact evaluation confirms the reproducibility infrastructure is largely sound. The external_validation_results.json demonstrates: (1) automatic regex extraction with no manual edits (extraction_mode: automatic_regex_no_manual_edit_offline_snapshot_replay), (2) offline snapshot replay capability (network_required: false), (3) SHA-256 locked sources with retrieval timestamps, (4) explicit none-semantics handling (none_semantics: may, failure_policy: none). All 3 real projects show consistent U0 support, all 6 mutation tests behave as expected. However, minor documentation gaps remain regarding: (a) explicit replay validation procedure description in manuscript, (b) none-semantics impact quantification in result interpretation, (c) extraction pattern validation methodology. These are easily addressable through documentation enhancements without re-running experiments.

## Strengths
- Reproducibility infrastructure is production-grade: SHA-256 source locks with UTC timestamps, offline snapshot replay, deterministic extraction patterns logged per project
- Automatic extraction claim is verifiable: extraction_mode explicitly states no_manual_edit, extraction_patterns section logs every regex used with match evidence
- Mutation testing validates detection: 6/6 mutations detected as expected (3 contradictory, 3 boundary changes), demonstrating framework sensitivity to specification drift
- None-semantics handling is explicit: failure_policy and none_semantics documented in results; lifted_membership shows must/may distinction per layer
- Real-world projects selection is credible: PostgreSQL, zlib, SQLite are widely-deployed systems with stable documented specifications

## Required Fixes
- Document replay validation procedure: Manuscript should explicitly state how readers can verify snapshot replay produces identical results (e.g., running reproduce.sh with --offline flag uses locked snapshots in snapshots/ directory bypassing network)
- Quantify none-semantics impact on conclusions: Current results show 2/9 layer-intervals have null bounds (unknown); manuscript should discuss whether 22% unknown rate affects U0 support claims or remains acceptable under may semantics
- Add extraction pattern validation section: Briefly explain how regex patterns were validated (e.g., manual spot-check against raw snapshots, pattern matched expected format) to address how do we know the regexes are correct concern

## Optional Fixes
- Consider adding Threats to Validity subsection mentioning: (a) regex patterns may miss edge cases in documentation phrasing, (b) snapshot timing may not represent all spec versions, (c) 3 projects is small sample
- Provide diff command in reproduce.sh showing snapshots/ content matches source_lock SHA-256 hashes for full auditability
- Add table in manuscript mapping each project layer-status (supported/unknown) to specific artifact fields to make none-semantics concrete
