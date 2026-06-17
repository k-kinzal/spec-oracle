# Reviewer 3 Round 37

- Role: Artifact Evaluation Chair (Reproducibility & Empirical Rigor)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This paper presents a rigorous artifact evaluation with strong reproducibility mechanisms (deterministic snapshot replay, hash-locked sources, zero network dependency). The empirical validation demonstrates consistent U0 support across 3 real-world projects with perfect mutation detection (6/6). However, three critical clarifications are required before acceptance: (1) the semantics of support/unknown ratios must be explicitly defined to prevent misinterpretation, (2) the automated extraction claim needs explicit statement in the methodology, and (3) the failure policy's impact on judgements must be documented. With these minor revisions addressing interpretability and methodological transparency, the artifact meets publication standards for empirical software engineering research.

## Strengths
- Strong deterministic replay foundation: The snapshot-based approach with SHA-256 locking (source_lock with 9 URLs, timestamps, and hash verification) enables bit-exact reproduction without network dependency. The extraction_patterns provide full transparency into how intervals were derived from snapshots
- Mutation testing validates detection capability: All 6 mutations (3 stale_requirement_lower + 3 unit_mismatch_upper_scale_down_1024) were correctly detected with 100% expectation satisfaction rate. This demonstrates the framework can distinguish between consistent and contradictory artifact states
- Zero parse failures across all artifacts: parse_issue_count=0 with documented extraction patterns for each project indicates robust automated processing. The regex patterns are traceable (e.g., 'max_identifier_length\s+is\s+([0-9]+)\s+bytes') enabling independent verification
- Complete artifact provenance chain: Each of 3 real projects (PostgreSQL, zlib, SQLite) has requirement/api/code layers with explicit source URLs, retrieval timestamps (UTC), and human-readable notes explaining what each interval represents

## Required Fixes
- Clarify the semantics of 'avg_support_ratio=0.778' and 'avg_unknown_ratio=0.222' in the manuscript. These metrics are ambiguous: do they represent artifact-layer coverage, confidence levels, or partial membership? The JSON shows code layers often have null lower bounds (marked 'unknown'), but the paper must explicitly define what 'support' vs 'unknown' means for U0 validation to avoid reader misinterpretation as measurement error
- Add explicit statement in Section 5 (Case Study) that the extraction is 'automatic_regex_no_manual_edit_offline_snapshot_replay' as documented in the JSON. Currently the manuscript implies but does not state that regex extraction was fully automated without manual correction - this is critical for reproducibility claims
- Document the 'none' failure policy semantics ('may' interpretation) in the manuscript methodology section. The JSON shows failure_policy='none' with none_semantics='may', meaning incomplete intervals are treated permissively. Readers must understand this design choice affects the consistency judgements

## Optional Fixes
- Consider adding explicit timestamp or version information in the manuscript text itself (not just JSON metadata) to contextualize when the snapshot was taken, strengthening the temporal validity discussion
- The mutation detection rate (6/6) is perfect but based on only 2 mutation types across 3 projects - consider acknowledging this limited mutation operator diversity as a threat to validity
- Add brief discussion of the snapshot maintenance burden: how often would snapshots need refreshing in a real deployment scenario to remain meaningful?
