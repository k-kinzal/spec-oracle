# Case Study

This directory contains two case-study tracks:
1. internal consistency check aligned with `paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`
2. external validation on real OSS artifacts

## Layer semantics
- Requirement layer: `min_req <= n <= max_req`
- API layer: `min_api <= n`
- Code layer: `n <= max_code`

Consistency condition:

`max(min_req, min_api) <= min(max_req, max_code)`

## Purpose
- Validate that the closed-form consistency predicate used in Lean case study
  matches brute-force witness search on generated artifact triples.
- Validate external applicability on real project artifacts (PostgreSQL/zlib/SQLite).
- Provide reproducible extraction evidence with source lock metadata and snapshots.

## Files
- `password_policy_benchmark.py`: consistency-check runner
- `benchmark_results.json`: generated summary from 5 runs x 200,000 cases
  - includes baseline formula-vs-bruteforce agreement check (20,000 cases)
  - includes witness validity check (`witness_violation_count`, expected `0`)
- `real_projects/external_validation.py`: real-artifact extraction + consistency evaluation
- `real_projects/external_validation_results.json`: extracted constraints and outcomes
- `real_projects/external_validation_sources.lock.json`: source URL/SHA256/timestamp lock
- `real_projects/snapshots/`: fetched source snapshots referenced by the lock file
- `real_projects/README.md`: source URLs and run instructions

## Reproduce
```bash
python3 paper/case-study/password_policy_benchmark.py
python3 paper/case-study/real_projects/external_validation.py
```
