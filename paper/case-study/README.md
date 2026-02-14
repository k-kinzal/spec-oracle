# Case Study: Password Policy Layer Integration

This directory contains a reproducible computational case study aligned with
`paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`.

## Layer semantics
- Requirement layer: `min_req <= n <= max_req`
- API layer: `min_api <= n`
- Code layer: `n <= max_code`

Consistency condition:

`max(min_req, min_api) <= min(max_req, max_code)`

## Purpose
- Validate that the closed-form consistency predicate used in Lean case study
  matches brute-force witness search on generated artifact triples.
- This is a reproducibility/sanity check, not a replacement for formal proofs.

## Files
- `password_policy_benchmark.py`: consistency-check runner
- `benchmark_results.json`: generated summary from 5 runs x 200,000 cases
  - includes baseline formula-vs-bruteforce agreement check (20,000 cases)
  - includes witness validity check (`witness_violation_count`, expected `0`)

## Reproduce
```bash
python3 paper/case-study/password_policy_benchmark.py
```
