# Case Study: Password Policy Layer Integration

This directory contains a reproducible computational case study aligned with
`paper/lean/UadfU0/CaseStudy/PasswordPolicy.lean`.

## Layer semantics
- Requirement layer: `min_req <= n <= max_req`
- API layer: `min_api <= n`
- Code layer: `n <= max_code`

Consistency condition:

`max(min_req, min_api) <= min(max_req, max_code)`

## Files
- `password_policy_benchmark.py`: benchmark runner
- `benchmark_results.json`: generated summary from 5 runs x 200,000 cases

## Reproduce
```bash
python3 paper/case-study/password_policy_benchmark.py
```
