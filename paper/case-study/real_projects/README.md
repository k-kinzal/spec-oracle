# Real-Project Feasibility Validation (RQ6)

This directory contains a **preliminary feasibility demonstration** for the
UAD/f PoC extraction pipeline.
It is not a statistical external-validation study.

## Scope
- Target constraints:
  - PostgreSQL identifier length
  - zlib compression level
  - SQLite page size
- Layer model:
  - `requirement`, `api`, `code`
- Output intent:
  - deterministic replay with source lock
  - tri-valued judgement + policy projection
  - mutation expectation tracking

## Required Files (Reproducibility Package)
- `paper/case-study/real_projects/external_validation.py`
- `paper/case-study/real_projects/reproduce.sh`
- `paper/case-study/real_projects/external_validation_sources.lock.json`
- `paper/case-study/real_projects/snapshots/*`
- `paper/case-study/real_projects/external_validation_results.json` (reference output schema/sample)

## Method Summary
1. Load artifacts from snapshots (offline lock) or fetch online.
2. Extract numeric bounds via regex into layer artifacts.
3. Build tri-state layer status:
   - `supported`: two-sided interval exists and `lower <= upper`
   - `invalid`: two-sided interval exists and `lower > upper`
   - `unknown`: extraction failed or one-sided bound only
4. Compute:
   - `judgement`: raw 3-valued result (`consistent` / `contradictory` / `inconclusive`)
   - `policy_judgement`: policy projection by `--none-semantics`
5. Run two pre-fixed mutation families:
   - `stale_requirement_lower`
   - `unit_mismatch_upper_scale_down_1024`

Mutation intent:
- `stale_requirement_lower`: simulates stale documentation where requirement lower bound exceeds current implementation/API upper bound.
- `unit_mismatch_upper_scale_down_1024`: simulates unit confusion (e.g., bytes vs KiB) by scaling requirement upper bound.

## Replay Modes
Use `reproduce.sh` to run all three modes:
- `external_validation_offline.log`
  - offline fail-fast
- `external_validation_graceful_must.log`
  - graceful + must (`inconclusive -> contradictory`)
- `external_validation_graceful_may.log`
  - graceful + may (`inconclusive -> consistent`)

## Run
```bash
cd paper/case-study/real_projects
bash reproduce.sh
```

## Minimal Verification Checklist
```bash
cd paper/case-study/real_projects
jq '{n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation}' logs/external_validation_offline.log
```

Expected checks:
- `n_real_projects == 3`
- `raw_judgement_distribution.consistent == 3`
- `mutation_detected_by_expectation == 6`

Notes:
- `date` is runtime-dependent and not part of deterministic comparison.
- Python dependency is stdlib-only (no extra pip packages required).
- Verified environment in manuscript: Python `3.9.6` on Darwin (`paper/manuscript/uadf_u0_spec_proof.md`, §7.2).

## Output Schema (minimum keys)
`external_validation_results.json` should include:
- summary keys:
  - `n_real_projects`
  - `raw_judgement_distribution`
  - `policy_judgement_distribution`
  - `n_u0_support_indicator`
  - `n_u0_unfalsified_indicator`
  - `n_u0_unknown_only`
  - `mutation_detected_by_expectation`
- detailed keys:
  - `real_results[*].layer_status`
  - `real_results[*].lifted_membership`
  - `mutation_results[*].expected_outcome`
  - `mutation_results[*].expectation_satisfied`
  - `extraction_patterns`

## Outputs
- `external_validation_results.json`
  - `real_results`: extracted constraints + tri-state outputs
  - `mutation_results`: expected-outcome checks
  - `source_lock`: URL/SHA256/timestamp/snapshot metadata
  - `extraction_patterns`: regex + matched fragments (pattern transparency)
- `external_validation_sources.lock.json`
  - compact lock file (URL/SHA256/timestamp/snapshot path)
- `logs/*`
  - replay outputs for each mode
