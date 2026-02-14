# Real-Project External Validation

This directory validates the interval-consistency checker on constraints
extracted from real OSS documentation/source artifacts.

## Targets
- PostgreSQL identifier length
- zlib compression level
- SQLite page size

## Method
1. Fetch official docs/source pages.
2. Parse numeric bounds from text.
3. Build three-layer artifacts (`requirement`, `api`, `code`).
4. Check consistency using interval intersection.
5. Run mutation tests by forcing `requirement.lower = upper + 1`.

## Run
```bash
python3 paper/case-study/real_projects/external_validation.py
```

## Output
- `external_validation_results.json`
  - `real_results`: extracted constraints and consistency outcome
  - `mutation_results`: contradiction-detection sensitivity check
