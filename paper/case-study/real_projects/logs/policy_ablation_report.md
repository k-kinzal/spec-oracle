# Policy Ablation Report

## Summary
- n_scenarios: 21
- group_counts: {'contradiction': 6, 'uncertainty': 9, 'benign_change': 6}
- raw_exact_match_rate: 0.905
- contradiction_detection_rate: must=1.000, may=1.000, binary_strict=1.000
- false_contradiction_rate_on_non_contradiction: must=0.733, may=0.133, binary_strict=0.867
- uncertainty_collapse_rate: must=1.000, may=0.000, binary_strict=1.000

## Scenario Table
| project | scenario | expected(raw) | raw | must | may | binary_strict |
|---|---|---|---|---|---|---|
| PostgreSQL identifier length | stale_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| PostgreSQL identifier length | api_upper_below_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| PostgreSQL identifier length | all_uppers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| PostgreSQL identifier length | all_lowers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| PostgreSQL identifier length | parse_issue | inconclusive | inconclusive | contradictory | consistent | contradictory |
| PostgreSQL identifier length | unit_scale_upper_1024 | consistent | contradictory | contradictory | contradictory | contradictory |
| PostgreSQL identifier length | off_by_one_upper | consistent | consistent | consistent | consistent | contradictory |
| zlib compression level | stale_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| zlib compression level | api_upper_below_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| zlib compression level | all_uppers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| zlib compression level | all_lowers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| zlib compression level | parse_issue | inconclusive | inconclusive | contradictory | consistent | contradictory |
| zlib compression level | unit_scale_upper_1024 | consistent | consistent | consistent | consistent | consistent |
| zlib compression level | off_by_one_upper | consistent | consistent | consistent | consistent | consistent |
| SQLite page size | stale_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| SQLite page size | api_upper_below_requirement_lower | contradictory | contradictory | contradictory | contradictory | contradictory |
| SQLite page size | all_uppers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| SQLite page size | all_lowers_missing | inconclusive | inconclusive | contradictory | consistent | contradictory |
| SQLite page size | parse_issue | inconclusive | inconclusive | contradictory | consistent | contradictory |
| SQLite page size | unit_scale_upper_1024 | consistent | contradictory | contradictory | contradictory | contradictory |
| SQLite page size | off_by_one_upper | consistent | consistent | consistent | consistent | contradictory |

## Interpretation
- `policy_must` prioritizes contradiction signaling on uncertain inputs.
- `policy_may` avoids contradiction escalation on uncertain inputs.
- `binary_strict` is a fail-closed baseline that conflates uncertainty with contradiction.
