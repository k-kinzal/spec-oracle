# Round 31 Reviewer Summary

- Date: 2026-02-15
- Scope:
  - `paper/manuscript/uadf_u0_spec_proof.md`
  - `paper/case-study/real_projects/external_validation.py`
  - `paper/case-study/real_projects/external_validation_results.json`

## Verdicts

- Reviewer 1 (`paper/reviews/reviewer1_round31.md`): `VERDICT: OK`
- Reviewer 2 (`paper/reviews/reviewer2_round31.md`): `VERDICT: OK`
- Reviewer 3 (`paper/reviews/reviewer3_round31.md`): `VERDICT: OK`

## Confirmed Resolutions

1. may 側指標の意味論（support vs unknown）を三値 `layer_status` に分離し、`U0` 指標を support/unknown 系で記録。
2. mutation 検出期待を事前固定の定量条件へ変更（`raw_judgement=contradictory` / `upper' <= floor(upper/2)`）。
3. RQ6 を source-lock 付き deterministic replay に限定し、理論定理の適用境界を §4.8 で明示。

## Residual Notes

- 残件は編集上の軽微修正のみ（説明文の可読性向上、脚注追記レベル）。
