# Build Evidence Snapshot

This appendix records one reproducible local run for artifact integrity checks.
It is not a replacement for external CI, but it provides concrete command/output evidence tied to this package state.

## Commands

```bash
bash paper/formal-methods/appendix/reproduce_formal.sh

# equivalent manual commands:
cd paper/lean
~/.elan/bin/lake clean
~/.elan/bin/lake build
for thm in \
  U0On_monotone UAndOn_antitone UAndOn_subset_U0On UAndOn_empty_eq_univ \
  consistent_iff_exists_UAndOn_pair U0_least_upper_bound_iff UAndOn_greatest_lower_bound_iff \
  lifted_transfer preimage_compose preimage_subset_semanticPullback_of_sound \
  semanticPullback_subset_preimage_of_complete preimage_eq_semanticPullback \
  preimageMay_subset_semanticPullbackMay_of_sound semanticPullbackMay_subset_preimageMay_of_complete \
  preimageMay_eq_semanticPullbackMay
do
  rg -n "^theorem ${thm}\\b" UadfU0 >/dev/null
done
rg -n '\bsorry\b' UadfU0 || true
rg -n '^theorem ' UadfU0 | wc -l
```

## Recorded outputs

- traceability-path checks (including `naive_totalization_adds_spurious_witness` in expected file): pass
- `Build completed successfully (46 jobs).`
- primary-theorem membership checks: `15/15` found
- `sorry` matches: `0`
- theorem declarations (informational): `74`
- LOC under `paper/lean/UadfU0` (informational): `1807`

## Hash checks

```bash
python3 - <<'PY'
import hashlib, pathlib
for path in ["paper/lean/lake-manifest.json", "paper/lean/lean-toolchain", "paper/lean/lakefile.lean"]:
    p = pathlib.Path(path)
    print(path, hashlib.sha256(p.read_bytes()).hexdigest())
PY
```

Expected values:
- `paper/lean/lake-manifest.json`: `8c098d788704fb7c279c7004a1f492723bd892acf2500483665ae39e7a00a6e7`
- `paper/lean/lean-toolchain`: `d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb`
- `paper/lean/lakefile.lean`: `74729ef754fd55cdc1add76accac3f5632e06fe934e8d9f4f8ed0e16d6b51891`
- key source hashes are also checked in `reproduce_formal.sh` for traceability-critical files (Definitions/U0Spec/InterLayer and selected example/case-study files).
