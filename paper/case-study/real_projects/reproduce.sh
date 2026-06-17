#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}"

mkdir -p logs
LOCK_FILE="external_validation_sources.lock.json"
DRIFT_LOCK_FILE="logs/regex_drift_lock.json"
DRIFT_SNAPSHOT_FILE="logs/regex_drift_snapshot.txt"

if [[ ! -f "${LOCK_FILE}" ]]; then
  echo "Missing lock file: ${LOCK_FILE}" >&2
  exit 1
fi

if [[ ! -f "${DRIFT_LOCK_FILE}" ]]; then
  echo "Missing drift lock file: ${DRIFT_LOCK_FILE}" >&2
  exit 1
fi

if [[ ! -f "${DRIFT_SNAPSHOT_FILE}" ]]; then
  echo "Missing drift snapshot file: ${DRIFT_SNAPSHOT_FILE}" >&2
  exit 1
fi

LOCK_BACKUP="$(mktemp)"
cp "${LOCK_FILE}" "${LOCK_BACKUP}"
cleanup() {
  cp "${LOCK_BACKUP}" "${LOCK_FILE}"
  rm -f "${LOCK_BACKUP}"
}
trap cleanup EXIT

python3 - <<'PY'
import hashlib
import pathlib
import sys

expected = {
    "external_validation.py": "ea820e0d86324d2c7583e963cd5e0a9e49c2f2f827e8e0a8d2f560bea8b649d7",
    "external_validation_sources.lock.json": "0c34d22165d3f032d3929f8333657fa25fa65aa55542749d83dba031f11a4793",
    "logs/regex_drift_lock.json": "1f31c8e65688f680abc9b4781ea41aca7f4ebe142f1838f74b7698d5e2517330",
    "logs/regex_drift_snapshot.txt": "0d2d319f9edd4dbf2c80351bf1bcbfd3264552999ca557ad9598ac833ea4480c",
}

for rel, want in expected.items():
    path = pathlib.Path(rel)
    got = hashlib.sha256(path.read_bytes()).hexdigest()
    if got != want:
        print(f"SHA256 mismatch: {rel} expected={want} actual={got}", file=sys.stderr)
        raise SystemExit(1)
print("SHA256 precheck OK.")
PY

echo "[1/6] offline fail-fast replay"
python3 external_validation.py \
  --offline-lock "${LOCK_FILE}" \
  > logs/external_validation_offline.log

echo "[2/6] graceful replay (must)"
python3 external_validation.py \
  --offline-lock "${LOCK_FILE}" \
  --failure-policy none \
  --none-semantics must \
  > logs/external_validation_graceful_must.log

echo "[3/6] graceful replay (may)"
python3 external_validation.py \
  --offline-lock "${LOCK_FILE}" \
  --failure-policy none \
  --none-semantics may \
  > logs/external_validation_graceful_may.log

echo "[4/6] regex-drift replay suite"
# This mode intentionally fails in fail-fast because the drifted text does not
# match the primary regex pattern; keep the failure log for paper §6.4.
if python3 external_validation.py \
  --offline-lock "${DRIFT_LOCK_FILE}" \
  > logs/regex_drift_failure.log 2>&1; then
  echo "Warning: drift fail-fast replay unexpectedly succeeded" >&2
fi

python3 external_validation.py \
  --offline-lock "${DRIFT_LOCK_FILE}" \
  --failure-policy none \
  --none-semantics must \
  > logs/regex_drift_graceful_must.log

python3 external_validation.py \
  --offline-lock "${DRIFT_LOCK_FILE}" \
  --failure-policy none \
  --none-semantics may \
  > logs/regex_drift_graceful_may.log

echo "[5/6] classify_uand edge-case log"
python3 - <<'PY' > logs/check_consistent_edge_cases.log
from external_validation import LayerBounds, apply_none_policy, classify_uand

cases = [
    (
        "contradiction_min_gt_max",
        (
            LayerBounds(lower=2048, upper=65536, source="edge", note=""),
            LayerBounds(lower=512, upper=1024, source="edge", note=""),
            LayerBounds(lower=None, upper=65536, source="edge", note=""),
        ),
        False,
    ),
    (
        "boundary_equal",
        (
            LayerBounds(lower=63, upper=63, source="edge", note=""),
            LayerBounds(lower=63, upper=63, source="edge", note=""),
            LayerBounds(lower=63, upper=63, source="edge", note=""),
        ),
        False,
    ),
    (
        "zero_and_negative",
        (
            LayerBounds(lower=-1, upper=9, source="edge", note=""),
            LayerBounds(lower=-1, upper=9, source="edge", note=""),
            LayerBounds(lower=None, upper=9, source="edge", note=""),
        ),
        False,
    ),
    (
        "missing_bounds",
        (
            LayerBounds(lower=None, upper=None, source="edge", note=""),
            LayerBounds(lower=None, upper=None, source="edge", note=""),
            LayerBounds(lower=None, upper=None, source="edge", note=""),
        ),
        False,
    ),
]

for name, layers, undefined_from_parse in cases:
    judgement, lower, upper, _ = classify_uand(*layers, undefined_from_parse=undefined_from_parse)
    policy_judgement = apply_none_policy(judgement, "must")
    print(name, {"consistent": policy_judgement == "consistent", "lower": lower, "upper": upper})
PY

echo "[6/6] policy ablation benchmark"
python3 evaluate_policy_ablation.py \
  --offline-lock "${LOCK_FILE}" \
  --out-json logs/policy_ablation_report.json \
  --out-md logs/policy_ablation_report.md \
  > logs/policy_ablation_report.stdout.json

echo "Replay completed. Logs written to: ${SCRIPT_DIR}/logs"
