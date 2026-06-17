# Reviewer 3 Round 58

- Role: Reproducibility Reviewer
- Recommendation: Minor Revision
- Pass Gate: false

## Summary
The offline replay pipeline is well-designed and substantially reproducible. The main lock file (`external_validation_sources.lock.json`), the script, and the `reproduce.sh` precheck mechanism are internally consistent. Actual log output matches the paper's stated numerical claims (6/6 mutations detected, 3/3 consistent, avg_support_ratio=0.778, etc.). However, two blockers prevent a fully independent reader from completing a clean deterministic replay: (1) `reproduce.sh` only precheks `external_validation.py` via SHA256, but the drift-scenario commands use a *different* lock file (`logs/regex_drift_lock.json`) that is not listed in `reproduce.sh` at all — meaning the drift scenario is not replayable via `reproduce.sh`; and (2) the SHA256 hardcoded in `reproduce.sh` for `external_validation.py` (`970c0fcc…`) is documented in §7.2 as the authoritative hash, but the script itself does not verify `reproduce.sh`'s own hash, so an independent reader has no way to confirm the script they received has not been modified. These two issues are self-contained and fixable without altering results.

## Strengths
- All 9 snapshot files are locked via SHA256 + UTC timestamp in external_validation_sources.lock.json, providing content-addressable offline inputs for the main replay.
- The graceful-may log output matches every numerical claim in §6.2 exactly: n_real_projects=3, raw_judgement_distribution={consistent:3}, mutation_detected_by_expectation=6, avg_support_ratio≈0.778, avg_unknown_ratio≈0.222.
- The drift scenario is self-contained: regex_drift_lock.json, regex_drift_snapshot.txt, regex_drift_failure.log, regex_drift_graceful_must.log, regex_drift_graceful_may.log are all present and internally consistent. The failure log shows the exact ValueError at the expected line.
- reproduce.sh includes a Python SHA256 precheck for external_validation.py before execution, preventing silent script substitution for the main three modes.
- The script uses only Python stdlib; no pip dependencies means environment setup friction is minimal.
- Claim in §6.4 that graceful+must yields policy_judgement=contradictory and graceful+may yields policy_judgement=consistent for the SQLite drift case is verified by the two drift logs.
- Three replay modes (fail-fast, graceful-must, graceful-may) are independently logged and all three are invocable from reproduce.sh.

## Required Fixes
- reproduce.sh must include commands (or at minimum documentation) for replaying the drift scenario using logs/regex_drift_lock.json. The §6.4 re-generation commands are documented in the manuscript but absent from reproduce.sh, leaving the drift scenario unreachable from the single-entry-point script. Add the three drift commands from §6.4 as a fourth section in reproduce.sh, referencing logs/regex_drift_lock.json explicitly.
- reproduce.sh must verify logs/regex_drift_lock.json and logs/regex_drift_snapshot.txt via SHA256 before executing drift commands, consistent with the precheck pattern already applied to external_validation.py. Without this, the drift scenario's determinism guarantee is weaker than the main scenario's.

## Optional Fixes
- §7.2 lists a SHA256 for reproduce.sh itself (`ba57d30…`), but there is no mechanism for an independent reader to verify this hash — the script cannot verify itself. Consider adding a note in §7.2 instructing readers to verify reproduce.sh's hash externally before running it, or provide a companion checksum file.
- The manifest SHA256 listed in §7.2 (`8c098d78…`) for lake-manifest.json is not verifiable from the provided files; consider including lake-manifest.json in the reproducibility package or at minimum noting it is only needed for the Lean build path.
- In reproduce.sh, the offline fail-fast mode writes to logs/external_validation_offline.log but the paper only references logs/external_validation_graceful_may.log as the primary evidence log (§6.2). A brief comment in reproduce.sh clarifying which log corresponds to which §6.2 claim would reduce ambiguity.
- The note field for SQLite code layer reads 'sqliteLimit.h max/default = 65536/4096' (hardcoded from code_default) but code.lower=null because code_default is unused in bounds construction. A comment in external_validation.py explaining why code_default is extracted but not used as a bound would clarify the one-sided unknown for independent readers.

## Evidence Quote
- "再生成コマンド（current schema）:\n```bash\ncd paper/case-study/real_projects\npython external_validation.py --offline-lock logs/regex_drift_lock.json > logs/regex_drift_failure.log 2>&1 || true\npython external_validation.py --offline-lock logs/regex_drift_lock.json --failure-policy none --none-semantics must > logs/regex_drift_graceful_must.log\npython external_validation.py --offline-lock logs/regex_drift_lock.json --failure-policy none --none-semantics may > logs/regex_drift_graceful_may.log\n```"
