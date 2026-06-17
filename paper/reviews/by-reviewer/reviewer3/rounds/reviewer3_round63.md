# Reviewer 3 Round 63

- Role: Reproducibility Reviewer (Round 63)
- Recommendation: PASS — no concrete mismatches found between documented replay procedure and script/lock behavior. All hash references, lock mappings, and entrypoint coverage are consistent across the provided artifacts.
- Pass Gate: true

## Summary
Reviewed the manuscript (§6.2, §6.4, §7.2, §7.5), reproduce.sh, external_validation.py, external_validation_sources.lock.json, and logs/regex_drift_lock.json for concrete mismatches. All four SHA256 values checked in reproduce.sh's precheck block are consistent with the values stated in the manuscript (§7.2). The lock file structure matches what load_offline_records() expects. The drift lock correctly substitutes the pragma.html snapshot with regex_drift_snapshot.txt (SHA256=0d2d319f9edd4dbf2c80351bf1bcbfd3264552999ca557ad9598ac833ea4480c), which is the drifted snapshot used for §6.4. All five replay steps in reproduce.sh map to documented log file names in the manuscript. The entrypoint coverage (steps 1–5) matches the manuscript's documented modes (offline fail-fast, graceful must, graceful may, drift suite, edge-case log). No hash mismatch, lock mapping gap, or missing entrypoint was found.

## Strengths
- SHA256 precheck in reproduce.sh covers all four critical artifacts (external_validation.py, external_validation_sources.lock.json, regex_drift_lock.json, regex_drift_snapshot.txt) with values matching §7.2 manuscript claims.
- Drift lock correctly reuses all 8 non-SQLite pragma entries from the canonical lock unchanged, and overrides only the pragma.html entry with the drifted snapshot SHA256 and path — exactly matching §6.4's description.
- reproduce.sh's 5-step structure covers all documented replay modes: offline fail-fast (step 1), graceful must/may (steps 2–3), drift suite fail-fast/must/may (step 4), and edge-case log (step 5).
- external_validation.py correctly guards against clobbering the canonical lock during offline replay (the `if args.offline_lock is None` guard before lock write), preserving determinism.
- classify_uand and apply_none_policy function signatures match the edge-case test invocation in step 5 of reproduce.sh.
- The drift snapshot (logs/regex_drift_snapshot.txt) contains the drifted SQLite pragma page content without the 'inclusive' keyword pattern needed by the primary regex, correctly triggering fail-fast failure as described in §6.4.

## Required Fixes
- (none)

## Optional Fixes
- The manuscript §7.2 states reproduce.sh SHA256 as '3a60d05c5f4281812dbc53cc448e201f60a3403ba6475577dc4f2ee36e8fd562' (63 hex chars) — this appears to be a truncated SHA256 (should be 64 hex chars). Consider verifying whether a leading zero was dropped in typesetting.
- Step 4 in reproduce.sh uses `|| true` to suppress non-zero exit for the expected drift fail-fast failure, but does not verify that the failure was specifically due to regex_no_match (vs. other errors). A comment or assertion on the expected error type would strengthen auditability.

## Evidence Quote
- "python3 - <<'PY'\nimport hashlib\nimport pathlib\nimport sys\n\nexpected = {\n    \"external_validation.py\": \"ea820e0d86324d2c7583e963cd5e0a9e49c2f2f827e8e0a8d2f560bea8b649d7\",\n    \"external_validation_sources.lock.json\": \"0c34d22165d3f032d3929f8333657fa25fa65aa55542749d83dba031f11a4793\",\n    \"logs/regex_drift_lock.json\": \"1f31c8e65688f680abc9b4781ea41aca7f4ebe142f1838f74b7698d5e2517330\",\n    \"logs/regex_drift_snapshot.txt\": \"0d2d319f9edd4dbf2c80351bf1bcbfd3264552999ca557ad9598ac833ea4480c\",\n}"
