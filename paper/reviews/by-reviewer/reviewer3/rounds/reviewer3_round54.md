# Reviewer 3 Round 54

- Role: Reproducibility Reviewer (#3) — Replay Protocol & Copy-Paste Robustness
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The §7.5 restructuring substantially improves reproducibility. The minimal Python-only path is now clearly delineated, SHA256 anchors cover all critical artifacts, the three-mode reproduce.sh intent is unambiguous, and the deterministic contract (offline + lock + SHA mismatch = exception stop) is stated with enough precision for a third party to follow. Residual risks are moderate and fixable at revision stage: one SHA256 value in §7.2 is listed for external_validation_sources.lock.json but the file path for snapshots/* is not SHA-anchored; the reproduce.sh script itself lacks a copy-pasteable invocation block; and the truncated end of the manuscript leaves the jq block incomplete, preventing copy-paste verification of that optional path. No fatal reproducibility blocker was found under the Python-only minimal path.

## Strengths
- Python-only minimal path is fully self-contained: bash reproduce.sh + two inline Python heredocs cover the critical assertions (n_real_projects, raw/policy judgement distribution, mutation_detected_by_expectation) using only stdlib — no pip, no jq, no external tooling required.
- SHA256 anchors provided for all three critical artifacts: external_validation.py (7fb6541b...), reproduce.sh (388ef94c...), and external_validation_sources.lock.json (1b090656...). These enable independent integrity verification before any execution.
- Offline replay path is deterministically defined: --offline-lock flag triggers SHA256 check per snapshot via fetch_text, and mismatch causes exception stop — the failure mode is explicit and loud rather than silent.
- Three-mode intent of reproduce.sh is clearly documented (fail-fast / graceful-must / graceful-may) with named log files per mode, allowing reviewers to distinguish policy effects from extraction effects.
- Deterministic contract is stated precisely: 'same lock/snapshot input → deterministic re-execution' with explicit carve-out that document-update robustness is NOT claimed. This scopes the reproducibility claim correctly.
- must/may policy judgement pipeline is mapped to concrete function names (classify_uand / apply_none_policy) and to appendix §12.1, allowing code-level tracing.
- lake-manifest SHA256 is provided for the Lean mechanization, giving independent integrity check for the formal layer separate from the Python layer.
- Negative example (§6.4 regex drift) is an honest, implementation-derived failure case with named comparison logs, not a constructed strawman.

## Required Fixes
- The jq block at the end of §7.5 is TRUNCATED in the submitted manuscript (the file ends mid-block). The complete jq one-liner for optional verification must be restored. A reviewer attempting copy-paste of the optional jq path will encounter a syntax error. Even if jq is optional, the truncation signals a manuscript assembly error that must be repaired before final submission.
- snapshots/* are listed as required reproducibility artifacts but carry no SHA256 anchor in §7.2 or §7.5. The lock file records per-source SHA256, but the snapshot directory as a whole has no manifest hash. Add either (a) a SHA256 of a tar/zip of the snapshots directory, or (b) an explicit statement that snapshot integrity is fully covered by the per-entry SHA256 in external_validation_sources.lock.json and that the offline path's fetch_text verification is the sole integrity gate. Currently the relationship is implicit.
- reproduce.sh itself is not shown inline. Its SHA256 is given (388ef94c...) but the actual invocation sequence is not copy-pasteable from the manuscript — a reviewer must locate the file in the repo. Add a minimal inline block (5–10 lines) showing the exact commands reproduce.sh executes, so the manuscript is self-contained for the replay path.

## Optional Fixes
- The Python SHA check heredoc uses assert without a descriptive message. Change to assert h == '7fb6541b...', f'Got {h}' so a reviewer sees the actual vs expected hash on failure rather than a bare AssertionError.
- §7.2 lists 'external_validation.py SHA256（2026-02-15 実行版）' with a date qualifier. If the file changes between submission and artifact freeze, this anchor becomes stale. Consider replacing the date qualifier with a commit SHA or artifact DOI reference to make the anchor version-stable.
- The 'Lean LOC' measurement command references rg (ripgrep) which may not be universally installed. Add a fallback using grep -r for the wc -l computation, or note that rg is required only for the measurement step and not for build/verification.
- The three-mode log naming (external_validation_offline.log / graceful_must / graceful_may) in §7.5 uses .log extension for JSON content. The note that 'jq で直接検証できる' is correct but the extension mismatch may surprise reviewers. A one-line note that the files are valid JSON despite the .log extension would prevent confusion.
- In the Python JSON verification heredoc, the variable name p shadows pathlib.Path — this is harmless but could confuse reviewers reading the inline snippet. Use log_path or result_path for clarity.

## Evidence Quote
- "期待出力の照合（最低限, Python-only）:
```bash
cd paper/case-study/real_projects
bash reproduce.sh
# SHAチェック（macOS/Linux 共通, 追加依存なし）:
python - <<'PY'
import hashlib, pathlib
p = pathlib.Path(\"external_validation.py\")
h = hashlib.sha256(p.read_bytes()).hexdigest()
print(h)
assert h == \"7fb6541b43605e229aa68b73c921908969400e5adc3152b84381e37a9837d2d4\"
PY
```
[...]
任意の追加確認（jq を使う場合）:
```bash
jq '{n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation}' logs/external_validation_graceful_may.log
jq -e '
  .n_real_projects == 3 and
  .raw_judgement_distribution.consistent == 3 and
--- END FILE: paper/manuscript/uadf_u0_spec_proof.md (TRUNCATED)"
