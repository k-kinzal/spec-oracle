# Reviewer 3 Round 52

- Role: Reproducibility/Artifact Reviewer (#3)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The manuscript demonstrates strong reproducibility engineering with (i) source-locked offline replay (§7.5), (ii) deterministic fields explicitly defined (4-item minimal contract), (iii) SHA256-verified snapshots, and (iv) executable reproduction script. The deterministic replay specification is internally consistent and auditable. However, minor gaps exist: (1) the "TRUNCATED" status suggests §7.5 definition may be incomplete in the provided excerpt, (2) the jq-based verification specification needs explicit handling of distribution key ordering/stability, (3) build reproducibility for Lean proofs lacks Docker/Nix-level isolation specification, and (4) mutation expectation criteria need formalization as assertions rather than prose. These are addressable without major restructuring.

## Strengths
- Deterministic replay scope is explicitly bounded to 4 fields (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation) with clear pass/fail criteria in §7.5
- Source-lock mechanism (external_validation_sources.lock.json) includes URL, SHA256, UTC timestamp, and snapshot path—comprehensive provenance tracking
- Offline verification path is executable: reproduce.sh bundles 3 modes (fail-fast, graceful-must, graceful-may) with snapshot-based input isolation
- SHA256 verification is implemented in fetch_text with explicit mismatch-halts-execution semantics, preventing silent corruption
- Non-deterministic fields (e.g., execution date) are explicitly documented as excluded from pass criteria, avoiding false-negative divergence
- Lean mechanization reproducibility includes toolchain lock (lean-toolchain), manifest (lake-manifest.json with SHA256), and zero external dependencies (mathlib-free)
- Mutation expectation tracking (6/6 detected) provides operational observability beyond baseline consistency checks
- Graceful/must/may policy variation is systematically logged (3 separate .log files) enabling policy-sensitivity audit

## Required Fixes
- Complete §7.5 deterministic replay definition (manuscript appears truncated—verify full specification of jq-based structural equivalence including distribution key ordering/unknown key tolerance)
- Formalize mutation expectation criteria as executable assertions: provide jq predicates or Python assert statements for 'expectation_satisfied' checks (currently prose-only in table)
- Specify Lean build reproducibility isolation: add Dockerfile/Nix derivation or explicit OS/version constraints (currently 'Darwin 23.5.0' is documented but not containerized)
- Clarify distribution key stability guarantee: does {consistent:3, contradictory:0, inconclusive:0, <unknown_key>:X} pass or fail? Add explicit jq filter showing required-key extraction vs. full-object equality

## Optional Fixes
- Add checksums for reproduce.sh and snapshots/* to source-lock (currently only external_validation.py and sources.lock.json have SHA256)
- Provide machine-readable schema for external_validation_results.json (e.g., JSON Schema) to enable automated validation beyond manual jq inspection
- Include timing bounds for offline replay (e.g., 'completes in <5min on reference hardware') to detect performance regressions masquerading as correctness
- Add reproduce.sh exit-code contract: should it exit 0 on pass and nonzero on mismatch? Currently silent on failure semantics
- Document whether snapshots/* can be regenerated from lock.json alone (i.e., is lock.json sufficient or are snapshots/* canonical?)
- Specify fallback behavior for URL expiry: Wayback is mentioned but not scripted—consider adding --wayback-fallback flag to external_validation.py

## Evidence Quote
- §7.5: "deterministic replay の定義（本稿）: 固定入力: external_validation_sources.lock.json + snapshots/* + external_validation.py（同一版） / 決定性対象（論文照合仕様）: n_real_projects / raw_judgement_distribution / policy_judgement_distribution / mutation_detected_by_expectation / 同一性判定レベル: JSON の構造同値（上記必須フィールドの値一致）で判定し、キー順・表示順は一致要件に含めない（§7.5 の jq チェックを準拠仕様とする）" — This establishes clear deterministic scope BUT the jq specification reference appears circular (§7.5 defines jq as canonical but jq filter for key-order-insensitive structural match is not shown). Required fix: show the actual jq filter or Python structural-diff predicate.
