# Reviewer 3 Round 53

- Role: Reproducibility Reviewer (#3)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The manuscript provides a detailed reproducibility framework with source-locking, SHA256 verification, and deterministic replay contracts. §7.5 establishes minimal check contracts and specifies 4-item verification criteria. The jq-based verification pipeline is well-defined with concrete expectations. However, several ambiguities remain regarding offline replay semantics, snapshot integrity verification, and failure-mode contracts that should be resolved for artifact-level auditability.

## Strengths
- **Strong SHA256-based deterministic replay contract**: §7.5 clearly specifies the 4-item minimal verification contract (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation) with concrete jq assertion commands
- **Comprehensive source-lock mechanism**: external_validation_sources.lock.json provides URL, SHA256, UTC timestamp, and snapshot path for full input provenance tracking
- **Executable verification script**: reproduce.sh provides 3-mode batch execution (offline fail-fast / graceful must / graceful may) with explicit log outputs suitable for jq-based automated checking
- **Clear artifact boundary declaration**: §0.3 and §6.2 explicitly limit PoC claims to 'deterministic replay' rather than statistical generalization or extractor soundness proof
- **Transparent failure-mode documentation**: §6.4 negative example (regex drift) demonstrates actual extractor brittleness with 3 concrete logs showing fail-fast vs graceful+must vs graceful+may policy differences
- **Minimal dependency contract**: Python standard library only (no pip requirements.txt), reducing reproducibility barriers

## Required Fixes
- **Specify offline replay SHA256 mismatch behavior precisely**: §7.5 states 'SHA256 不一致時は例外停止' but does not specify (i) exception type, (ii) whether partial results are preserved, (iii) which file in snapshots/* triggered mismatch. Add concrete error message example or reference implementation line numbers
- **Clarify snapshot/* SHA256 verification scope**: Does SHA256 check apply to (a) only source HTML/text, (b) also extracted bounds JSON, or (c) lock file itself? §7.5 mentions 'fetch_text オフライン分岐' but does not state whether snapshots are pre-extraction or post-extraction artifacts
- **Add deterministic replay failure-mode contract**: If reproduce.sh execution fails in one of the 3 modes, what is the minimal debugging output guaranteed? Current text only shows success-path jq queries but does not specify error-case observability (e.g., do mutation logs still get written if baseline extraction fails?)
- **Specify lake-manifest.json role in Lean reproducibility**: §7.2 lists manifest SHA256 but does not state whether 'lake build' verifies manifest integrity automatically or requires manual check. Add one sentence clarifying whether manifest mismatch is fail-stop or warning
- **Resolve 'date' exclusion ambiguity**: §7.5 states 'date は実行時刻依存で差分が出るため、決定的照合対象から除外' but does not specify whether 'date' field is (a) omitted from logs entirely, (b) present but ignored by jq checker, or (c) replaced with fixed placeholder. Specify which and show example jq filter if (b)

## Optional Fixes
- **Provide snapshot/* directory structure example**: A one-line tree output or file count would help reviewers understand what 'snapshots/*' contains before running reproduce.sh
- **Add reproduce.sh expected runtime estimate**: Helps reviewers budget artifact checking time (even if just 'completes in <5 minutes on typical laptop')
- **Clarify lock file versioning**: If external_validation_sources.lock.json changes between manuscript revisions, how should reviewers detect schema breaking changes? Consider adding a 'lock_version' field
- **Add graceful-mode stability note**: §6.4 shows graceful+must vs graceful+may can produce different policy_judgement for same raw input. Add one sentence in §7.5 noting which mode the 4-item minimal contract is fixed to (appears to be graceful+may but not explicit)
- **Suggest DOI-based long-term preservation recommendation**: §7.5 mentions 'ソース固定アーカイブ（例: DOI付きリポジトリアーカイブ）' but does not commit to one. For artifact badge eligibility, specify concrete archive plan (e.g., Zenodo deposit with DOI)
- **Add network-free verification smoke test**: Provide a one-liner that checks snapshots/* SHA256 locally before attempting offline replay (catches snapshot corruption early)

## Evidence Quote
- §7.5 期待出力の照合（最低限）provides concrete jq assertion:
```
jq -e '
  .n_real_projects == 3 and
  .raw_judgement_distribution.consistent == 3 and
  .raw_judgement_distribution.contradictory == 0 and
  .raw_judgement_distribution.inconclusive == 0 and
  .policy_judgement_distribution.consistent == 3 and
  .policy_judgement_distribution.contradictory == 0 and
  .policy_judgement_distribution.inconclusive == 0 and
  .mutation_detected_by_expectation == 6
' logs/external_validation_graceful_may.log
```
This establishes a **script-level minimal artifact check contract** that is auditable without human judgment.

However, §7.5 also states: 'オフライン追試で SHA256 不一致が発生した場合は、論文実行時と異なる入力であり再現性が保証されないことを意味するため、同梱 snapshot と lock の一致状態を復元して再実行する' — this creates ambiguity about what 'restore consistency' means operationally (manual file replacement? automatic fallback?).
