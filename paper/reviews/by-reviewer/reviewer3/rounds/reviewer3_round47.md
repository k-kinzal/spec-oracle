# Reviewer 3 Round 47

- Role: Reviewer 3 (Reproducibility / Artifact)
- Recommendation: Accept
- Pass Gate: true

## Summary
The manuscript provides exceptional reproducibility infrastructure with deterministic replay capabilities, source-lock verification, and comprehensive documentation. The artifact package (Lean proofs + extraction pipeline) demonstrates technical maturity rare in preliminary feasibility studies. Key strengths: (1) SHA256-locked snapshots with offline replay, (2) tri-valued judgment + policy projection separation, (3) explicit mutation expectation tracking, (4) clear Non-goals boundaries preventing overclaims. Minor presentation refinements would strengthen clarity but do not block acceptance.

## Strengths
- Deterministic replay claim is concrete and testable: §7.5 defines structural equality on 4 required fields (n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation), with SHA256 verification of script (7fb6541b...) and lock file (1b090656...)
- Source-lock infrastructure is production-grade: external_validation_sources.lock.json with URL/SHA256/UTC/snapshot_path, offline replay with hash mismatch detection (fetch_text ValueError on mismatch), three replay modes (fail-fast/graceful-must/graceful-may) with separate logs
- Mutation expectation tracking prevents ambiguous 'success': 6/6 pre-fixed expectations satisfied (stale_requirement_lower: raw_judgement=contradictory; unit_mismatch: upper'<=floor(baseline/1024)), not just binary pass/fail
- Non-goals §0.3 and scope boundaries are rigorous: explicit statements that n=3 is convenience sample (not statistical), interval-domain only (not general behavioral), extraction soundness proof is out-of-scope, PoC is feasibility demo (not production-ready)
- Lean artifact is self-contained: 59 theorems, 1502 LOC, no mathlib dependency (stdlib only), lake build with versioned toolchain (v4.27.0), manifest SHA256 documented
- Tri-state layer status (supported/invalid/unknown) + U0 observability (support_ratio/unknown_ratio) prevent binary oversimplification: §6.2 PoC observes avg_support_ratio=0.778, avg_unknown_ratio=0.222, making partial coverage explicit
- README.md provides minimal verification checklist with exact jq command: 'jq {n_real_projects, raw_judgement_distribution, policy_judgement_distribution, mutation_detected_by_expectation} logs/external_validation_graceful_may.log' → expected values n_real_projects==3, consistent==3, mutation_detected==6
- Negative case (regex drift) is included with actual implementation pattern: §6.4 shows 'inclusive' removal breaks 'between [0-9]+ and ([0-9]+) inclusive' pattern, with fail-fast/graceful-must/graceful-may logs demonstrating policy differences

## Required Fixes
- None

## Optional Fixes
- Add reproduce.sh to minimal verification checklist in §7.5 (currently only shows jq command for one log, but README.md indicates reproduce.sh runs all three modes)
- Clarify 'logs/*.log are JSON' note in README.md earlier (currently appears mid-section; could add to output schema section for immediate clarity)
- Consider adding a one-line 'expected runtime' note to README.md (even qualitative: 'offline replay ~seconds, online fetch ~minutes') to help artifact evaluators budget time
- In §6.2 mutation table, the 'criterion' column duplicates 'expected_outcome' in some rows; consider consolidating or clarifying the distinction
- The term 'preliminary feasibility demonstration' appears in README.md but could be consistently used in §6.2 introduction for alignment

## Evidence Quote
- "deterministic replay with source lock... deterministic comparison is based on JSON structural equality of required fields... sha256(external_validation.py)=7fb6541b43605e229aa68b73c921908969400e5adc3152b84381e37a9837d2d4 (§7.5)"
