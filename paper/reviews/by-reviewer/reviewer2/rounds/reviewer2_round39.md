# Reviewer 2 Round 39

- Role: Senior Software Engineering / Requirements Engineering Researcher (SE/RE Conference Track)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The UAD/f manuscript presents a theoretically sound reverse-mapping framework with empirical validation on real artifacts. The U0 indicator methodology (support_ratio, unknown_ratio) provides practical metrics for cross-layer consistency. The external validation demonstrates detectability (6/6 mutations caught) and non-triviality (3/3 real projects show measurable U0 support). However, three scoping issues require minor revision: (1) the claim scope vs. validation scope mismatch (interval-domain validation doesn't directly support general UAD/f claims), (2) ambiguous interpretation of "unknown" layer status in practical decision-making, and (3) insufficient discussion of scalability beyond simple numeric intervals.

## Strengths
- Strong empirical grounding: 3 real OSS projects (PostgreSQL, zlib, SQLite) with offline snapshot-based validation eliminate network brittleness and ensure reproducibility
- Non-trivial U0 indicators: avg_support_ratio=0.78, avg_unknown_ratio=0.22 shows the framework detects meaningful cross-layer patterns beyond toy examples
- Mutation testing validates fault detection: 6/6 injected defects (stale requirements, unit mismatches) correctly trigger contradictory judgments, demonstrating practical utility
- Methodological rigor: automatic regex extraction with source_lock (SHA256 hashes) and explicit failure_policy='none' with may-semantics provides transparent, reproducible evidence
- Theoretically grounded: U0 as reverse-mapped root specification with f₀ᵢ⁻¹ transformations provides clear semantic foundation for multi-layer governance

## Required Fixes
- Scope alignment: Clarify that current empirical validation targets interval-domain specifications (numeric ranges) and does not claim to validate the full UAD/f model's applicability to non-interval domains (e.g., protocol state machines, temporal properties). Add explicit scope boundary in Section 4 or 5.
- Interpret 'unknown' layer status: The current JSON shows code layers with 'unknown' status (lower=null) in 2/3 projects. Manuscript must explain whether this represents (a) missing artifact data, (b) under-specified implementation, or (c) valid MAY-semantics where U0 permits discretion. This directly impacts practical decision-making.
- Address scalability limitations: With only 3 projects and simple numeric intervals, discuss whether the automatic extraction approach scales to: (a) richer specification types (e.g., state machines, contracts), (b) larger artifact sets (hundreds of requirements), (c) cross-layer dependencies beyond pairwise interval intersection.

## Optional Fixes
- Enhance mutation coverage explanation: While 6/6 mutations were detected, only 2 mutation types were tested (stale_requirement_lower, unit_mismatch_upper). Discuss what other mutation types (e.g., semantic drift, cross-layer timing inconsistencies) would strengthen external validity.
- Quantify 'reverse-mapping' overhead: The paper claims specORACLE constructs U0 through reverse mappings, but doesn't report effort metrics. Even rough estimates (e.g., regex pattern authoring time, manual validation effort for 3 projects) would ground practical adoption claims.
- Clarify 'failure_policy=none' vs. quality gates: The JSON uses 'none' policy with may-semantics, which is appropriate for exploratory validation. However, for production adoption, discuss what policy thresholds (e.g., min support_ratio, max unknown_ratio) would constitute acceptable U0 quality.
