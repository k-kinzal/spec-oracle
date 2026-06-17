# Reviewer 1 Round 53

- Role: Formal Methods Reviewer #1
- Recommendation: Accept
- Pass Gate: true

## Summary
The manuscript has successfully addressed all major formal verification concerns raised in previous rounds. The critical improvements are: (1) §4.3 now clearly separates abstract adequacy theorems from concrete extractor obligations with explicit proof-obligation templates, (2) §6.2 provides formal non-equivalence notes distinguishing operational analogues from theoretical definitions, and (3) §7.5 establishes deterministic replay criteria with SHA256 verification and jq assertions. The work demonstrates mechanical verification of the UAD/f core, explicit assumption tracking, and reproducible artifact evaluation. Minor optional improvements remain but do not block acceptance.

## Strengths
- §4.3 adequacy decomposition now explicitly states 'RQ5 is abstract theory; concrete extractor application requires separate proof' with clear 4-step proof obligation template
- §6.2 formal distinction between proj_i^U0 (interval extraction) and measure_i^U∧ (bounds observation) eliminates operational/theoretical conflation
- §7.5 deterministic replay specification uses SHA256 + jq assertions on 4 fixed metrics, enabling mechanical verification of reproducibility claims
- Non-goals §0.3 properly scopes claims (no statistical generalization, no interval-domain extrapolation, no extractor soundness proof, no production readiness)
- Lean mechanization (59 theorems, 1502 LOC) provides reference implementation with assumption tracking via explicit hypotheses
- Must/may semantics §4.7 formally separates inconclusive projection policy from membership semantics
- Mutation testing §6.2 uses pre-fixed expectations (contradictory for stale_lower, upper'≤floor(upper/1024) for unit_mismatch) enabling deterministic validation

## Required Fixes
- None

## Optional Fixes
- §4.3: Consider adding forward reference to §12.1 where concrete 4-step template is demonstrated (currently only mentioned in passing)
- §6.2 Table '理論要素とPoC要素の対応': The operational analogue caveat could benefit from explicit Lean snippet showing classify_uand ≠ UAndOn membership
- §7.5: The jq assertion script could explicitly check mutation_detected_by_expectation == '6 / 6' string equality (currently uses numeric ==6 which works but loses the denominator information present in the JSON)
- §6.2: The 'formal non-equivalence note' after the PoC layer mapping could be extracted into a numbered remark for easier citation in reviews/rebuttals
- §2.7 NL→IR evidence_span schema: Consider adding a concrete example showing how 'identifier length must be at most 63 bytes' maps to the full IR structure with span_id

## Evidence Quote
- §4.3: "**重要（適用境界）**: 本節のadequacy定理は抽象関係`E`に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について`hSound`/`hComplete`が成り立つことを**別途証明**する必要がある。" | §6.2: "形式注記: 本稿は`∀x, classify_uand(ŵidehat{bounds}(x)) ↔ x∈UAndOn`の同値主張を行わない。PoCは`U0`側と`U∧`側で異なる観測関数を併置する運用構成である。" | §7.5: "jq -e '.n_real_projects == 3 and .raw_judgement_distribution.consistent == 3 and ... .mutation_detected_by_expectation == 6'"
