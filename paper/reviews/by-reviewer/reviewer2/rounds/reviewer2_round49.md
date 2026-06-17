# Reviewer 2 Round 49

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This manuscript presents a mechanized formalization of UAD/f multi-layer specification consistency with careful scope discipline and reproducible PoC evidence. The work makes a solid contribution to requirements engineering tool foundations through: (1) Lean4-verified core theorems exposing necessary assumptions (projection composition, one-sided adequacy, non-adjointness under partiality), (2) explicit separation of U0 (join-based coverage) vs U∧ (meet-based consistency), and (3) a deterministically reproducible extraction pipeline demo with source-locked artifacts. The authors demonstrate exceptional discipline in delineating non-goals and not overclaiming from n=3 convenience samples. However, the manuscript would benefit from streamlining the dense formalism and more clearly signposting for SE/RE audiences where theoretical results end and practical implementation begins.

## Strengths
- Exceptional scope discipline with explicit Non-goals preventing overclaim (§0.3 clearly states no statistical generalization, no interval-domain generalization, no extractor soundness proof)
- Complete reproducibility package: Lean proofs build deterministically, PoC includes SHA256-locked sources with offline replay capability (§7.5)
- Honest treatment of PoC limitations: clearly separates RQ5 theory (adequacy for abstract E) from RQ6 practice (regex extraction demo), states 'this does NOT prove regex extractors satisfy adequacy'
- Well-defined observability metrics: U0 support/unknown/invalid tri-state decomposition with clear operational semantics, avoiding conflation of coverage with correctness
- Mechanized exposure of implicit assumptions: non-adjointness under partiality (§4.4), one-sided adequacy decomposition (§4.3), projection domain separation (§3.5) - these design decisions are Lean-verified not just claimed
- Pre-registered mutation expectations with checkable criteria (stale_requirement_lower expects contradictory, unit_mismatch expects upper'≤floor(baseline/1024)) - testable not post-hoc

## Required Fixes
- Add a 1-page visual roadmap early in §2-3 showing the reader WHERE each formalism component (Ω, proj, lifted, U0, U∧) lives in the architecture and HOW they connect to PoC implementation - current exposition is correct but dense
- Clarify in §4.3 abstract header: 'The following adequacy theorems apply to ABSTRACT extraction relation E. Applying these to concrete regex/LLM extractors requires SEPARATE soundness proofs (out of scope).' - this boundary is stated but buried
- Streamline §4.7 must/may discussion: current 3-page exposition mixes runtime policy, semantic foundations, and operational interpretation - recommend splitting into (a) semantic definition (1 page) and (b) operational policy guide (moved to §6 context)
- Add explicit limitation statement in §6.2 results: 'The 0.778 support_ratio and 0.222 unknown_ratio indicate partial observability in THIS PoC regex implementation, not a fundamental bound on UAD/f coverage' - prevent misreading metrics as inherent limits

## Optional Fixes
- Consider separating Lean formalization details (currently §4.1-4.7) into appendix with §4 summary focusing on WHAT was proven and WHY it matters for RE practitioners
- Add a 'Threats to Validity' subsection in §6 consolidating current scattered limitations (§6.3, §6.5, footnotes) using standard SE evaluation terminology
- Provide a comparison table: 'What typical RE traceability tools do' vs 'What UAD/f U0 provides' vs 'What this PoC demonstrates' - would ground the contribution for SE audiences
- The negative example (§6.4 regex drift) is valuable but feels isolated - consider framing as 'Failure Mode Analysis' with systematic enumeration of extraction brittleness patterns
- Add forward pointer in abstract/intro: 'Our PoC demonstrates TECHNICAL reproducibility (§6-7) but does NOT claim production readiness or cross-domain generalization' - set expectations early

## Evidence Quote
- "The PoC results are: n_real_projects=3, raw_judgement_distribution={consistent:3}, mutation_detected_by_expectation=6/6, avg_support_ratio=0.778, avg_unknown_ratio=0.222. This demonstrates deterministic replay with source-lock付き再実行 (§6.2), not external validity. The manuscript explicitly states: 'The gap between theoretical adequacy (§4.3) and practical regex extractors...本稿は regex 抽出そのものの soundness/completeness を証明していない'"
