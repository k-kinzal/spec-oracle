# Reviewer 2 Round 50

- Role: Reviewer 2 (Software Engineering / Requirements Engineering)
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
This paper presents a typed mechanization of the UAD/f model for multi-layer specification consistency governance, with solid theoretical grounding and impressive Lean4 formalization (59 theorems, 1502 LOC). The core contribution—establishing `U0` (join) vs `U∧` (meet) as distinct operations with explicit assumptions—is clearly valuable. However, the manuscript suffers from scope boundary confusion between theoretical mechanization (strong) and PoC empirical claims (overclaimed). The n=3 convenience sample is presented with appropriate statistical disclaimers but then interpreted beyond its demonstrable scope. Critical issues: (1) regex extraction is acknowledged as out-of-scope for soundness proof yet drives all empirical interpretation, (2) `U0` observability claims conflate theoretical membership with operational `support_ratio` metrics, (3) mutation "detection" validates implementation behavior rather than external validity. These are addressable through clearer scoping statements and reframing empirical results as "technical replay demonstration" rather than "validation."

## Strengths
- Exceptional formalization discipline: 59 mechanized theorems with explicit assumption tracking (hproj, hSound, hComplete) prevents invisible dependencies
- Clean separation of theoretical contributions (RQ1-5) from implementation demo (RQ6), with honest Non-goals declaration in §0.3
- Sophisticated handling of partial projections: proves non-adjoints (§4.4) and distinguishes must/may semantics (§4.7) rather than hiding partiality
- Deterministic replay infrastructure (source-lock + SHA256 + snapshots) provides genuine technical reproducibility for the n=3 PoC
- Transparent tri-state monitoring (supported/invalid/unknown) with policy projection makes observability boundaries explicit
- Proper positioning as 'preliminary feasibility demonstration' not statistical validation study (§6.2 header, §0.3 Non-goals)

## Required Fixes
- CRITICAL (overclaim): §6.2 claims 'U0 can be directly observed' via support_ratio but §2.6 states 'regex soundness/completeness is unproven.' Add explicit statement: 'U0_support equivalence to theoretical U0 holds only under the unverified assumption that regex extraction satisfies hSound+hComplete for the PoC instantiation.'
- CRITICAL (scope violation): §6.3 'What we showed' conflates replay success with extraction validity. Reframe as: 'The PoC demonstrates (i) deterministic replay mechanics, (ii) tri-state judgment stability, (iii) mutation expectation tracking—all contingent on regex extraction fidelity which remains unverified.'
- MAJOR (interpretability): Abstract/§0 must state upfront: 'The n=3 PoC validates pipeline mechanics (source-lock replay, judgment computation) but does NOT validate extraction correctness or generalizability beyond interval-domain numeric constraints.' Currently buried in §6.2 footnotes.
- MAJOR (claim precision): §4.8 table correctly marks adequacy theorems as 'abstract E only' but §6.2-6.3 repeatedly interprets PoC results as if adequacy applies. Add post-table reminder: 'Therefore PoC mutation results demonstrate judgment-function behavior, not RQ5 adequacy in practice.'
- MINOR (boundary marking): Insert subsection break before §6.3 titled '6.3 Interpretation Boundaries' that explicitly lists: (a) what the PoC proves (replay+judgment mechanics), (b) what it assumes (regex fidelity), (c) what it does not claim (statistical generalization, non-interval domains).

## Optional Fixes
- Clarify §2.7 'NL入口' positioning: Currently reads as 'NL is permitted' but PoC uses fixed regex patterns. Consider: 'The model permits NL input via extractor abstraction; current PoC uses pattern-based regex (no NL understanding) as concrete extractor instance.'
- §6.2 'unknown解釈' paragraph could strengthen by adding: 'The 2/3 code.lower=null primarily reflects regex implementation limits (one-sided extraction) rather than establishing that APIs lack lower bounds in general. Distinguishing extractor incompleteness from domain semantics requires extractor adequacy proof (out of scope).'
- Consider moving the excellent §6.5 threat-to-validity discussion immediately after §6.2 results rather than relegating to end-of-section. This would prevent readers from over-interpreting results before seeing limitations.
- §3.4 MUS definition is theoretically clean but empirically unused. Either (a) add brief note 'MUS computation demonstrated out-of-scope for n=3 PoC' or (b) if space permits, show trivial MUS={requirement,api} for stale_requirement_lower mutations as worked example.
- The §7.5 deterministic replay definition is exemplary but appears late. Consider promoting key points (4-item checklist, structural equality, sha256 locks) to §1.2 evaluation table for earlier reader orientation.

## Evidence Quote
- "§6.3: "解釈: 本節が示すのは「既存仕様の不具合発見率」ではなく、**実アーティファクト抽出からJSON出力・交差判定までを source-lock 付きで再実行できること**。ただし抽出器自体（regex層）の正当性保証は本稿の範囲外であり、抽出 soundness/completeness は仮定として扱う。したがって本節は `RQ6 (practice)` の実行可能性確認を対象とし、`RQ5 (theory)` の実抽出器適用（意味保存証明）は対象外である。""
- ""
- "This quote exemplifies both strength (honest scope declaration) and weakness (appears only in mid-section interpretation rather than upfront abstract/intro claim). The required fixes aim to elevate such discipline to structurally prominent positions."
