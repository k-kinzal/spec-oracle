# Reviewer 1 Round 46

- Role: Reviewer 1 (Formal Methods / Mechanization correctness)
- Recommendation: Accept
- Pass Gate: true

## Summary
This manuscript presents a mechanized formalization of the UAD/f model's reverse-mapping kernel with exceptional clarity regarding its theoretical boundaries and practical claims. The authors have successfully addressed prior concerns about deterministic replay scope, PoC project naming, invalid/contradictory distinction, and RQ5/non-goals alignment. The work demonstrates strong formal rigor through 59 mechanized theorems in Lean4, explicit assumption tracking (particularly the decomposition of adequacy into sound/complete one-sided inclusions), and reproducible evaluation with source-locked artifact extraction. Most importantly, the manuscript maintains scrupulous honesty about what is and isn't proven, making it a model of responsible mechanization research.

## Strengths
- Exceptional boundary discipline: §0.3 Non-goals, §4.8 theorem application boundaries, and §6.2 PoC interpretation explicitly separate what is mechanically verified from what is demonstrated
- Sound theoretical core: 59 Lean4 theorems mechanizing RQ1-RQ5 with explicit assumption tracking (hproj, hA, hSound, hComplete), demonstrating that the UAD/f kernel can be made rigorous
- Honest adequacy treatment (§4.3): Correctly presents adequacy theorems as abstract results requiring separate proof for concrete extractors, not as validation of the regex implementation
- Clear operational/theoretical distinction: §6.2 explicitly labels U∧ judgement as 'operational analogue' rather than claiming direct mechanization of theoretical UAndOn
- Reproducibility infrastructure: Source-locked snapshots, SHA256 verification, offline replay mode, and 3-mode reproduce.sh enable deterministic verification of claimed results
- Well-calibrated PoC claims: §6.2 focuses on deterministic replay (RQ6) rather than overreaching to statistical generalization or extractor soundness
- Explicit assumption dependencies: §3.5 IdealRoot theorems labeled as 'assumption-dependent' rather than main contributions, §4.1 transfer requires hproj (same-point linkage)
- Tri-valued judgement design: Separating consistent/contradictory/inconclusive with policy projection (must/may) provides principled handling of extraction uncertainty

## Required Fixes
- None

## Optional Fixes
- Consider adding forward reference in §2.6 'artifact→IR extraction' discussion to §4.3 adequacy theorems, noting that while the decomposition is mechanized, concrete extractor instantiation remains future work
- §6.2 mutation table: Add footnote clarifying that 'invalid' (ill-formed interval l>u) vs 'contradictory' (intersection failure) are distinct concepts tracked separately in the output schema
- §7.6 correspondence table: Consider adding column indicating which theorems require additional instantiation proof vs. which are directly applicable
- The README.md mentions 'preliminary feasibility demonstration' which could be more prominently referenced in the main manuscript §6 introduction for alignment

## Evidence Quote
- "§4.3: "**重要（適用境界）**: 本節の adequacy 定理は抽象関係 `E` に対する一般定理である。具体抽出器（regex/LLM）へ適用するには、当該抽出器について `hSound` / `hComplete` が成り立つことを**別途証明**する必要がある。" "
- ""
- "This explicit statement of application boundaries exemplifies the manuscript's principled approach to distinguishing mechanized theory from empirical demonstration."
