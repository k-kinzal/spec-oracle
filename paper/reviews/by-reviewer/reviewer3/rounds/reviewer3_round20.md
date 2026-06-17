I'll provide a comprehensive review of this manuscript from the perspective of Reviewer #3, focusing on RE practical applicability and evaluation design.

---

VERDICT: NG

MAJOR:
1. **Pain/Goal mismatch (§0.1-0.2)**: The manuscript opens with "多層防御における仕様統制の困難性" but positions `U0` as a *coverage baseline* (over-approximation), not a *control mechanism*. The fundamental tension is unresolved: if `U0` is deliberately weaker than individual layers (§3.1), how does it "統制" them? The paper needs to either (a) reframe the goal as "layer-crossing comparison baseline construction" or (b) demonstrate how `U0` enables actual control operations (automated conflict resolution, change propagation enforcement, etc.). Currently it reads as "we build a join operator" with vague claims that this somehow solves governance problems.

2. **Evaluation does not match scope claims (§6.2)**: The paper explicitly disclaims general applicability ("母集団推定を目的としない", "convenience sample", "技術的実行可能性デモ"), yet §0.1 frames the problem as a pervasive industrial challenge. The n=3 PoC with hand-picked numeric boundary constraints is insufficient to support even *preliminary* evidence that real-world contradictions exist at detectable rates or that regex extraction works beyond toy cases. The paper needs to either (a) run the tooling on 30-50 OSS projects with documented specification inconsistencies to show detection rates, or (b) remove all industrial motivation claims and position this purely as a formal framework with one demo.

3. **RQ5/RQ6 boundary confusion (§4.3, §6.2)**: RQ5 (theory) proves abstract adequacy for an uninterpreted relation `E`, while RQ6 (practice) uses regex extractors whose soundness/completeness is explicitly unproven. The paper states "regex 抽出層は本稿で証明対象ではなく" but then claims to "demonstrate" extraction pipeline feasibility. This is circular: you cannot claim to demonstrate *anything* about extraction if you haven't verified the extractor. Either (a) prove soundness/completeness for the regex patterns used in §6.2 (even if only for the specific 3 projects), or (b) rename RQ6 to "extraction *scaffolding* feasibility" and remove all claims about actual contradiction detection.

MINOR:
1. **Must/may運用判断が曖昧 (§4.7)**: The paper presents must/may as a binary choice but doesn't provide decision criteria. In what scenarios should an RE practitioner choose must over may? The "偽陽性抑制 vs 偽陰性抑制" table is abstract—needs concrete examples like "use must when validating safety-critical constraints, use may during exploratory prototyping."

2. **Motivation example needs layer labels (§0.1)**: The HTTP/API/App example lacks explicit mapping to the formal model. Which layer is `β_req`? Which is `β_code`? Adding subscripts would help readers connect intuition to formalism.

3. **Theorem 3.5 presentation (§3.5)**: The "理想化強仮定版" theorems (`UStar_subset_UAndOn`, etc.) are listed without explaining when they're applicable vs. when the domain-restricted versions are needed. Needs a decision tree or table showing which variant to use under what observability assumptions.

4. **No tooling artifact (§7)**: The paper provides Lean proofs and Python scripts but no integrated CLI tool. A practitioner reading this cannot run `specoracle check myproject/` and get a report. Even a prototype wrapper would strengthen the "practical feasibility" claim.

5. **Extraction failure率の定量化欠如 (§6.4)**: The negative example shows regex drift causes failure, but doesn't quantify how often this happens in practice. What percentage of real documentation updates break extraction? Without this, the graceful degradation modes feel like defensive programming with no empirical basis.

6. **MUS/unsat core未実装 (§3.4)**: The paper defines MUS but punts implementation to "今後課題." For industrial use, automated conflict localization is essential—without it, practitioners get binary yes/no answers with no actionable next steps. Should at least sketch an algorithm (e.g., SAT solver adaptation) to show feasibility.

REQUIRED_CHANGES:
1. **Reframe §0.1-0.2 motivation**: Either (a) replace "統制" claims with "layer-crossing comparison baseline" framing, explicitly acknowledging that `U0` does *not* enforce consistency, or (b) add a new subsection showing how `U0` enables concrete control operations (e.g., automated test generation for coverage gaps, CI/CD gates that reject PRs violating `U∧`).

2. **Expand §6.2 evaluation OR remove industrial claims**: Either (a) evaluate 30-50 OSS projects, report contradiction detection rate distribution, and characterize failure modes, or (b) remove all language about "現代のソフトウェア開発" challenges and reposition as "a formal framework with one illustrative demo."

3. **Prove or remove RQ6**: Either (a) add soundness/completeness proofs for the 3 specific regex patterns used in §6.2 (can be Lean lemmas over string patterns), or (b) rename RQ6 to "extraction scaffolding" and remove all claims about detecting real contradictions.

4. **Add must/may decision criteria table (§4.7)**: Create a 2×2 table with rows={偽陽性 risk high/low} and columns={偽陰性 risk high/low}, showing which semantics to use in each quadrant with RE scenario examples.

RISK:
The core risk is **overclaim relative to evidence**. The paper builds a solid formal foundation (Lean mechanization is rigorous) but then extrapolates to broad industrial applicability without sufficient empirical support. The n=3 PoC with unverified extractors cannot justify statements like "多層防御の統制困難性" being a pervasive problem that this framework solves. Either the evaluation needs major expansion (50+ projects, human validation, extractor correctness proofs) or the framing needs to retreat to "we formalize a join/meet kernel for multi-layer specs and show it's mechanically sound." As written, RE practitioners will read §0-1, expect a validated industrial tool, and be disappointed by §6's narrow scope. Academic reviewers will see the gap between formal rigor (strong) and empirical rigor (weak) and question the contribution's significance.
