Verdict: Minor Revision

## What is now convincing

• **Methodological rigor in scope definition**: The manuscript now clearly frames its contribution as "暗黙仮定の可視化" rather than theorem count, which appropriately positions this as a mechanization paper rather than a purely theoretical advancement.

• **Honest threat articulation**: §9 explicitly acknowledges the convenience sample limitation, regex extraction soundness gap, and absence of one-sided adequacy实証—this transparency strengthens credibility.

• **Reproducibility infrastructure**: The addition of `external_validation_sources.lock.json` with URL/SHA256/UTC timestamps provides genuine artifact reproducibility, meeting mechanization standards.

• **Operator disambiguation**: The join (`U0`) vs meet (`U∧`) separation with explicit role assignment (情報集約 vs 同時満足) resolves the semantic conflation that plagued earlier drafts.

• **Non-triviality demonstration**: The four "discoveries" (§5) successfully argue that Lean formalization revealed substantive hidden assumptions—particularly the same-point connection assumption (`hproj`) in transfer theorems.

• **Appropriate claims calibration**: §6.3 correctly frames the 3-project study as "再現可能パイプライン実証" rather than statistical prevalence estimation, avoiding overreach.

## Remaining blocking issues

• **Evaluation-theory gap persists**: While §6.2 states "理論との対応（最小接続）", the actual connection remains superficial. The regex-extracted intervals are claimed to "具体化" the `A(i)` sets, but there is no formal correspondence proof between the extraction pipeline and the `preimage`/`UAndOn` constructs. This gap undermines the "接続可能性デモ" claim in the title.

• **Mutation testing mischaracterization**: §6.3 describes mutation as "手続きテスト" for "矛盾検出ロジック", but the actual mutations (`lower > upper`) are trivial contradictions that any interval checker would catch. This does not validate the theoretical machinery—it merely confirms basic arithmetic works. The claim "変異試験で矛盾検出感度を確認" overstates what is actually demonstrated.

• **Missing soundness analysis for extraction**: §9.4 acknowledges the regex extraction soundness gap, but §4.3's one-sided adequacy theorems are presented without connecting to this limitation. If the extraction is not proven sound, then the "connection" to real artifacts is not formally grounded in the theorems.

• **Insufficient justification for n=3**: While §6.2 now admits "convenience sample", there is no discussion of why these three projects are sufficient to demonstrate "接続可能性". Are there structural differences between projects that would test different aspects of the theory? The selection rationale remains vague.

• **Weak institutional positioning**: §8 states the relationship to Institution theory as "本稿は root 演算の具体的機械化に焦点を限定" but does not explain *why* this narrower focus is valuable when Institution already provides a general framework. What specific problems does UAD/f solve that Institution does not?

## Required final edits before submission

1. **Add explicit soundness assumption statement**: In §6.2, before the results table, insert: "We assume without proof that the regex extraction is sound (no false positives in boundary identification). Validating this assumption is future work." This makes the dependency explicit.

2. **Replace mutation testing section**: Revise §6.2 bullet 5 and §6.3's mutation discussion to: "We performed basic sanity checks by introducing contradictory constraints (`lower > upper`). These were detected as expected, confirming the implementation functions correctly on trivial cases. This does not validate the theoretical machinery against realistic inconsistencies."

3. **Clarify extraction-theory gap**: Add to §6.2 after "理論との対応（最小接続）": "This correspondence is informal. Formally connecting regex extraction to `preimage` definitions would require proving extraction soundness/completeness (§4.3's one-sided adequacy), which we leave for future work. The current demonstration shows mechanical feasibility, not formal adequacy."

4. **Strengthen n=3 justification**: In §6.2 selection criteria, add: "These three projects represent diverse constraint types: identifier length (linguistic), compression level (algorithmic parameter), and page size (storage allocation). We selected them to demonstrate extraction feasibility across different constraint domains, not to sample a representative distribution."

5. **Revise RQ6 answer**: In conclusion (§10), change the RQ6 answer from "実アーティファクト抽出をソースロック付きで再実行可能にし、理論入力へ接続するPoC基盤を示した" to "実アーティファクト抽出の再現可能性を確立したが、抽出から理論入力への接続は informal である。形式的adequacy証明は今後の課題。"

6. **Add Institution comparison**: In §8, after the Institution bullet, add: "UAD/f differs from Institution in three ways: (1) explicit partial projections via `Option`, (2) root-space join/meet operators, (3) Lean mechanization focusing on computation rather than categorical abstraction. We trade generality for executability and mechanized verification."

7. **Fix theorem count claim**: §7.4 lists "theorem declarations: 43" but does not distinguish between core theoretical results and auxiliary lemmas. Add a breakdown: "Of these, X are core contributions (§4), Y are adequacy/composition results (§4.2-4.3), Z are background lemmas (§4.6)." This prevents conflation of novelty with volume.
