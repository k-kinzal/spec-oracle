# Reviewer 1 Round 52

- Role: Formal Methods Reviewer #1
- Recommendation: Minor Revision
- Pass Gate: true

## Summary
The manuscript has made substantial progress in mechanization rigor since earlier rounds. The boundary separation between abstract adequacy theorems (§4.3) and PoC implementation (§6.2) is now technically sound. The source-lock deterministic replay infrastructure (§7.5) is well-defined. However, minor technical gaps remain: (1) §4.3's proof obligations for concrete extractors need explicit template examples, (2) §6.2's `proj_i^{U0}` vs `measure_i^{U∧}` duality requires formal justification or explicit non-compliance acknowledgment, (3) §7.5's deterministic replay success criteria should include extractor SHA256 in the minimal checking procedure. These are addressable without re-mechanization.

## Strengths
- §4.3 adequacy theorems correctly mechanized as abstract theorems over E : Ω → β_i → Prop, with explicit warning that concrete extractor application requires separate proof obligations (lines addressing R2 concern)
- §6.2 PoC boundary clearly stated: '본절은 RQ6 (practice)(source-lock付き決定的再実行可能性)を対象とする' with explicit Non-goals list preventing overclaiming
- §7.5 deterministic replay protocol is reproducible: source-lock JSON + snapshots + SHA256 verification + jq-based 4-field checking specification is complete and technically sound
- §6.2's dual observation setup (proj_i^{U0} := interval_i vs measure_i^{U∧} := bounds_i) is now explicitly labeled as 'operational analogue' rather than claimed as full UAndOn implementation
- Must/may semantics (§4.7) correctly formalized with inclusion relationships and operational policy mapping table (Table: 優先目標→推奨設定)
- Threat-to-validity section (§6.5) comprehensively lists sample bias, extractor limitations, mutation coverage gaps, and lack of human validation
- Lean mechanization is mathlib-independent with explicit logic foundation declaration (funext + propext, no Classical axioms)
- Definition 2.6 (obs/extract/proj decomposition) with Lean example (ArtifactBundleExample.lean) provides concrete instantiation template

## Required Fixes
- §4.3: Add minimal proof obligation template for concrete extractors. Currently states '具体抽出器へ適用するには...別途証明する必要がある' but provides no worked example. Add subsection §4.3.1 with pseudocode showing how to discharge hSound/hComplete for a toy regex case (e.g., 'must be at most N' → upper bound extraction). This need not be Lean-mechanized but should show the proof structure expected.
- §6.2: The dual projection setup (proj_i^{U0} uses interval, measure_i^{U∧} uses bounds) creates semantic gap with §2 Model where single proj_i is assumed. Either: (a) formalize this as two separate Model instances (Model_U0 and Model_U∧) with explicit relationship theorem, OR (b) add explicit disclaimer that PoC does not implement the single-projection Model but uses operational approximation. Current text hints at (b) but stops short of explicit non-compliance acknowledgment.
- §7.5: The deterministic replay check specifies 4 fields but omits extractor version. Add 'sha256(external_validation.py)==7fb6541b...' to the minimal jq checking command in §7.5's '期待出力の照合' block, since extractor changes invalidate deterministic claim. Currently buried in prose but should be in the executable check.

## Optional Fixes
- §6.2: The 'interval vs bounds' distinction is operationally justified but theoretically under-explained. Consider adding brief remark why U0 needs closed intervals (for lifted membership) while U∧ can work with partial bounds (for intersection feasibility check)—this would connect implementation choice to theoretical role.
- §4.8: Table's '未検証' entries are honest but could add one concrete example of what 'verify hproj for layer pair (req, api)' would look like in practice (e.g., show the statement form even if proof is future work).
- §6.3: 'support_ratio=0.778' interpretation is correctly cautious but could add one sentence explaining why code layer has lower support (2/3 unknown): is it regex limitation or inherent code structure? Current text mentions 'regex抽出器が片側境界しか回収できない実装上の限界' which is good but could tie to Table support_frequency more explicitly.
- §7.4: LOC breakdown is useful but consider adding one metric on 'theorem dependency depth' or 'longest proof chain' to give sense of mechanization complexity beyond raw counts.
- §2.7: NL → IR pipeline description is clear but could benefit from one worked example showing evidence_span preservation through the pipeline (e.g., how 'at most 63 bytes' at req-12:line3-18 becomes IR.bound.upper=63 with span pointer intact).

## Evidence Quote
- §4.3: '重要(適用境界): 本節のadequacy定理は抽象関係Eに対する一般定理である。具体抽出器(regex/LLM)へ適用するには、当該抽出器についてhSound / hCompleteが成り立つことを**別途証明**する必要がある。' || §6.2: 'PoCのU∧は、同一Ω上でlifted(i)のmeetを直接計算したものではなく、抽出制約(bounds)上の同時満足可能性を返す**operational analogue**として実装している。' || §7.5: 'deterministic replayの定義(本稿): 固定入力: external_validation_sources.lock.json + snapshots/* + external_validation.py(同一版) ... 決定性対象(論文照合仕様): n_real_projects / raw_judgement_distribution / policy_judgement_distribution / mutation_detected_by_expectation'
