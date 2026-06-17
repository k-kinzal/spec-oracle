VERDICT: OK

## Minor Suggestions

1. **Theorem boundary table ambiguity (§4.8)**
   - Line 632: "未検証（PoCは抽出再実行デモ）" for `lifted_transfer` could clarify that the *abstract assumptions* are mechanized in Lean, but *concrete instantiation for real extractors* is deferred. Current phrasing might suggest the theorem itself is unverified.

2. **RQ6 scope precision (§6.2 header)**
   - Line 925-926: "本節は `RQ6 (practice)` を対象とする" - consider adding explicit boundary: "RQ6 addresses deterministic replay of extraction pipeline; extractor semantic correctness (RQ5 adequacy instantiation) is out of scope."

3. **Mutation expectation basis (§6.2 results table)**
   - Line 1047-1052 mutation table: `detected_expectation` column shows all `true`, but "basis" differs (e.g., `intersection_changed` vs full policy change). Adding a footnote explaining "expectation met via *any* listed basis" would prevent misreading as strict conjunction.

4. **Related Work positioning (§8)**
   - Line 1476-1480: Institution/BX paragraphs could benefit from one sentence explicitly stating: "Our contribution is not theoretical novelty in these areas, but practical mechanization of UDA/f-specific root join/meet with `Option`-partiality in a self-contained Lean artifact."

5. **Appendix B function signature documentation (§12.2)**
   - Line 1850-1862: `classify_uand` and `apply_none_policy` code blocks lack docstrings. Adding 1-2 line docstrings (e.g., "Three-valued judgement from layer bounds intersection") would improve standalone readability.

---

**Summary**: No blocking issues for journal readiness. All five suggestions are editorial/clarification improvements that enhance precision but do not invalidate existing claims or mechanized proofs.
