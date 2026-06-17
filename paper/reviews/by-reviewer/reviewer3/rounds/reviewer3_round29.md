VERDICT: OK

## Minor Suggestions

1. **§6.2 mutation detection phrasing**: The manuscript states "mutation_detected_by_expectation = 6/6" but the table shows one detection via `basis: intersection_changed` (zlib unit_mismatch). Consider explicitly noting that "detection" encompasses both contradictory policy and output-change criteria, already clarified in §6.3 but worth reinforcing in §6.2's summary line.

2. **§7.5 SHA256 verification flow**: The text describes SHA256 mismatch as "論文実行時と異なる入力" but could add one sentence clarifying the recovery action: "restore the bundled snapshot/lock pair and re-run" (already implied by step 6, but worth stating explicitly for non-expert readers).

3. **§4.3 RQ5 boundary note positioning**: The disclaimer "実抽出器への適用には抽出層の意味保存証明が別途必要" appears mid-theorem-list. Consider moving it to the subsection header or a dedicated "Scope Note" paragraph to avoid interrupting the theorem enumeration flow.

4. **Appendix B mutation table alignment**: The inline Python shows `detection_basis` as a list, but the explanatory table in §6.2 uses "`basis: ...`" as a single label. Reconcile the presentation (either show the list explicitly or note "detection_basis contains [...] when multiple criteria apply").

5. **§9 limitation #13 trace instantiation**: "実行時トレース `Ω=Trace` への直接拡張は未検証" is clear, but adding a forward reference to the `ArtifactBundleExample.lean` mechanization would help readers see the concrete `Ω_art` example already exists (currently only mentioned in §6.1.1).

---

**Summary**: Text, script, and JSON are mutually consistent. The 3-project convenience-sample design, mutation detection criteria, and must/may policy distinctions are correctly documented without overclaim. The boundary between RQ5 (theory) and RQ6 (practice) is clearly maintained, and all negative-case logs (regex drift) are properly referenced.
