VERDICT: OK

MAJOR: none

MINOR:
1. §3.5 should clarify that the domain-restricted assumption `U* ∩ Dom_i ⊆ lifted(i)` is not weakening but rather making explicit the partial-projection boundary. Consider adding: "This is not a relaxation; rather, it acknowledges that `U*` cannot mandate behavior where observation is undefined."
2. §4.3 could benefit from a forward reference to §6.2's disclaimer that the regex extractor's soundness/completeness is not proven in this paper. Consider: "The theorems in this section apply to any abstract relation `E`; applying them to the regex extractor in §6.2 requires a separate adequacy proof (out of scope)."
3. §6.2's "重要（RQ5/RQ6境界）" box is excellent but appears mid-section. Consider moving it to the beginning of §6.2 as a "Scope Note" to prevent misreading the PoC as a full adequacy validation.

REQUIRED_CHANGES: none

RISK:
The paper successfully separates U0 (coverage baseline) from U* (ideal root) and makes all partial-projection assumptions explicit. The §3.5 domain-restriction formulation is correct but could be misread as a "weakening workaround" rather than a necessary boundary condition. The RQ5/RQ6 boundary is now clearly demarcated, preventing conflation of theoretical adequacy (§4.3) with practical extraction demonstration (§6.2). No major mathematical or structural defects remain; the minor points are presentational refinements to forestall reviewer misinterpretation.
