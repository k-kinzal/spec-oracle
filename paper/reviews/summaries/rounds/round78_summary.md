# Round 78 Summary (Formal Paper)

Target venues used in review prompts:
- FM / ITP / CPP / TACAS / FASE / Formal Aspects

Reviewer outcomes:
1. Reviewer1: **Strong Reject**
2. Reviewer2: **Major Revision (Conditional Accept potential)**
3. Reviewer3: **Reject (Conditional Major Revision)**

Converged strengths:
1. assumption-interface discipline (`hproj`, `hA`, `hcomm`) and counterexample-backed necessity are consistently rated strong.
2. reproducibility package (hash checks, replay script, Docker path) is considered solid.
3. must/may split under partial projections is viewed as technically coherent.

Converged blockers:
1. novelty bar for FM/ITP/CPP-level acceptance is still not met: reviewers request a theorem-level delta beyond classical set/order identities.
2. `UStar` section is repeatedly flagged as conditional/vacuous unless either instantiated non-trivially or demoted from core contribution.
3. case-study depth is seen as toy-level (especially PasswordPolicy); reviewers demand a genuinely nontrivial heterogeneous partial-projection instance.
4. related-work differentiation remains too positional; reviewers ask theorem-level comparison with closest mechanized lines (Mathlib/ITP/BX/Institution/CGC).
5. venue strategy must be tightened (single primary target, likely CPP/ITP methodology track) and manuscript structure adjusted accordingly.

Immediate next-revision focus:
1. add one explicit non-reducibility theorem or failed-baseline proof path (e.g., direct Mathlib reduction failure with proof artifact).
2. either provide one concrete `UStar` instantiation theorem chain or move `UStar` to template-only appendix status.
3. replace/augment toy case with one medium non-identity, heterogeneous projection case in main body.
4. strengthen §7 from definition-level positioning to theorem-level comparative claims with explicit references.
5. align sectioning/venue framing to a single target track and remove multi-venue ambiguity in core narrative.
