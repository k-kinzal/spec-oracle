# Round 77 Summary (Formal Paper)

Target venues used in review prompts:
- FM / ITP / CPP / TACAS / FASE / Formal Aspects

Reviewer outcomes:
1. Reviewer1: **Major Revision**
2. Reviewer2: **Weak Accept / Minor Revision**
3. Reviewer3: **Major Revision**

Converged strengths:
1. assumption-audited theorem interfaces (`hproj`, `hA`, `hcomm`) are consistently rated strong.
2. mechanized counterexamples (`Transfer`, `Adequacy`, `Totalization`, vacuous-meet) are seen as substantive.
3. reproducibility package (hash checks, replay script, Docker recipe) is considered above average.

Converged blockers:
1. novelty framing remains under-argued for top-theory venues (FM/ITP/CPP/TACAS level); reviewers request a sharper scientific claim beyond "well-engineered library".
2. RQ1/RQ2 are still seen as partially self-referential unless operational evidence is made more explicit in main text.
3. `UStar` section is still viewed as potentially vacuous unless either instantiated non-trivially or further demoted to template-only status.
4. related-work differentiation needs tighter definition-level comparisons to closest mechanized partial-function / institution / GC lines.

Immediate next revision focus:
1. strengthen §6 with one formalized "failed baseline reduction" narrative tied directly to theorem statements.
2. compress/demote `UStar` claims further (template framing) unless adding concrete instantiation.
3. expand §1/§3 bridge paragraphs for RQ1/RQ2 with explicit theorem-signature evidence and failure interpretations.
4. tighten §7 comparisons with explicit structural incompatibility statements.
