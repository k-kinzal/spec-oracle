# Round 58 Summary

- Date: 2026-02-17
- Method: claude -p subagent, 3 independent reviewer roles
- Target manuscript: paper/manuscript/uadf_u0_spec_proof.md

## Verdict Overview
- Reviewer 1: Accept (pass_gate=true)
- Reviewer 2: Accept (pass_gate=true)
- Reviewer 3: Minor Revision (pass_gate=false)
- Gate result: **2/3 pass gate**

## Residual Required Fixes
- [R3] reproduce.sh must include commands (or at minimum documentation) for replaying the drift scenario using logs/regex_drift_lock.json. The §6.4 re-generation commands are documented in the manuscript but absent from reproduce.sh, leaving the drift scenario unreachable from the single-entry-point script. Add the three drift commands from §6.4 as a fourth section in reproduce.sh, referencing logs/regex_drift_lock.json explicitly.
- [R3] reproduce.sh must verify logs/regex_drift_lock.json and logs/regex_drift_snapshot.txt via SHA256 before executing drift commands, consistent with the precheck pattern already applied to external_validation.py. Without this, the drift scenario's determinism guarantee is weaker than the main scenario's.

## Residual Optional Fixes
1. [R1] §6.2 mutation table row for 'zlib unit_mismatch_upper_scale_down_1024' shows mutated_intersection as [-1, 0] (lower=-1, upper=0) but the criterion states 'upper' ≤ floor(upper/1024)'. Since the baseline zlib upper is 9, floor(9/1024)=0, upper'=0 satisfies the criterion. However the lower=-1 originates from the baseline lower (-1), not from the mutation, which may confuse readers. A footnote clarifying that the lower boundary is unchanged by this mutation type would help.
2. [R1] §3.3 states 'consistent_iff_exists_UAndOn_pair' as a theorem name but the body defines Consistent(i,j) via a direct ∃x formula. For round-59 readability, it would be helpful to add a one-line note confirming that the Lean statement is definitional unfolding plus the non-emptiness witness, not an additional axiom.
3. [R1] §7.4 theorem count (59) and LOC (1502 for UadfU0, 1538 total) should be re-verified against the committed Lean tree if any files were added after the round-57 recount; the numbers are internally consistent but a re-run of the stated measurement commands before camera-ready would eliminate any stale-count risk.
4. [R2] §6.2 table note for bound_shrinkage: the zlib row shows mutated_intersection [-1, 0] satisfying upper' <= 0 as true, but -1 is the lower bound and 0 is the upper bound — a brief parenthetical clarifying which endpoint is being compared to floor(upper/1024) would prevent reader confusion (the text implies upper'=0 ≤ floor(9/1024)=0, which holds, but the notation is ambiguous at first read).
5. [R2] §3.4 MUS definition: the finiteness assumption (Fintype {i // active i}) is stated in prose but not reflected in the Lean file references listed; a brief note confirming whether this is axiom-free or uses a Fintype instance in Lean would help readers assessing the mechanisation.
6. [R2] §4.7 operational policy table: the column headers 'sound 側' and 'complete 側' refer to the extractor adequacy assumptions (hSound/hComplete), but a reader who has not fully absorbed §4.3 might conflate these with must/may semantics — a one-line disambiguating footnote would help.
7. [R2] The manuscript is unusually long for a research paper; the camera-ready version should consider moving §12 appendices and the detailed PoC ratio definitions to supplementary material or an extended version, leaving the main body at a more typical page count.
8. [R3] §7.2 lists a SHA256 for reproduce.sh itself (`ba57d30…`), but there is no mechanism for an independent reader to verify this hash — the script cannot verify itself. Consider adding a note in §7.2 instructing readers to verify reproduce.sh's hash externally before running it, or provide a companion checksum file.
9. [R3] The manifest SHA256 listed in §7.2 (`8c098d78…`) for lake-manifest.json is not verifiable from the provided files; consider including lake-manifest.json in the reproducibility package or at minimum noting it is only needed for the Lean build path.
10. [R3] In reproduce.sh, the offline fail-fast mode writes to logs/external_validation_offline.log but the paper only references logs/external_validation_graceful_may.log as the primary evidence log (§6.2). A brief comment in reproduce.sh clarifying which log corresponds to which §6.2 claim would reduce ambiguity.
11. [R3] The note field for SQLite code layer reads 'sqliteLimit.h max/default = 65536/4096' (hardcoded from code_default) but code.lower=null because code_default is unused in bounds construction. A comment in external_validation.py explaining why code_default is extracted but not used as a bound would clarify the one-sided unknown for independent readers.

## Recommendation
- Round 58 did not pass gate (**2/3**). Address residual required fixes before next round.
