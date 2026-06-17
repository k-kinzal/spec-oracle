# Reviewer 3 Round 40

- Role: Artifact/Reproducibility Reviewer (Round 40 Gate)
- Recommendation: Accept
- Pass Gate: true

## Summary
The artifact demonstrates strong reproducibility guarantees through offline snapshot replay with locked sources (SHA256 hashes, UTC timestamps), automated regex extraction patterns with match evidence, and clear "none" policy semantics (may-membership for unknown intervals). All 3 real projects achieve consistency (100%), mutation testing validates detection (6/6), and the automation trail is complete from URL → snapshot → pattern → extracted value. The artifact meets acceptance criteria for deterministic replay and transparency.

## Strengths
- Deterministic replay infrastructure: SHA256-locked snapshots with UTC timestamps enable bit-exact reproduction without network dependency (network_required: false)
- Complete automation evidence trail: extraction_patterns section documents regex→match mapping for all 9 fields across 3 projects, enabling verification that no manual editing occurred
- Clear 'none' policy semantics: failure_policy='none' with none_semantics='may' correctly implements unknown intervals as may-membership (lifted_membership shows must=false, may=true for code layers with null bounds)
- Mutation testing validates detection capability: 6/6 mutations detected with expected outcomes (3 contradictory injections caught, 3 scale-down changes detected)
- Strong consistency results: 3/3 real projects consistent, avg_support_ratio=0.78, no parse issues, demonstrating practical U0 reverse-mapping feasibility

## Required Fixes
- None

## Optional Fixes
- Consider adding extraction_patterns.*.match_line_number or match_byte_offset to enable precise verification against snapshots (currently match text is sufficient but byte offset would be gold standard)
- Document the regex pattern development process (were patterns written before seeing snapshots? from independent spec reading?) to strengthen claim of 'no manual editing after extraction'
- Add a reproduce.sh --verify-checksums mode that re-hashes all snapshots and compares to source_lock to catch any inadvertent snapshot modification
