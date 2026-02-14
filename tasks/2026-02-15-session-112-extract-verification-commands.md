# Session 112: Extract Verification Commands

## Date
2026-02-15

## Goal
Extract verification commands from main.rs to commands/verification.rs module

## Motivation
- main.rs is 4180 lines (violates SoC specification [b706e529])
- specORACLE detects this as a self-governance issue
- Incremental extraction: focus on verification commands batch

## Commands to Extract

**Verification commands**:
1. `DetectContradictions` - formal verification of spec consistency
2. `DetectOmissions` - isolated spec detection
3. `VerifyLayers` - layer integrity check
4. `ProveConsistency` - SMT-based consistency proof
5. `ProveSatisfiability` - SMT-based satisfiability proof
6. `InspectModel` - model inspection

## Approach

1. Create `spec-cli/src/commands/verification.rs`
2. Extract standalone implementations from `run_standalone()`
3. Extract server implementations from `main() match`
4. Update `commands/mod.rs` to export functions
5. Update both match statements to call extracted functions
6. Test: `cargo build && spec check`

## Expected Impact

- Removes ~300-400 lines from main.rs
- Groups related verification functionality
- Maintains both standalone and server mode support
- Zero behavioral changes

## Success Criteria

- [ ] cargo build succeeds
- [ ] spec check reports same results
- [ ] main.rs reduced by 300+ lines
- [ ] Verification commands work in both modes
- [ ] Commit with smallest unit of change

## Status
**In Progress**

## Notes
This is Phase 1 of CLI refactoring. Subsequent sessions will extract:
- Phase 2: Query/search commands (Query, Find, Trace, ResolveTerm)
- Phase 3: Extraction commands (Extract, ConstructU0, InferRelationships)
- Phase 4: Utility commands (Summary, Init, Watch, CleanupLowQuality)
- Phase 5: Deprecated API commands
