# Continue Goal Session - Critical Issues Analysis

**Date**: 2026-02-14
**Session**: Goal Continuation
**Focus**: Addressing remaining issues to fully achieve "new era" specification tool

## Context

User requested: "please continue for goal"

From CLAUDE.md:
> **Goal**: Create an open-source specification description tool for a new era

From goal-continuation-verified.md:
> **Goal Status**: Substantially YES, with qualifications
> - ✅ Works at scale (536+ specs)
> - ✅ Reduces effort (75% omission reduction)
> - ✅ AI adds value (cross-layer matching)
> - ⚠️ Not 100% accurate (needs human review)
> - ⚠️ Some edge cases missed (password specs)

## Session Progress

### Issue 1: Password Spec Connection Failure ✅ DIAGNOSED

**Problem**: Multiple password-related specs remain isolated despite obvious semantic equivalence.

**Root Cause Identified**: Confidence threshold (0.7) too high for REFINES edges

**Key Finding**:
```
Case: 34bf0b12 <-> 5fdeafb2
- Keyword similarity: 0.7778
- Edge kind: REFINES (same kind, sim > 0.6)
- Confidence: 0.7778 × 0.75 = 0.5833
- Threshold: 0.7
- Result: 0.5833 < 0.7 → edge NOT created ❌
```

**Why This Happens**:
- Different edge types have different confidence multipliers:
  - Synonym: × 0.95
  - Formalizes: × 0.9
  - DerivesFrom: × 0.85
  - **Refines: × 0.75** (lowest)
- With min-confidence 0.7:
  - Refines edges need similarity > 0.93 (unrealistic)
  - Many valid relationships filtered out

**Solution Options**:
1. **Option A**: Lower min-confidence to 0.5
   - Pros: Simple, no code changes
   - Cons: May increase false positives

2. **Option B**: Increase REFINES multiplier from 0.75 to 0.9
   - Pros: Better balance, fixes systematic issue
   - Cons: Requires code change

3. **Option C**: Review 200 suggestions manually
   - Pros: High precision
   - Cons: Time-consuming

**Recommended**: Option B (adjust multiplier)
- Changes password spec confidence: 0.7778 × 0.9 = 0.7000 (meets threshold!)
- Aligns REFINES with other edge types
- Addresses systematic problem, not just password specs

**Documentation**: `tasks/2026-02-14-password-spec-root-cause.md`

### Issue 2: Project Separation ✅ DESIGNED

**Problem**: No project/namespace concept - all specs mixed in one global graph

**Impact**:
- Cannot separate spec-oracle's own specs from demo examples
- No way to manage multiple projects
- Real-world usage blocked

**Design Completed**: Option A (Separate Graph Files)

**Structure**:
```
~/.spec-oracle/
├── config.json          # Current project, settings
└── projects/
    ├── spec-oracle/     # Tool's own specifications
    ├── demo-examples/   # Demo specs
    └── my-webapp/       # User projects
```

**Key Features**:
- True isolation per project
- Project switching: `spec project switch <name>`
- Scoped operations: `spec extract --project myapp`
- Backward compatible (default project)

**Implementation Phases**:
1. Create projects/ structure and config
2. Update server with project context
3. Add CLI project commands
4. Migrate existing data
5. Extract into separate projects

**Documentation**: `tasks/2026-02-14-project-separation-design.md`

## Current System State

**Specifications**: 536 nodes
**Edges**: 1212 relationships
**Omissions**: 168 (down from 674, 75% reduction)
**Tests**: 55 passing
**AI Cache**: Active

**Issues Remaining**:
1. Password specs isolated (confidence threshold)
2. No project separation (architecture gap)

## Next Steps

### Immediate: Fix Confidence Threshold

**File**: `spec-core/src/extract.rs:414`

**Change**:
```rust
// Before
if source.kind == target.kind {
    return Some((
        crate::EdgeKind::Refines,
        similarity * 0.75,  // Too low
        ...
    ));
}

// After
if source.kind == target.kind {
    return Some((
        crate::EdgeKind::Refines,
        similarity * 0.9,   // Aligned with other edge types
        ...
    ));
}
```

**Validation**:
1. Run tests: `cargo test`
2. Re-run AI inference: `spec infer-relationships-ai --min-confidence 0.7`
3. Verify password specs connected
4. Check omission count (expect further reduction)
5. Measure false positive rate

### Short-term: Implement Project Separation

**Estimated effort**: 4-6 hours
**Priority**: High

**Implementation checklist**:
- [ ] Create config file structure
- [ ] Update FileStore for project paths
- [ ] Add project management to specd
- [ ] Add project commands to CLI
- [ ] Update gRPC proto
- [ ] Migrate existing data
- [ ] Extract spec-oracle into own project
- [ ] Extract demo examples into separate project
- [ ] Update documentation
- [ ] Test all functionality

## Constraints (from CLAUDE.md)

✅ **Behavior guaranteed through tests** - Will verify with `cargo test`
✅ **Minimal changes** - Confidence fix is 1-line change
✅ **No clarification questions** - Design decisions made autonomously
✅ **No planning mode** - Direct action, documented in tasks/
⚠️ **Use specification tools** - Will verify changes with spec-oracle itself

## Goal Progress

**Before this session**:
- Goal substantially achieved
- 2 critical issues identified

**After this session**:
- ✅ Issue 1 root cause diagnosed
- ✅ Issue 2 design completed
- ⏭️ Ready for implementation

**When both issues resolved**:
- ✅ Password specs connected (demonstrates accuracy)
- ✅ Projects separated (enables real-world use)
- ✅ Goal fully achieved

## Success Metrics

**After confidence fix**:
- Expect: Password specs have 3-4 new edges
- Expect: Omissions reduced to ~120-150 (80% reduction)
- Expect: False positive rate < 10% (measured via spot checks)

**After project separation**:
- Can manage multiple projects independently
- spec-oracle manages its own specs cleanly
- Demo examples isolated from production specs

## Session Artifacts

**Created**:
1. `tasks/2026-02-14-password-spec-root-cause.md` - Detailed root cause analysis
2. `tasks/2026-02-14-project-separation-design.md` - Complete design document
3. `tasks/2026-02-14-continue-goal-session.md` - This summary

**Diagnostic tools** (temporary, removed):
- `test_password_sim.rs` - Similarity calculation test
- `diagnose_password.rs` - Comprehensive password spec analysis
- `test_edge_priority.rs` - Edge creation rule verification

## Conclusion

Both critical issues blocking full goal achievement have been **analyzed and designed**.

**Issue 1** (password specs): Simple fix, ready to implement
**Issue 2** (project separation): Architecture designed, ready to implement

The "new era" specification tool is **nearly complete** - just needs these final refinements.

---

**Ready to proceed with implementation.**
