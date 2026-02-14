# Session 110: CLI Architecture Refactoring - Summary

## Goal
Resolve specORACLE's self-detected CLI architecture violation to complete self-governance.

## Problem
- **Violation**: main.rs (4475 lines) violates separation of concerns
- **Requirement**: Separate modules for parsing, use cases, presentation, persistence, AI
- **Self-governance test**: Can specORACLE detect AND fix its own violations?

## Progress Completed

### Phase 1: Presentation Layer ✅
- Created `presentation/formatter.rs` (94 lines)
- Extracted formatting functions
- Reduction: 4475 → 4444 lines (-31)

### Phase 2: Persistence Layer ✅
- Created `persistence/store_router.rs` (55 lines)
- Extracted store detection logic
- Reduction: 4444 → 4432 lines (-12)

### Phase 3a: Utilities ✅
- Created `utils.rs` (159 lines)
- Extracted parsing/conversion functions
- Reduction: 4432 → 4309 lines (-123)

### Total Progress
- **Original**: 4475 lines
- **Current**: 4309 lines
- **Reduction**: 166 lines (3.71%)
- **Target**: < 500 lines (90% reduction)
- **Remaining**: 3809 lines to extract

## Modules Created

```
spec-cli/src/
├── main.rs (4309 lines) ← still too large
├── presentation/
│   ├── mod.rs (3 lines)
│   └── formatter.rs (94 lines)
├── persistence/
│   ├── mod.rs (3 lines)
│   └── store_router.rs (55 lines)
└── utils.rs (159 lines)

Total extracted: 314 lines
```

## Next Steps Required

### Phase 3b: Command Implementations (Critical)
Extract command handler functions to separate modules:
- `commands/add.rs` - High-level Add command
- `commands/check.rs` - Check command (contradictions + omissions)
- `commands/trace.rs` - Trace command
- `commands/find.rs` - Find command
- `commands/extract.rs` - Extract command
- `commands/api/*.rs` - Low-level graph operations

**Estimated extraction**: ~2500 lines

### Phase 4: AI Integration
Extract AI-powered features:
- `ai/semantic.rs` - Semantic search
- `ai/inference.rs` - Relationship inference

**Estimated extraction**: ~500 lines

### Phase 5: Verify Self-Governance
- Re-extract architectural properties from new structure
- Run `spec check`
- Verify: 0 contradictions (CLI violation resolved)
- Update specifications

## Challenges

1. **Scale**: Need to extract 3809 lines (88%) more
2. **Complexity**: Command implementations are deeply intertwined
3. **Risk**: Large refactoring without planning mode
4. **Constraints**: Smallest possible commits

## Recommendation

The current incremental approach (3.71% in 3 phases) will require ~75 more phases at this rate. This is not sustainable.

### Two Options:

**Option A: Aggressive Extraction (Recommended)**
- Extract all commands in one phase (~2500 lines)
- Extract AI in another phase (~500 lines)
- Larger commits, higher risk, but faster progress

**Option B: Continue Incremental**
- Maintain current pace
- Many small commits
- Lower risk, but very slow

**Recommendation**: Switch to Option A (aggressive extraction) for commands. The modules are now well-established, and command extraction is a natural boundary.

## Current Status

✅ **Foundation established**:
- Module structure defined
- Presentation, persistence, utilities extracted
- All tests passing
- CLI functional

❌ **Self-governance not achieved**:
- CLI still violates separation of concerns
- main.rs still 4309 lines (8.6x target)
- Contradiction still detected

## Next Action

Begin Phase 3b: Extract command implementations aggressively to reach <500 lines target.
