# Session 114: Fix CLI Architecture Violation

**Date**: 2026-02-15

## Problem

specORACLE detected its own violation (self-governance working!):
- Spec [d26341fb]: CLI architecture violates separation of concerns (3736 lines in main.rs)
- Spec [b706e529]: CLI must separate concerns into separate modules

**Current state**:
- main.rs: 3736 lines
- Some commands extracted: trace, check, add, find, contradictions, omissions, query
- But run_standalone() function (~1300 lines) contains most command handlers

## Goal

Refactor CLI to satisfy specification [b706e529]:
- ✓ Command parsing - already separate (clap in main.rs)
- ✗ Use case implementation - needs extraction
- ✓ Presentation formatting - already separate (presentation/formatter.rs)
- ✓ Persistence routing - already separate (persistence/store_router.rs)
- ✗ AI integration - needs extraction

## Approach

1. **Extract remaining command handlers** to commands/ module
2. **Create use_cases/ module** for business logic shared across commands
3. **Create ai/ module** for AI integration (handle_ai_query, etc.)
4. **Reduce main.rs** to <500 lines (just CLI definition + dispatch)

## Implementation Progress

### Phase 1: Extract Remaining Commands
- [x] Extract API commands to commands/api.rs (9 commands)
- [x] Extract Summary command to commands/summary.rs
- [x] Extract Extract command to commands/extract.rs
- [x] Extract Prover commands to commands/prover.rs (ProveConsistency, ProveSatisfiability, InspectModel)
- [x] Extract U0 operations to commands/u0.rs (ConstructU0, CleanupLowQuality)
- [x] **Current**: main.rs reduced from 3736 to 2865 lines (-871 lines, -23.3%)
- [x] **Commit**: 0b49195 "Extract Prover and U0 commands"
- [ ] Extract Layer operations (VerifyLayers, FilterByLayer, DetectLayerInconsistencies)
- [ ] Extract relationship commands (InferRelationships, InferRelationshipsAi)
- [ ] Extract remaining server-mode handlers
- [ ] Goal: Reduce main.rs to <500 lines

### Phase 2: Create Use Cases Module
- [ ] Identify shared business logic across commands
- [ ] Create use_cases/ module
- [ ] Extract: semantic similarity, relationship inference, conflict detection, etc.

### Phase 3: Create AI Module
- [ ] Extract handle_ai_query and AI-related functions
- [ ] Create ai/ module
- [ ] Centralize AI integration logic

### Phase 4: Verify Self-Consistency
- [ ] Rebuild and test
- [ ] Run `spec check`
- [ ] Verify contradiction [d26341fb] is resolved
- [ ] Achieve self-consistency: specORACLE satisfies its own specifications

## Progress Summary

### Extracted So Far
- **commands/api.rs** (5448 bytes): 9 low-level graph API operations
- **commands/summary.rs** (2732 bytes): Summary command
- **commands/extract.rs** (4604 bytes): Extract command
- **commands/prover.rs** (390 lines): ProveConsistency, ProveSatisfiability, InspectModel
- **commands/u0.rs** (292 lines): ConstructU0, CleanupLowQuality
- **commands/add.rs, check.rs, contradictions.rs, find.rs, omissions.rs, query.rs, trace.rs** (already extracted)

### Metrics
- **Before**: 3736 lines (main.rs)
- **After**: 2865 lines (main.rs)
- **Reduction**: -871 lines (-23.3%)
- **Remaining**: ~2365 lines to remove to reach <500 line target

### Remaining Work

**Large blocks still in main.rs:**
- run_standalone() function: ~460 lines (mostly thin dispatch, but some inline handlers remain)
- Server mode handlers in main(): likely contains duplicate logic
- Utility functions: is_semantically_related, handle_ai_query, extract_and_sync, etc.
- Remaining commands with inline implementations:
  - Layer operations: VerifyLayers, FilterByLayer, DetectLayerInconsistencies
  - Relationship operations: InferRelationships, InferRelationshipsAi
  - Watch command
  - Various smaller commands

**Next Steps:**
1. Extract layer operations to commands/layer.rs
2. Extract relationship operations to commands/relationships.rs
3. Extract utility functions to utils/ or helpers/ module
4. Remove duplicate server-mode handlers (consolidate with standalone)
5. Thin down run_standalone to pure dispatch

## Success Criteria

- main.rs < 500 lines
- All command handlers in commands/ module
- Business logic in use_cases/ module (if needed)
- AI logic in ai/ module (if needed)
- `spec check` shows 0 contradictions
- **Self-governance achieved**: specORACLE satisfies its own architecture requirements
