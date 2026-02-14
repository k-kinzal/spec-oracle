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
- [x] **Current**: main.rs reduced from 3736 to 3131 lines (-605 lines, -16.2%)
- [ ] Extract U0 operations (ConstructU0, CleanupLowQuality)
- [ ] Extract Layer operations (VerifyLayers, FilterByLayer, DetectLayerInconsistencies)
- [ ] Extract remaining commands
- [ ] Each command handler: input validation → use case → presentation

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

## Success Criteria

- main.rs < 500 lines
- All command handlers in commands/ module
- Business logic in use_cases/ module
- AI logic in ai/ module
- `spec check` shows 0 contradictions
- **Self-governance achieved**: specORACLE satisfies its own architecture requirements
