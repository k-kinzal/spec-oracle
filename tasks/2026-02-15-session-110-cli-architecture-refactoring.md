# Session 110: CLI Architecture Refactoring

**Date**: 2026-02-15
**Goal**: Resolve the self-detected CLI architecture violation to complete specORACLE's self-governance essence

## Problem

specORACLE detected its own violation (Session 109):
- **U0 Requirement** [b706e529]: CLI must separate concerns (parsing, use cases, presentation, persistence, AI)
- **U3 Reality** [d26341fb]: main.rs is 4475 lines, all concerns mixed in one file
- **Contradiction**: System detects but hasn't fixed its own violation

## Current State

```
spec-cli/src/
└── main.rs (4475 lines, 191,919 bytes)
```

All concerns mixed:
- Command parsing (clap)
- Use case implementation (30+ commands)
- Presentation formatting (output messages)
- Persistence routing (standalone vs server)
- AI integration (semantic search, infer relationships)

## Target Architecture

```
spec-cli/src/
├── main.rs (minimal, entry point)
├── commands/
│   ├── mod.rs (command trait)
│   ├── add.rs
│   ├── check.rs
│   ├── trace.rs
│   ├── find.rs
│   ├── extract.rs
│   └── api/ (low-level graph operations)
│       ├── add_node.rs
│       ├── add_edge.rs
│       └── ...
├── presentation/
│   ├── mod.rs
│   ├── formatter.rs (output formatting)
│   └── messages.rs (user messages)
├── persistence/
│   ├── mod.rs
│   └── store_router.rs (standalone vs server selection)
└── ai/
    ├── mod.rs
    └── semantic.rs (AI-powered features)
```

## Implementation Plan

### Phase 1: Extract Presentation Layer (Priority 1)
- Create `presentation/` module
- Move output formatting logic
- Keep command logic in main.rs for now
- **Benefit**: Immediate reduction, low risk

### Phase 2: Extract Persistence Routing (Priority 2)
- Create `persistence/` module
- Move standalone vs server selection logic
- Centralize store access

### Phase 3: Extract Command Implementations (Priority 3)
- Create `commands/` module
- Move command implementations one by one
- Keep parsing in main.rs

### Phase 4: Extract AI Features (Priority 4)
- Create `ai/` module
- Move semantic search, inference logic

### Phase 5: Verify Self-Governance (Final)
- Extract architectural properties from new structure
- Run `spec check`
- Verify: 0 contradictions (CLI violation resolved)
- Update specifications

## Success Criteria

1. ✅ main.rs < 500 lines (90% reduction)
2. ✅ Separate modules for each concern
3. ✅ `spec check` shows 0 contradictions
4. ✅ All tests pass
5. ✅ Architectural property extraction can verify compliance
6. ✅ specORACLE successfully governs itself

## Commits

Each phase will be committed separately (smallest possible units).

## Status

- [x] Phase 1: Extract Presentation (✓ Complete - formatter module, 97 lines)
- [x] Phase 2: Extract Persistence (✓ Complete - store_router module, 58 lines)
- [x] Phase 3a: Extract Utilities (✓ Complete - utils module, 159 lines)
- [ ] Phase 3b: Extract Commands (In Progress - Session 111)
  - [x] Add command extracted (add.rs, 158 lines)
  - [x] Check command extracted (check.rs, 204 lines)
  - [ ] Remaining ~30 commands to extract
- [ ] Phase 4: Extract AI
- [ ] Phase 5: Verify Self-Governance

## Progress

- Original main.rs: 4475 lines
- After Phase 1: 4444 lines (-31 lines)
- After Phase 2: 4432 lines (-12 lines)
- After Phase 3a: 4309 lines (-123 lines)
- After Phase 3b (Session 111): 4180 lines (-129 lines)
- **Total reduction: 295 lines (6.59%)**
- **Commands module: 372 lines**
- **Target: < 500 lines (90% reduction)**
- **Remaining: 3680 lines to extract**
