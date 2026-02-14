# Session 114 Progress: CLI Architecture Refactoring

## Current Status (2026-02-15)

### Metrics
- **main.rs size**: 3488 lines (down from 3736, -248 lines, -6.6%)
- **Goal**: <500 lines
- **Remaining**: ~3000 lines to extract

### Completed
- ✅ Created `commands/api.rs` - 172 lines (9 API commands)
- ✅ Created `commands/summary.rs` - 90 lines
- ✅ Created `commands/extract.rs` - 112 lines (reverse mapping f₀ᵢ⁻¹)
- ✅ Updated `run_standalone()` to delegate to command modules
- ✅ All 71 tests still passing
- ✅ Committed: 9b780f5

### Remaining Work

#### Phase 1: Command Extraction (80% remaining)
Commands still in main.rs that need extraction:
- GetNode, VerifyLayers, ProveConsistency, ProveSatisfiability
- InspectModel, ConstructU0, CleanupLowQuality
- Watch, InferRelationshipsAi
- All deprecated commands (AddNode, AddEdge, ListNodes, etc.)
- All server mode duplicates

Estimated: ~30 more command handlers to extract

#### Phase 2: Business Logic Extraction
Create `use_cases/` module for:
- Semantic similarity (`is_semantically_related`)
- Relationship inference
- Conflict detection
- Model inspection
- U0 construction logic

#### Phase 3: AI Integration Extraction
Create `ai/` module for:
- `handle_ai_query` function
- AI-powered relationship inference
- Query enhancement logic

#### Phase 4: Server Mode Refactoring
- The main() function has a second giant match statement (lines ~1800-3600)
- This duplicates most command logic for server mode
- Need to unify server/standalone command handling

### Architecture Goal

```
main.rs (<500 lines)
├── CLI definition (clap)
├── Simple dispatch
└── Mode detection (standalone vs server)

commands/
├── api.rs - Low-level graph operations
├── add.rs, check.rs, find.rs, trace.rs, etc. - High-level commands
├── extract.rs - Reverse mapping
└── [30+ more command modules]

use_cases/
├── semantic_similarity.rs
├── relationship_inference.rs
└── conflict_detection.rs

ai/
├── query_enhancement.rs
└── relationship_inference.rs

presentation/
└── formatter.rs (already exists)

persistence/
└── store_router.rs (already exists)
```

### Self-Governance Status

specORACLE is still detecting its own violation:
```
Contradictions:
  1. [d26341fb] CLI violates separation (spec says 4475 lines)
     vs
     [b706e529] CLI must separate concerns
```

The contradiction will resolve when main.rs < 500 lines and follows the architectural pattern.

## Estimated Effort
- Phase 1 (command extraction): 2-3 hours
- Phase 2 (use cases): 1 hour
- Phase 3 (AI module): 30 minutes
- Phase 4 (server unification): 1-2 hours
- **Total**: 5-7 hours of refactoring work

## Risk Assessment
- **Test coverage**: All tests passing, low risk
- **Incremental approach**: Can commit after each extraction
- **Backward compatibility**: Internal refactoring, no API changes
