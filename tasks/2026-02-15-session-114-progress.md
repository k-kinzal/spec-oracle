# Session 114 Progress: CLI Architecture Refactoring

## Current Status (2026-02-15)

### Metrics
- **main.rs size**: 2717 lines (down from 3736, -1019 lines, -27.3%)
- **Goal**: <500 lines
- **Remaining**: ~2217 lines to extract
- **Completion**: 27.3% done

### Completed
- ✅ Created `commands/api.rs` - 172 lines (9 API commands)
- ✅ Created `commands/summary.rs` - 90 lines
- ✅ Created `commands/extract.rs` - 112 lines (reverse mapping f₀ᵢ⁻¹)
- ✅ Created `commands/prover.rs` - 390 lines (ProveConsistency, ProveSatisfiability, InspectModel)
- ✅ Created `commands/u0.rs` - 292 lines (ConstructU0, CleanupLowQuality)
- ✅ Created `commands/layer.rs` - 161 lines (VerifyLayers, DetectLayerInconsistencies)
- ✅ Fixed imports in api.rs (format_formality_layer from presentation::formatter)
- ✅ Fixed function calls in main.rs (added commands:: prefix)
- ✅ Updated `run_standalone()` to delegate to command modules
- ✅ All 71 tests still passing
- ✅ Committed: b4e7bf5

### Extraction History
1. **Session 113**: API commands, Summary, Extract (248 lines)
2. **Session 114 (early)**: Prover, U0 commands (871 lines)
3. **Session 114 (current)**: Layer commands (148 lines)
4. **Total extracted**: 1267 lines across 6 new modules

### Remaining Work

#### Phase 1: Command Extraction (75% remaining)
Commands still in main.rs that need extraction:
- **GetNode** - low-level API operation (already in api namespace, just needs extraction)
- **InferRelationships, InferRelationshipsAi** - relationship inference operations
- **Watch** - file watching functionality
- **ResolveTerm, FindRelatedTerms, DetectPotentialSynonyms** - semantic search operations
- **All deprecated/legacy commands** (AddNode, AddEdge, ListNodes, RemoveNode, etc.)
- **All server mode duplicates** (lines ~1000-2700)

Estimated: ~20-25 more command handlers to extract

#### Phase 2: Business Logic Extraction
Create `use_cases/` module for:
- Semantic similarity (`is_semantically_related`)
- Relationship inference logic
- Conflict detection utilities
- Model inspection logic
- U0 construction logic

#### Phase 3: Server Mode Refactoring
- The main() function has a second giant match statement (lines ~1000-2700)
- This duplicates most command logic for server mode
- Need to unify server/standalone command handling
- Consider: route all server commands through standalone implementations where possible

#### Phase 4: Utility Functions
Create modules for scattered utility functions:
- Semantic similarity functions
- AI query handling
- Format/parse helpers (already partially in utils.rs and presentation/formatter.rs)

### Architecture Goal

```
main.rs (<500 lines)
├── CLI definition (clap)
├── Simple dispatch
└── Mode detection (standalone vs server)

commands/
├── api.rs - Low-level graph operations ✅
├── add.rs, check.rs, find.rs, trace.rs, etc. - High-level commands ✅
├── extract.rs - Reverse mapping ✅
├── prover.rs - Formal verification ✅
├── u0.rs - U0 construction ✅
├── layer.rs - Layer verification ✅
└── [15-20 more command modules]

use_cases/ (future)
├── semantic_similarity.rs
├── relationship_inference.rs
└── conflict_detection.rs

presentation/ ✅
└── formatter.rs (already exists)

persistence/ ✅
└── store_router.rs (already exists)
```

### Self-Governance Status

specORACLE is detecting its own violation:
```
Contradictions:
  1. [d26341fb] CLI violates separation (4475 lines → now 2717 lines)
     vs
     [b706e529] CLI must separate concerns
```

The contradiction will resolve when main.rs < 500 lines and follows the architectural pattern.

## Recent Commits
- **b4e7bf5**: Extract layer verification commands (-148 lines, -5.2%)
- **0b49195**: Extract Prover and U0 commands (-871 lines, -23.3%)
- **9b780f5**: Extract API, Summary, Extract commands (-248 lines)

## Next Steps (Priority Order)

1. **Extract relationship commands** to `commands/relationships.rs`:
   - InferRelationships
   - InferRelationshipsAi
   - Expected reduction: ~100-150 lines

2. **Extract semantic search commands** to `commands/semantic.rs`:
   - ResolveTerm
   - FindRelatedTerms
   - DetectPotentialSynonyms
   - FindFormalizations
   - Expected reduction: ~150-200 lines

3. **Extract remaining low-level commands** to existing `commands/api.rs`:
   - GetNode
   - Any other API-level operations in standalone mode
   - Expected reduction: ~50-100 lines

4. **Refactor server mode duplicates**:
   - Unify server/standalone implementations
   - Route server commands through standalone where possible
   - Expected reduction: ~800-1000 lines (largest single reduction)

5. **Extract utility functions** to dedicated modules:
   - is_semantically_related
   - handle_ai_query
   - extract_and_sync
   - Expected reduction: ~200-300 lines

## Estimated Effort
- Phase 1 (remaining command extraction): 2-3 hours
- Phase 2 (server mode unification): 2-3 hours
- Phase 3 (utility extraction): 1 hour
- **Total remaining**: 5-7 hours of refactoring work

## Risk Assessment
- **Test coverage**: All 71 tests passing, low risk
- **Incremental approach**: Can commit after each extraction
- **Backward compatibility**: Internal refactoring, no API changes
- **Build stability**: Z3 linking resolved with RUSTFLAGS
