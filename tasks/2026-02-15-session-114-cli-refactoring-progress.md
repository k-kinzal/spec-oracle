# Session 114: CLI Refactoring - Command Extraction Progress

## Goal
Continue CLI refactoring toward coherent layered structure (resolving Critical issue: "spec-cliが継ぎ足し実装の集合になっており、体系化された操作モデルとHuman Friendlyな体験が崩壊している")

## Progress Summary

### Line Reduction
- **Started**: 2717 lines in main.rs
- **Ended**: 2172 lines
- **Total Reduction**: -545 lines (-20.1%)

### Commands Extracted

1. **Init command** → `commands/init.rs` (187 lines)
   - Project initialization logic
   - .spec directory structure creation
   - Server management scripts generation

2. **InferRelationshipsAi** → `commands/relationships.rs` (35 lines)
   - AI-powered semantic relationship inference
   - Cross-layer relationship matching

3. **Watch command** → `commands/watch.rs` (66 lines + 120 lines helpers)
   - File watching and synchronization
   - Helper functions: extract_and_sync, verify_specifications, should_process_event

4. **Deprecated commands simplified**:
   - GetNode: 103 lines → 3 lines (using api module)
   - AddEdge: 48 lines → 3 lines (using api module)

### Current Command Module Structure

**16 command modules** (alphabetically):
- add.rs - High-level specification addition
- api.rs - Low-level graph API operations
- check.rs - Unified contradiction + omission checking
- contradictions.rs - Contradiction detection
- extract.rs - Code extraction
- find.rs - Semantic search
- **init.rs** ✨ NEW - Project initialization
- layer.rs - Layer verification
- omissions.rs - Omission detection
- prover.rs - Formal verification (Prove*, Inspect)
- query.rs - Natural language queries
- **relationships.rs** ✨ NEW - Relationship inference
- summary.rs - Summary statistics
- trace.rs - Relationship tracing
- u0.rs - U0 construction & cleanup
- **watch.rs** ✨ NEW - File watching

### Commits
1. `380929e` - Extract Init, relationships, simplify deprecated commands (-361 lines)
2. `8b94a10` - Extract Watch command and helper functions (-184 lines)

## Remaining Work

### High Priority
- Extract remaining server-mode inline commands:
  - ResolveTerm
  - Ask (AI Q&A)
  - FindFormalizations
  - FindRelatedTerms
  - DetectPotentialSynonyms
  - InferRelationships (non-AI version)

### Medium Priority
- Organize commands by domain:
  - Terminology commands (ResolveTerm, FindRelatedTerms, DetectPotentialSynonyms)
  - AI commands (Ask, InferRelationshipsAi)
  - Temporal commands (QueryAtTimestamp, DiffTimestamps, NodeHistory)
  - Compliance commands (TestCoverage, ComplianceReport, CheckCompliance)

### Low Priority
- Remove or stub out unimplemented temporal/compliance commands
- Further consolidate deprecated commands
- Consider creating command groups/submodules

## Metrics

- **Command modules**: 13 → 16 (+3)
- **main.rs size**: 2717 → 2172 lines (-20.1%)
- **Modularization**: ~25% complete (estimated)
- **Tests**: All 71 tests passing ✅

## Next Steps

1. Continue extracting remaining inline commands
2. Group related commands into submodules
3. Establish clear command layering (high-level vs. low-level)
4. Document command organization in README

## Related Issue

PROBLEM.md: "spec-cliが継ぎ足し実装の集合になっており、体系化された操作モデルとHuman Friendlyな体験が崩壊している"
- Status: In Progress
- Specification nodes: [c6119c42], [c6920b06], [b706e529]
