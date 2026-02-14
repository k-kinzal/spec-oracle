# Session: Investigate Isolated proto_rpc Specifications

**Date**: 2026-02-15
**Goal**: Understand and resolve 32 isolated specifications (primarily proto_rpc)

## Current State

```bash
$ spec check
Total specs:        184
Isolated specs:     32 (17.4%)
  - proto_rpc: 24 specs
  - doc: 1 specs
  - test: 2 specs
```

## Investigation

### Proto RPC Specifications

- 16 specifications with "RPC:" prefix found
- Metadata: `extractor: "proto_rpc"`, `inferred: "true"`, `confidence: "0.95"`
- Examples:
  - RPC: Set node universe
  - RPC: Get compliance trend
  - RPC: Get node history
  - RPC: Diff timestamps
  - RPC: Get compliance report

### Root Cause

These specifications were extracted by ProtoExtractor (Session 97) but remain isolated because:

1. **Semantic similarity failure**: RPC names (technical, concise) vs requirement specs (natural language, descriptive)
2. **Vocabulary mismatch**: "GetComplianceTrend" vs "compliance report" vs "trend analysis"
3. **No manual connections**: Automated edge inference failed due to low similarity scores

### Discrepancy

- `spec check` reports "proto_rpc: 24 specs"
- `jq` finds only 16 specs with "RPC:" prefix
- Need to investigate metadata.extractor filtering in detect_omissions()

## Understanding of specORACLE

As a specification description tool, specORACLE currently provides:

### Core Features (Recorded in Specifications)

1. **Specification Management**:
   - `spec add` - Natural language spec creation with automatic kind inference
   - `spec find` - Semantic search with layer filtering
   - `spec trace` - Hierarchical relationship visualization
   - `spec check` - Unified contradiction and omission detection

2. **Multi-Layer Tracking** (U0→U2→U3):
   - U0: Natural language requirements
   - U2: Interface specifications (gRPC proto, API definitions)
   - U3: Implementation specifications (code, tests, contracts)
   - Formalizes edges connecting layers

3. **Reverse Mapping Engine**:
   - `RustExtractor` - Extracts specs from Rust code (Session 93: 178 specs)
   - `ProtoExtractor` - Extracts specs from gRPC proto (Session 97: 28 specs)
   - Idempotent extraction (deduplication via find_node_by_content)
   - U0 construction: U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3)

4. **Project-Local Management**:
   - `.spec/specs.json` - Project-specific specifications
   - Standalone mode - No server required
   - Auto-detection - Traverses directories to find .spec/

5. **Quality Assurance**:
   - Contradiction detection (exact duplicates, semantic conflicts, explicit edges)
   - Omission detection (isolated nodes, uncovered domains, missing assertions)
   - Multi-layer consistency verification

### Core Essence (from CLAUDE.md)

**specORACLE is a reverse mapping engine.**

It does NOT manage specifications written by humans.
It constructs U0 (the root specification) from diverse artifacts through reverse mappings.

### Current Gap

The reverse mapping engine successfully extracts specifications but fails to integrate them:

- Extraction works: 178 specs from Rust code, 28 specs from proto
- Integration fails: 32 isolated specs (17.4% of total)
- Root cause: Semantic similarity matching insufficient for technical names

## Root Cause Analysis

### Timing Issue

Proto_rpc specifications were extracted at: 1771078430 (2024-02-14 23:53:50)
Related U0 specifications were added at: 1771088204 (2024-02-15 01:50:04)

**The proto_rpc specs were extracted BEFORE the related U0 specs existed.**

Automatic edge inference only runs during extraction (`ingest()` method), so these later-added U0 specs were never connected to the proto_rpc specs.

### Example: Missing Connection

**U2 spec** (proto_rpc, isolated):
- "AI-powered relationship inference (cross-layer semantic matching)"
- RPC: InferAllRelationshipsWithAi
- Created: 2024-02-14 23:53:50

**U0 spec** (should be connected):
- "Cross-layer edge inference uses layer-aware similarity threshold..."
- Created: 2024-02-15 01:50:04

**Semantic similarity**: {"cross-layer", "inference"} = 2/10 = 0.2
**Threshold**: 0.15 (cross-layer)
**Expected**: Edge should be created (0.2 > 0.15)
**Actual**: No edge (because U0 spec didn't exist during extraction)

### Attempted Solutions

1. ❌ **`spec infer-relationships`** - Not supported in standalone mode
2. ❌ **`spec infer-relationships-ai`** - Takes too long (timeout after 2 minutes)
3. ✅ **Manual connection script** - Session 66-68 precedent

## Core Issue: Incomplete Reverse Mapping Engine

**Current behavior**:
- ✅ Extraction is automatic (RustExtractor, ProtoExtractor)
- ❌ Integration is incomplete (only runs during extraction)
- ❌ Re-integration after new U0 specs is not automatic

**Expected behavior** (from CLAUDE.md):
> specORACLE is a reverse mapping engine.
> It constructs U0 (the root specification) from diverse artifacts through reverse mappings.

The reverse mapping engine should:
1. Extract specifications from artifacts (✅ working)
2. Integrate them into the graph (⚠️ partial - only during extraction)
3. Re-integrate when new specs are added (❌ not working)

## Decision: Minimal Manual Connection

Based on Session 66-68 precedent and CLAUDE.md constraints:
- Commits should be in smallest possible units
- No planning mode
- No asking user questions

**Approach**: Create targeted connection script for the 24 isolated proto_rpc specs.

## Resolution

### Scripts Created

1. **connect_isolated_proto_rpc.py** - First pass (15 connection patterns)
2. **connect_remaining_proto_rpc.py** - Second pass (13 connection patterns)

### Results

**Before**:
- 32 isolated specs (17.4%)
- proto_rpc: 24 specs

**After**:
- 15 isolated specs (8.2%)
- proto_rpc: 8 specs

**Reduction**:
- 17 specs connected (53.1% reduction)
- 33 edges created manually

### Remaining Isolated Specs (15)

- **proto_rpc: 8 specs** - Basic CRUD operations without clear U0 counterparts
  - RPC: Diff timestamps
  - RPC: Remove edge
  - RPC: List edges
  - Edge operations
  - RPC: Remove node
  - RPC: List nodes
  - RPC: Get node
  - Node operations
- **doc: 1 spec** - Documentation-related
- **test: 2 specs** - Test-related

### Known Limitation

**Re-integration is not automatic**:
- Extraction triggers automatic edge inference (`ingest()`)
- Adding new U0 specs later does NOT trigger re-inference
- Manual connection scripts required for post-extraction integration

This is a **fundamental limitation** of the current reverse mapping engine:
- ✅ Extraction is automatic
- ⚠️  Integration is semi-automatic (only during extraction)
- ❌ Re-integration is manual

## Conclusion

Isolated specifications reduced from 32 (17.4%) to 15 (8.2%), achieving 53.1% reduction through manual connection scripts. This resolves the immediate isolation issue but does not address the fundamental limitation of the reverse mapping engine's integration process.

**Status**: ✅ **Isolation significantly reduced** but core integration limitation remains.

## Specification Status

Current specORACLE specifications cover:
- ✅ Add/find/trace/check commands (U0→U2→U3)
- ✅ Contradiction/omission detection (U0→U2→U3)
- ✅ RustExtractor extraction (Session 93)
- ✅ ProtoExtractor extraction (Session 97)
- ❌ **Re-integration after new specs added** (known limitation)
- ❌ **Automatic relationship inference in standalone mode** (not implemented)
