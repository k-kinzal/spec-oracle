# Session 95: Investigation of 225 Isolated Specifications

**Date**: 2026-02-14
**Goal**: Understand why extracted specifications remain isolated and achieve full U0 integration

## Current State

### Specification Summary
- **Total specifications**: 363
- **Extracted specifications**: 234 (64.5%)
- **Isolated specifications**: 225 ⚠️
- **Contradictions**: 0 ✓

### Layer Distribution (from construct-u0)
- U0: 464 total after construction
- U1: 8 specifications
- U2: 93 specifications (gRPC proto interfaces)
- U3: 185 specifications (implementation/code)
- Transform functions: 11

### Extracted Spec Breakdown
- **Assertion**: 57
- **Constraint**: 117
- **Scenario**: 60

## Root Cause Analysis

### Problem 1: Low-Quality Extraction
Extracted specifications are raw test names, not meaningful spec statements:
```
- "scenario {}"
- "coverage empty graph"
- "coverage no tests"
- "coverage with tests"
- "Invariant: fetched.content, "U""
- "user login"
```

**Impact**: These lack semantic content to match with U0 requirements.

### Problem 2: Weak Semantic Matching
`infer_relationships_for_node` uses keyword-based Jaccard similarity:
```rust
similarity = intersection(keywords) / union(keywords)
if similarity < 0.3 { skip }  // Too dissimilar
```

**Example failure**:
- Extracted (U3): "coverage empty graph"
- U0 requirement: "The system must detect omissions where specifications have no relationships"
- Keyword overlap: ~0% → No relationship created

### Problem 3: Cross-Layer Matching Not Prioritized
- U3 specs (implementation details) need to connect to U0 specs (requirements)
- Current `ingest()` compares against **all nodes** equally
- No explicit "find the U0 spec this implements" logic

### Problem 4: Missing source_type Metadata
All 234 extracted specs have `source_type: null`:
```json
{
  "metadata": {
    "inferred": "true",
    "source_type": null  // ← Missing!
  }
}
```

**Impact**: Cannot distinguish test-extracted from code-extracted specs.

## Technical Analysis

### `construct_u0` Flow
```
1. UDAFModel.populate_from_graph(graph)
2. For each universe (U1, U2, U3):
   - Find inverse transform: f_U3_to_U0
   - Execute transform strategy (RustExtractor)
   - Extract specs → IDs only: "extracted:file:line:content"
3. Does NOT add specs to graph
4. Does NOT create edges
```

**Result**: `construct_u0` demonstrates theory but doesn't persist extracted specs.

### `spec extract` Flow
```
1. RustExtractor.extract(path) → Vec<InferredSpecification>
2. Filter by confidence >= 0.7
3. graph.ingest(specs) →
   a. Create nodes (metadata.inferred="true")
   b. infer_relationships_for_node(new_id)
   c. Auto-create edges if confidence >= 0.8
   d. Suggest edges if confidence >= 0.5
4. Save graph
```

**Result**: Specs ARE persisted, but relationships fail due to weak matching.

### `ingest()` Relationship Inference
```rust
for new_node in created_nodes:
    suggestions = infer_relationships_for_node(new_node.id)
    for suggestion in suggestions:
        if confidence >= 0.8: auto_create_edge()
        elif confidence >= 0.5: add_to_review_queue()
```

**Problem**: Confidence rarely exceeds 0.5 for cross-layer matches.

## Evidence from Codebase

### spec-core/src/extract.rs:373-414
```rust
fn infer_relationships_for_node(&self, node_id: &str) -> Vec<EdgeSuggestion> {
    let source_node = self.get_node(node_id)?;
    let all_nodes = self.list_nodes(None);

    for target_node in all_nodes {
        let similarity = self.calculate_semantic_similarity(
            &source_node.content,
            &target_node.content,
        );

        if similarity < 0.3 {
            continue; // ← Isolated specs fail here
        }

        if let Some((edge_kind, confidence, explanation)) =
            self.infer_edge_kind(source_node, target_node, similarity) {
            suggestions.push(EdgeSuggestion { ... });
        }
    }
}
```

### spec-core/src/extract.rs:417-435
```rust
fn calculate_semantic_similarity(&self, text1: &str, text2: &str) -> f32 {
    let words1: HashSet<String> = text1.split_whitespace().collect();
    let words2: HashSet<String> = text2.split_whitespace().collect();

    let intersection = words1.intersection(&words2).count();
    let union = words1.union(&words2).count();

    intersection as f32 / union as f32  // Jaccard coefficient
}
```

**Limitation**: "coverage empty graph" vs "detect omissions" → 0% overlap.

## The Essence of specORACLE (CLAUDE.md Violation)

**Stated goal**:
> "specORACLE is a reverse mapping engine. It does not manage specifications written by humans. It constructs U0 (the root specification) from diverse artifacts through reverse mappings."

**Current reality**:
- ✓ Reverse mapping implemented (RustExtractor)
- ✓ 234 specs extracted automatically
- ✗ **Extracted specs isolated, not integrated into U0**
- ✗ **No cross-layer semantic bridging**

**Quote from CLAUDE.md**:
> "NOTE: You are running away from the essence of specORACLE. Nothing has been achieved."

## What Success Looks Like

### Target State
1. **Zero isolated specs** (or only legitimate isolates)
2. **Cross-layer traceability**: Each U3 spec links to U2/U0 specs
3. **Automatic U0 construction**: `construct-u0 --execute` creates AND persists specs
4. **Rich metadata**: source_type, extraction_method, confidence tracking

### Example Connection (currently missing)
```
U0: "System must detect contradictions between specifications"
  ↓ formalizes
U2: "DetectContradictions RPC returns Contradiction messages"
  ↓ formalizes
U3: "test_detect_contradictions_finds_password_length_conflict()"
     (extracted assertion: "Password 8 chars vs 10 chars contradiction detected")
```

## Proposed Solutions

### Option A: Improve Extraction Quality
- **Enhance RustExtractor** to generate semantic descriptions
  - "coverage empty graph" → "Test verifies coverage calculation for empty specification graph"
  - "scenario {}" → "Test verifies scenario specification can be created with empty content"
- Add doc comments as context for better understanding

### Option B: Implement Cross-Layer AI Matching
- Use `infer_cross_layer_relationships_with_ai()` (already exists!)
- AI can bridge semantic gap:
  - U3: "coverage no tests"
  - U0: "System must detect when specifications lack test coverage"
  - AI similarity: high (despite low keyword overlap)

### Option C: Explicit U0 Anchoring During Extraction
- When extracting U3 specs, **immediately search for U0 counterpart**
- Use function/test name as query: "coverage" → find "detect omissions" U0 spec
- Create `formalizes` edge during ingestion (not post-hoc)

### Option D: Two-Phase Ingestion
1. **Phase 1**: Extract & create nodes (current behavior)
2. **Phase 2**: Run `infer-cross-layer-with-ai` as separate step
   - User reviews AI suggestions
   - Confirms high-confidence matches
   - Manually bridges remaining gaps

## Immediate Next Steps

### Step 1: Verify AI Integration
```bash
# Check if AI semantic matching is available
which claude || which codex

# Test AI-enhanced cross-layer matching
./target/release/spec infer-cross-layer-with-ai --min-confidence 0.6
```

### Step 2: Analyze Isolated Specs
```bash
# Sample isolated specs to understand patterns
jq '.graph.nodes |
    map(select(.metadata.inferred == "true")) |
    group_by(.kind) |
    map({kind: .[0].kind, samples: .[0:3] | map(.content)})' \
    .spec/specs.json
```

### Step 3: Manual Connection Experiment
- Pick 5 isolated U3 specs
- Manually find their U0 counterparts
- Create `formalizes` edges
- Document similarity scores & inference patterns

### Step 4: Implement Auto-Connection
Based on manual experiment, enhance `ingest()`:
```rust
// After creating node, do targeted U0 search
let u0_candidates = self.find_u0_specs_for_extracted(new_node);
for (u0_spec, confidence) in u0_candidates {
    if confidence > 0.7 {
        self.add_edge(u0_spec.id, new_node.id, EdgeKind::Formalizes);
    }
}
```

## Success Metrics

- [ ] `spec check` reports **0 isolated specifications**
- [ ] Every extracted U3 spec has >= 1 edge to U0/U2
- [ ] `spec trace <u0-spec-id>` shows full U0→U1→U2→U3 chain
- [ ] `construct-u0 --execute` creates self-connecting graph

## References

- **CLAUDE.md**: Core concept of reverse mapping engine
- **PROBLEM.md**: Multiple issues related to isolation (矛盾検出, 漏れ検出)
- **conversation.md**: U/D/A/f model, U0 construction theory
- **Session 93**: First successful extraction (178 specs), but isolation problem already present

---

## Next Session Continuation Points

1. Run AI-enhanced cross-layer matching experiment
2. Profile similarity scores for current isolated specs
3. Implement targeted U0 search during ingestion
4. Consider creating "extraction pipeline" command:
   ```bash
   spec pipeline extract-and-integrate spec-core/src/
   ```
