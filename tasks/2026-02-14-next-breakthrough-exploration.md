# Next Breakthrough: Beyond Manual Specification

**Date**: 2026-02-14
**Context**: Exploring how to transcend DSL limitations identified in conversation.md

## The Core Problem Restated

From conversation.md, the fundamental issue:

> "人間にはこの形式で仕様管理を行うのは不可能だと思います。表現しきれないものは種類を増やしますか？無限に増やしますか？結局そういう話であり現実ではないです。"
> "I think it's impossible for humans to manage specifications in this format. If something can't be expressed, do you add more types? Do you add infinitely many? It's ultimately that kind of thing and not reality."

**The Issue**: Any DSL (including our graph-based one) forces humans to:
1. Choose the right node/edge types
2. Express all relationships manually
3. Keep the graph consistent as system evolves
4. Verify completeness (no omissions)

As systems grow, this becomes **cognitively impossible**.

## Current Approaches and Their Limits

### 1. Manual Graph Construction (Current spec-oracle)

**Method**: Users explicitly create nodes and edges
**Strength**: Full control, clear semantics
**Weakness**: Doesn't scale to real systems with thousands of specifications

### 2. Specification Extraction from Code

**Method**: Parse code to extract specifications
**Examples**:
- Dafny: Extract contracts from code annotations
- TypeScript: Extract interface specs from type definitions
- QuickCheck: Property-based test = specification

**Strength**: Specifications stay synchronized with code
**Weakness**: Only captures what's in code, not intent; Still requires manual annotation

### 3. Specification Inference from Behavior

**Method**: Observe system behavior, infer specifications
**Examples**:
- Daikon: Infer invariants from test executions
- Symbolic execution: Derive path constraints
- Fuzzing: Discover input grammars

**Strength**: Discovers specifications humans didn't think to write
**Weakness**: Incomplete (only covers observed behavior), may infer wrong specifications

## The Synthesis Insight: Multi-Source Specification Aggregation

### The Key Realization

Real-world specifications exist in **multiple forms already**:

| Source | Type | Example |
|--------|------|---------|
| Code comments | Natural language | `// User must be authenticated` |
| Function names | Structured text | `validate_password_strength()` |
| Type signatures | Formal specification | `fn process(user: AuthenticatedUser)` |
| Assertions | Executable constraints | `assert!(password.len() >= 8)` |
| Unit tests | Behavioral scenarios | `test_rejects_weak_passwords()` |
| Documentation | Intent explanation | "Passwords must meet NIST 800-63B" |
| API specs (OpenAPI) | Interface contracts | `minLength: 8` |
| Database schemas | Data constraints | `NOT NULL, CHECK(...)` |
| Runtime monitors | Enforcement code | `if !user.is_admin() { return Err(...) }` |

**The Problem**: These exist in isolation. No tool unifies them.

**The Opportunity**: Build a **specification aggregator** that:
1. **Extracts** specifications from all sources automatically
2. **Normalizes** them into the spec-oracle graph
3. **Detects contradictions** across sources
4. **Identifies omissions** (what's in tests but not in docs?)
5. **Synthesizes** a unified specification from fragments

### This Addresses the DSL Limitation

Users don't need to manually build the graph in a DSL. Instead:
- Write code naturally (with types, tests, assertions)
- Write docs naturally (markdown, comments)
- The tool **infers** the specification graph automatically
- Users only **correct** inferred specifications, not create from scratch

## Concrete Implementation Approach

### Phase 1: Multi-Source Extractors

Build extractors for common specification sources:

```rust
trait SpecificationExtractor {
    fn extract(&self, source: &Path) -> Vec<InferredSpecification>;
}

struct InferredSpecification {
    content: String,
    kind: NodeKind,        // Inferred node type
    confidence: f32,        // 0.0-1.0
    source_file: String,
    source_line: usize,
    formality_layer: u8,
}

// Extractors
struct RustTypeExtractor;      // Extract from type signatures
struct RustTestExtractor;      // Extract from #[test] functions
struct RustDocExtractor;       // Extract from /// comments
struct OpenAPIExtractor;       // Extract from openapi.yaml
struct SQLSchemaExtractor;     // Extract from CREATE TABLE
struct ProtoExtractor;         // Extract from .proto files
```

### Phase 2: Automatic Graph Construction

```rust
impl SpecGraph {
    /// Ingest specifications from multiple sources, auto-create nodes/edges
    pub fn ingest(&mut self, inferred_specs: Vec<InferredSpecification>) -> IngestionReport {
        for spec in inferred_specs {
            // Create node
            let node_id = self.add_inferred_node(spec);

            // Infer relationships with existing nodes
            let potential_edges = self.infer_relationships(&node_id);

            for (target, edge_kind, confidence) in potential_edges {
                if confidence > 0.7 {  // High confidence threshold
                    self.add_edge(&node_id, &target, edge_kind, metadata);
                } else {
                    // Flag for human review
                    report.suggestions.push((node_id, target, edge_kind, confidence));
                }
            }
        }
    }

    /// Use AI to infer relationships between specifications
    fn infer_relationships(&self, node_id: &str) -> Vec<(String, EdgeKind, f32)> {
        // Use semantic similarity (AI embeddings) to find related specs
        // If spec A says "password >= 8" and spec B says "validate password length",
        // infer: B refines A, or B implements A
    }
}
```

### Phase 3: Cross-Source Contradiction Detection

```rust
impl SpecGraph {
    /// Detect contradictions across different sources
    pub fn detect_cross_source_contradictions(&self) -> Vec<CrossSourceContradiction> {
        // Example: Type says `Option<User>` (can be None)
        //          Test asserts user is always present
        //          Documentation says "user is required"
        // These contradict: Some sources allow None, others forbid it
    }
}

struct CrossSourceContradiction {
    spec_a: InferredSpecification,  // From types
    spec_b: InferredSpecification,  // From tests
    explanation: String,
    severity: ContradictionSeverity,  // Critical, Warning, Info
}
```

### Phase 4: Specification Synthesis

```rust
impl SpecGraph {
    /// Synthesize unified specification from multiple sources
    pub fn synthesize_spec(&self, topic: &str) -> SynthesizedSpecification {
        // Collect all specifications related to topic
        let fragments = self.query_related(topic);

        // Group by formality layer
        let natural = fragments.filter(|s| s.formality_layer == 0);
        let formal = fragments.filter(|s| s.formality_layer >= 2);

        // Use AI to synthesize coherent specification
        // "Based on types, tests, and docs, the unified spec for X is..."
    }
}
```

## Why This Transcends DSL Limitations

### Traditional DSL Approach (spec-oracle v1)

1. User thinks: "What specifications exist?"
2. User writes: `add-node "Password >= 8 chars" --kind constraint`
3. User maintains: Manually updates when code changes
4. **Cognitive load**: User must know all specs and express them correctly

### Inference-Based Approach (spec-oracle v2)

1. Tool scans: Code, tests, docs, schemas
2. Tool infers: "I see 5 password constraints from different sources"
3. Tool detects: "Test requires 8 chars, but OpenAPI spec says 6—contradiction"
4. User reviews: Confirms or corrects inferred specifications
5. **Cognitive load**: User only fixes errors, doesn't create from scratch

### Key Difference

**v1**: User is the source of truth → Must manually encode everything
**v2**: Code/tests/docs are source of truth → Tool extracts and unifies

This doesn't eliminate DSL entirely, but **inverts the burden**:
- DSL is the output, not the input
- Users work in familiar formats (code, markdown)
- Tool does the heavy lifting of graph construction

## Addressing the "Ruler" Problem

The conversation.md asks: How do we verify that verifications are correct?

### Insight from Multi-Source Aggregation

**The "ruler" emerges from consensus across sources.**

If 5 different sources say the same thing, confidence is high:
- Type signature: `password: String` with constraint `len >= 8`
- Unit test: `assert!(password.len() >= 8)`
- OpenAPI spec: `minLength: 8`
- Documentation: "Passwords must be at least 8 characters"
- Database schema: `CHECK (LENGTH(password) >= 8)`

If sources contradict, **that's the detection mechanism**:
- Test says >= 8
- OpenAPI says >= 6
- **Contradiction detected without meta-verification**

The ruler isn't a perfect external standard—it's **triangulation across multiple imperfect sources**.

## Implementation Roadmap

### MVP: Single-Source Extraction

**Goal**: Prove the concept with one extractor

```bash
# Extract specifications from Rust code
./spec extract --source ./src --language rust

# Results in automatically populated graph
./spec list-nodes
# Shows inferred constraints, assertions, scenarios

./spec detect-contradictions
# Shows conflicts between code and tests
```

**Scope**: ~500 LOC
- Rust code parser (use `syn` crate)
- Extract type constraints, assertions, test scenarios
- Auto-create graph nodes

### Phase 2: Multi-Source Aggregation

**Goal**: Combine specifications from different sources

```bash
./spec extract --source ./src --language rust
./spec extract --source ./docs --format markdown
./spec extract --source ./api --format openapi

./spec detect-cross-source-contradictions
# "Type says Option<T>, doc says required—contradiction"
```

**Scope**: ~800 LOC
- Markdown extractor
- OpenAPI extractor
- Cross-source contradiction detector

### Phase 3: Relationship Inference

**Goal**: Automatically infer edges between nodes

```bash
./spec infer-relationships --use-ai

# Uses AI embeddings to find semantic similarity
# Auto-creates Refines, DerivesFrom, Contradicts edges
```

**Scope**: ~400 LOC
- Semantic similarity via AI (use existing claude/codex integration)
- Heuristics for relationship types
- Confidence scoring

### Phase 4: Specification Synthesis

**Goal**: Generate unified specifications from fragments

```bash
./spec synthesize "password requirements"

# Output:
# Unified Specification: Password Requirements
# - Minimum length: 8 characters (consensus from 5 sources)
# - Maximum length: 128 characters (from database schema only—WARNING: not tested)
# - Must include special character (contradiction: tests require, OpenAPI doesn't)
```

**Scope**: ~600 LOC
- Fragment collection and grouping
- Consensus detection
- Natural language synthesis (via AI)

## This Is the Breakthrough

### Why This Addresses conversation.md Critique

1. **"DSL is impossible for humans to manage"**
   → Humans don't manage DSL directly; tool infers it from natural artifacts

2. **"Can't express everything without infinite types"**
   → Don't need to; tool works with what exists in code/docs/tests

3. **"No ruler to measure correctness"**
   → Ruler emerges from cross-source consensus and contradiction detection

4. **"Multi-layered specifications can't be unified"**
   → They can't be *perfectly* unified, but tool makes inconsistencies *visible*

### Why This Is "New Era"

**Past tools**: Assume specifications are primary artifacts (write specs, generate code)
**Reality**: Code, tests, docs, schemas exist first; specifications are implicit

**New paradigm**: **Specification archaeology**
- Dig up implicit specifications from existing artifacts
- Surface contradictions that always existed but were invisible
- Make the hidden specification graph explicit

This inverts the traditional specification-first approach:
- Don't force developers to write formal specs
- Extract specifications from what developers already write
- Focus human effort on resolving contradictions, not creating from scratch

## Conclusion: The Path Forward

### Immediate Next Step

Implement **MVP single-source extraction**:

```rust
// In spec-core/src/extract.rs
pub mod extract;
pub use extract::{RustExtractor, InferredSpecification, IngestionReport};
```

Test with spec-oracle itself:
1. Run extractor on spec-oracle's source code
2. Auto-populate graph with inferred specifications
3. Compare with manually created specifications
4. Measure accuracy and usefulness

### Success Criteria

The extraction approach succeeds if:
1. **90%+ precision**: Inferred specifications are actually valid
2. **70%+ recall**: Most important specifications are captured
3. **Contradiction detection**: Finds real inconsistencies between sources
4. **Time saving**: Faster than manual graph construction

### This IS the "New Software Engineering"

Not by solving Gödel's theorem, but by:
- **Accepting** that specifications are fragmented across sources
- **Extracting** implicit specifications automatically
- **Detecting** contradictions through cross-source validation
- **Synthesizing** unified views from fragments

This is **emergence**: A new capability (unified specification understanding) emerges from combining existing artifacts in a novel way.
