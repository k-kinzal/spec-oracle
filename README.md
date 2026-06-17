# specORACLE: Reverse Mapping Engine

**Constructs U0 (root specification) from diverse artifacts through reverse mappings.**

specORACLE is not a traditional specification tool. It is a **reverse mapping engine** that constructs the foundational specification (U0) from multiple sources:

```
Code, Tests, Docs, Proto, Contracts, Types, TLA+ → [f₀ᵢ⁻¹] → U0
```

U0 serves as the baseline for governing multi-layered defenses. Humans express intent. The system infers everything else.

**Status**: Production-ready architecture. Multi-project support, UDA/f model management, gRPC-based core engine, comprehensive testing.

## Documentation

**New to specORACLE?** Start here:
- **[Concepts Guide](docs/concepts.md)** - Understand formality layers (U0-U3), reverse mapping, and the U/D/A/f model
- **[Motivation](docs/motivation.md)** - Why specORACLE is needed (multi-layer defense coordination)
- **[Theoretical Foundation](docs/conversation.md)** - Deep dive into specification theory (U, D, A, f model)

## Architecture

### Core Components

**specd** (Core Engine):
- Manages UDA/f model (Universe, Domain, AdmissibleSet, Transform)
- Project/namespace management (multi-project support)
- Reverse mapping engine (construct U0 from artifacts)
- Formal verification layer operations
- Storage abstraction (LocalFile, Database, S3, Git - pluggable)
- gRPC server for all operations

**spec-cli** (Natural Language Interface):
- Pure gRPC client translating user intent to specd operations
- High-level commands (`add`, `check`, `find`, `trace`)
- Low-level RPC operations (`spec rpc <operation>`)
- Future: LLM/AI Agent integration for natural language formalization

**spec-core** (Shared Library):
- UDA/f model data structures
- Specification graph (nodes, edges, relationships)
- Formal verification primitives
- Storage backends (file, directory, future: database)
- Projection and transform logic

## UDA/f Model

Based on the theoretical foundation in `docs/conversation.md`:

- **U (Universe)**: Specification space at a formality level (U0=root, U1=formal, U2=interface, U3=implementation)
- **D (Domain)**: Region a spec covers (boundaries, constraints)
- **A (Admissible Set)**: Valid implementations satisfying a spec (constraints defining membership)
- **f (Transform)**: Mappings between universes (forward, inverse, parallel)

### Reverse Mapping

The core innovation of specORACLE is **reverse mapping** (f₀ᵢ⁻¹):

```
f₀₃⁻¹: U3 (Code) → U0 (Root Spec)
f₀₂⁻¹: U2 (Proto) → U0 (Root Spec)
f₀₁⁻¹: U1 (TLA+) → U0 (Root Spec)

U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3) ∪ ...
```

**Traditional tools**: Humans write specs → Generate code (forward mapping)
**specORACLE**: Code/artifacts exist → Construct root spec (reverse mapping)

This allows specORACLE to manage specifications for existing codebases and continuously synchronize them with reality.

## Core Features

### Reverse Mapping Engine
- **Automatic extraction** from code (Rust, PHP), protobuf, tests, and documentation
- **Multi-layer support**: U0 (requirements), U1 (formal specs), U2 (interfaces), U3 (implementation)
- **Reverse mappings**: f₀₃⁻¹ (code→specs), f₀₂⁻¹ (proto→specs), constructs U0 automatically
- **Idempotent extraction**: Running extraction multiple times produces the same result

### Formal Verification
- **Z3 SMT solver integration** for mathematical proof of specification consistency
- **Constraint extraction** from natural language (pattern-based + AI-powered)
- **Formal contradiction detection** with mathematical certainty (not just heuristics)
- **Property-based verification**: satisfiability, consistency, implication checking

### Self-Governance
- **specORACLE manages its own specifications** using the tool itself
- **Detects its own violations**: CLI architecture issues, separation of concerns
- **Demonstrates the essence**: The system that should govern multi-layer defenses actually governs itself

### Storage & Distribution
- **Directory-based storage**: Each specification is a separate YAML file (merge-friendly)
- **Project-local management**: `.spec/` directory, Git-integrated, CI/CD-ready
- **Standalone mode**: Zero configuration, no server required for basic operations
- **Auto-detection**: CLI automatically detects `.spec/` and runs in appropriate mode

### Analysis & Verification
- **Contradiction detection**: Z3-verified formal contradictions + heuristic detection
- **Omission detection**: Isolated specifications, incomplete coverage
- **Graph visualization**: DOT export for Graphviz, visual representation of spec relationships
- **Health metrics**: Summary statistics, connectivity analysis, quality indicators

### AI Integration
- **Semantic normalization** across formality layers (understands "at least 8" = ">= 8" = `len() >= 8`)
- **Automatic relationship inference** between specifications
- **Natural language querying** for spec search and understanding
- **Continuous synchronization** via watch mode

### Developer Experience
- **High-level commands**: `add`, `check`, `find`, `trace` - no need to think about nodes/edges
- **Comprehensive testing**: 73 tests covering all core functionality
- **Multi-project support**: Manage specifications for multiple codebases simultaneously

## Quick Start

### 1. Start specd

Build and start the core engine:
```bash
cargo build --release
cargo run --bin specd
# Server starts on [::1]:50051
```

### 2. Create a Project

In another terminal:
```bash
# Create a new project
spec project create my-app --description "My application specifications"

# Switch to the project
spec project use my-app

# List all projects
spec project list
```

### 3. Add Specifications

```bash
# Add specifications (auto-infers kind and relationships)
spec add "User can login with email and password"
spec add "Password must be at least 8 characters"
spec add "Email must be valid format"

# Get overview
spec summary
```

### 4. Work with UDA/f Model

```bash
# Create projection universes
spec rpc create-universe --layer 1 --name "TLA+" --description "Formal specifications"
spec rpc create-universe --layer 2 --name "gRPC" --description "API contracts"
spec rpc create-universe --layer 3 --name "Rust" --description "Implementation code"

# List universes
spec rpc list-universes

# Create domains
spec rpc create-domain --universe U1 --name "Authentication" --description "Auth domain"

# Create transforms
spec rpc create-transform --source U3 --target U0 --kind inverse

# Validate model
spec rpc validate-model
```

### 5. Verify Specifications

```bash
# Check for contradictions and omissions
spec check

# Find specifications
spec find "password"

# Trace relationships
spec trace <spec-id>

# Export graph visualization
spec export-dot --output specs.dot
dot -Tpng specs.dot -o specs.png
```

### Configuration

Server address (default: `[::1]:50051`):
```bash
spec --server http://localhost:50051 <command>
```

Project storage location (default: `~/.specd/projects/`):
```bash
# Configured via ~/.specd/config.ini
```

## Example: Real-World Usage (specORACLE Managing Itself)

**specORACLE uses itself to manage its own specifications** - demonstrating self-governance:

```bash
# Check system health
$ spec check
🔍 Checking specifications...
  ✓ No contradictions found
  ✓ No isolated specifications

📊 Summary:
  Total specs:        253
  Extracted specs:    75 (29.6%)
  Contradictions:     0
  Isolated specs:     0

✅ All checks passed!

# Get overview
$ spec summary
📊 Specification Summary
Total Specifications: 253

By Kind:
  Assertions: 170
  Constraints: 39
  Scenarios: 33
  Definitions: 11

By Formality Layer:
  U0: 131  (Natural Language Requirements)
  U2: 65   (Interface Definitions - gRPC proto)
  U3: 56   (Implementation - extracted from code)
  U1: 1    (Formal Specifications)

Health:
  ✓ No contradictions
  ✓ No isolated specs

# Extract specifications from codebase
$ spec extract spec-core/src/
✅ Ingestion complete:
   Nodes created: 75
   Edges created: 45 (automatic!)

# Visualize the specification graph
$ spec export-dot --output specs.dot
$ dot -Tpng specs.dot -o specs.png
```

**Real achievements**:
- **253 specifications** across 4 formality layers
- **29.6% auto-extracted** from code/proto (reverse mapping engine working)
- **Zero contradictions** (Z3-verified formal proofs)
- **Zero omissions** (complete graph connectivity)
- **Self-governance**: specORACLE detected and reported its own CLI architecture violations

## Example: Continuous Specification Synchronization

```bash
# Watch a directory for changes and maintain spec integrity
cargo run --bin spec -- watch ./src --min-confidence 0.8

# Output:
# 🔍 Watching ./src for changes...
#    Confidence threshold: 0.8
#    Check interval: 2s
#    Press Ctrl+C to stop
#
# 📦 Performing initial extraction...
# ✓ Extracted 127 specifications
#
# 🔬 Running initial verification...
#    ✓ No contradictions
#    ⚠️  23 isolated specification(s)
#
# 📝 Change detected: "auth.rs"
#    Re-extracting specifications...
#    ✓ Updated 127 specifications
#    🔬 Verifying...
#    ✓ No contradictions
#    ⚠️  19 isolated specification(s)
```

**Breakthrough feature**: Specifications automatically stay synchronized with code evolution - no manual intervention required.

## Example: AI-Powered Semantic Normalization

**The Problem**: Specifications exist at multiple formality layers but describe the same requirements:

```rust
// Layer 0 (natural language - doc comment):
/// Password must be at least 8 characters

// Layer 3 (executable code):
assert!(password.len() >= 8, "Password too short");

// Simple keyword matching fails: only "password" overlaps
```

**The Solution**: AI-powered semantic matching

```bash
# Traditional inference (keyword-based)
cargo run --bin spec -- infer-relationships
# Result: These specs stay isolated (no keyword overlap)

# AI-enhanced inference (semantic understanding)
cargo run --bin spec -- infer-relationships-ai --min-confidence 0.7
# Result: Recognizes semantic equivalence, creates "formalizes" edge

# Dramatically reduces omissions by connecting cross-layer specs
```

**How it works**:
1. Uses `claude` CLI to understand semantic equivalence
2. Recognizes that "at least 8" = ">= 8" = `len() >= 8`
3. Creates `formalizes` edges between natural and executable specs
4. Caches results to minimize AI calls

**Impact**: Can reduce 600+ isolated specifications down to ~100-200 by recognizing cross-layer equivalences that simple text matching cannot detect.

**This is the first specification tool to use AI for semantic normalization across formality layers.**

## Commands

### Essential Commands (Start Here)

**Project setup**:
- `spec init` - Initialize `.spec/` directory in your project

**Daily workflow**:
- `spec add "<content>"` - Add specification (auto-infers kind & relationships)
- `spec check` - Run all verification (contradictions + omissions, exits 1 if issues found)
- `spec summary` - Show statistics and health overview
- `spec find "<query>"` - Semantic search across specifications

**Understanding specifications**:
- `spec trace <id>` - Show all relationships for a spec (hierarchical tree, `--depth` to limit)
- `spec export-dot [--output file.dot]` - Generate graph visualization (Graphviz format)

**Extraction (reverse mapping)**:
- `spec extract <file-or-dir>` - Extract specs from code/proto (auto-detects language)
- `spec construct-u0 --execute` - Build U0 from all layers via reverse mappings

### Advanced Commands

**Verification & analysis**:
- `spec detect-contradictions` - Find conflicts (Z3-verified + heuristic)
- `spec detect-omissions` - Find isolated/incomplete specifications
- `spec infer-relationships-ai` - AI-powered relationship inference
  - `--dry-run` - Preview without creating edges
  - `--limit <N>` - Maximum edges to create
  - `--interactive` - Review each edge individually

**Export & documentation**:
- `spec export-dot [--layer <N>] [--metadata] [--output <file>]` - Graph visualization
- `python3 scripts/export_specs_md.py` - Markdown export (layer/kind filtering)

**Low-level operations** (use `spec api <command>` for direct graph access):
- `spec api add-node`, `spec api get-node`, `spec api list-nodes`
- `spec api add-edge`, `spec api list-edges`
- Most users don't need these - high-level commands are recommended

### AI Integration

- `spec ask "<question>"` - Natural language Q&A about specifications
- `spec infer-relationships-ai` - Semantic matching across formality layers
  - Understands "at least 8" = ">= 8" = `len() >= 8`
  - Creates cross-layer `formalizes` edges automatically

### Continuous Synchronization

- `spec watch <source> [--min-confidence <0.8>]` - Monitor code changes, auto-extract specs
- Real-time verification as code evolves

## Node Kinds

- **assertion**: Concrete claim about behavior
- **constraint**: Universal invariant
- **scenario**: Existential requirement (required path)
- **definition**: Term definition
- **domain**: Domain boundary declaration

## Edge Kinds

- **refines**: Target refines source (more specific)
- **depends_on**: Source depends on target
- **contradicts**: Source contradicts target
- **derives_from**: Source derived from target
- **synonym**: Terms are synonymous
- **composes**: Source composes with target
- **formalizes**: Target is more formal version of source
- **transform**: Maps specification from source universe to target universe (f function)

## Configuration

Server storage location (default: `~/spec-oracle/specs.json`):
```bash
export SPECD_STORE_PATH=/custom/path/specs.json
```

Server address (default: `[::1]:50051`):
```bash
cargo run --bin spec -- --server http://localhost:50051 <command>
```

## Testing

### Unit Tests
```bash
# All packages
cargo test

# Specific package
cargo test --package spec-core
cargo test --package specd
cargo test --package spec-cli
```

### Integration Tests

**Prerequisites**: specd must be running on [::1]:50051

```bash
# Start specd in one terminal
cargo run --bin specd

# Run integration tests in another terminal
cd specd
cargo test --test integration_test
```

Integration tests verify:
- Project lifecycle (create, use, delete, isolation)
- Universe operations (create, get, list, delete)
- Domain operations (create, get, list)
- Transform operations (create, get, list)
- Model synchronization and validation
- Multi-project isolation

### Coverage

Tests verify:
- **Project Management**: Creation, switching, deletion, isolation
- **UDA/f Model Operations**: Universe, Domain, AdmissibleSet, Transform
- **Graph Operations**: Node and edge CRUD operations
- **Contradiction Detection**: Z3-verified formal proofs + heuristics
- **Omission Detection**: Isolated nodes, incomplete coverage
- **Multi-layer Consistency**: U0-U3 specification alignment
- **Reverse Mapping**: f₀ᵢ⁻¹ code→specs extraction
- **Storage**: File-based, directory-based, pluggable backends
- **Concurrency**: Multi-client, concurrent operations

## License

See LICENSE file.
