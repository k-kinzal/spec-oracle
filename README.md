# specORACLE

**A reverse mapping engine for multi-layered specification management.**

specORACLE is not a traditional specification tool. It constructs the root specification (U0) from diverse artifacts through reverse mappings:

```
Code, Tests, Docs, Proto, Contracts, Types → [f₀ᵢ⁻¹] → U0
```

U0 serves as the baseline for governing multi-layered defenses. Humans express intent. The system infers everything else.

**Status**: Core concept realized. 234 specifications managed (26.1% auto-extracted), zero contradictions, zero omissions, complete graph connectivity. Self-governance demonstrated.

## Documentation

**New to specORACLE?** Start here:
- **[Concepts Guide](docs/concepts.md)** - Understand formality layers (U0-U3), reverse mapping, and the U/D/A/f model
- **[Motivation](docs/motivation.md)** - Why specORACLE is needed (multi-layer defense coordination)
- **[Theoretical Foundation](docs/conversation.md)** - Deep dive into specification theory

## Architecture

- **specd**: Server daemon managing the specification graph via gRPC
- **spec**: Command-line client for interacting with specifications
- **spec-core**: Core library with graph data structures, Z3 formal verification, and reverse mapping engine

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

### Option 1: Project-Local Specifications (Recommended - Zero Configuration)

Initialize specification management in your project:
```bash
cd your-project
spec init
```

This creates a `.spec/` directory with specifications storage.

**That's it! No server needed.**

Use specifications immediately (standalone mode - auto-detected):
```bash
# Add specifications with auto-inference
spec add "Password must be at least 8 characters"

# Get overview
spec summary

# Check for issues (runs both contradiction & omission detection)
spec check

# Search specifications
spec find "password"

# See relationships
spec trace <spec-id>
```

Commit to Git:
```bash
git add .spec/
git commit -m "Add authentication specifications"
```

Team members (zero configuration):
```bash
git clone your-repo
spec add "New specification"  # Just works! Auto-detects .spec/
spec list-nodes               # No server setup needed
```

**How it works**: The CLI automatically detects `.spec/` directory and runs in standalone mode (direct file access, no server required). For advanced features (AI inference, watch mode), server mode is available.

### Option 2: Global Specifications (Quick Testing)

Build the project:
```bash
cargo build --release
```

Start the server:
```bash
cargo run --bin specd
# Or: ./target/release/specd
```

Use the CLI (in another terminal):
```bash
# Add a domain
cargo run --bin spec -- add-node "Authentication" --kind domain

# Add a constraint
cargo run --bin spec -- add-node "Passwords must be >= 8 chars" --kind constraint

# Create relationship
cargo run --bin spec -- add-edge <constraint-id> <domain-id> --kind refines

# List all specifications
cargo run --bin spec -- list-nodes

# Detect issues
cargo run --bin spec -- detect-contradictions
cargo run --bin spec -- detect-omissions

# Query with AI (requires claude CLI)
cargo run --bin spec -- ask "What are the authentication requirements?"
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

```bash
cargo test
```

All 73 tests verify:
- Node and edge CRUD operations
- Contradiction detection (Z3-verified formal proofs + heuristics)
- Omission detection (isolated nodes, incomplete coverage)
- Multi-layer specification consistency (U0-U3)
- Automatic specification extraction (Rust, PHP, protobuf)
- Reverse mapping engine (f₀ᵢ⁻¹: code→specs)
- Idempotent extraction (べき等性)
- AI-powered relationship inference
- Search and terminology resolution
- Serialization and persistence (file-based & directory-based storage)

## License

See LICENSE file.
