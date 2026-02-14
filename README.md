# Specification Oracle

A next-generation specification description tool with strict graph-based specification management, contradiction detection, and AI-enhanced natural language querying.

## Architecture

- **specd**: Server daemon managing the specification graph via gRPC
- **spec**: Command-line client for interacting with specifications
- **spec-core**: Core library with graph data structures and analysis

## Features

- Graph-based specification storage (nodes: assertions, constraints, scenarios, definitions, domains)
- Relationship tracking (refines, depends_on, contradicts, derives_from, synonym, composes, formalizes, transform)
- Contradiction detection (explicit, structural, and inter-universe)
- Omission detection (isolated nodes, incomplete domains, unsupported scenarios)
- Inter-universe consistency checking (multi-layered specification validation)
- Automatic specification extraction from code (Rust)
- **Continuous synchronization via watch mode** (monitors code changes, maintains spec integrity)
- **AI-powered semantic normalization** (understands cross-layer specification equivalence)
- Natural language querying via AI integration (claude, codex)
- Terminology resolution and synonym management
- Temporal queries and compliance tracking
- File-based persistence (JSON)
- Comprehensive test coverage (55 tests)

## Quick Start

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

## Example: Managing Large Specification Sets

```bash
# Extract specifications from entire codebase
cargo run --bin spec -- extract spec-core

# Automatically infer relationships (handles hundreds of specs)
cargo run --bin spec -- infer-relationships

# Detect omissions (isolated specs)
cargo run --bin spec -- detect-omissions

# Detect contradictions
cargo run --bin spec -- detect-contradictions
```

**Practical demonstration**: Successfully manages 345+ specifications with automatic relationship inference generating 354 suggestions for human review.

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

### Node Operations
- `add-node <content> [--kind <type>]` - Create specification node
- `get-node <id>` - Retrieve node details
- `list-nodes [--kind <type>]` - List nodes with optional filtering
- `remove-node <id>` - Delete node

### Edge Operations
- `add-edge <source> <target> [--kind <type>]` - Create relationship
- `list-edges [--node <id>]` - List relationships
- `remove-edge <id>` - Delete relationship

### Analysis
- `query <text> [--ai]` - Search specifications
- `detect-contradictions` - Find conflicting specifications
- `detect-omissions` - Find incomplete specifications
- `detect-inter-universe-inconsistencies` - Find cross-layer contradictions
- `resolve-term <term>` - Find definitions and synonyms
- `set-universe <id> <universe>` - Set universe metadata for multi-layer specs
- `infer-relationships` - Automatically infer relationships for all nodes
- `infer-relationships-ai [--min-confidence <0.0-1.0>]` - **NEW**: AI-powered semantic matching across formality layers

### Continuous Synchronization
- `watch <source> [--language <lang>] [--min-confidence <0.0-1.0>]` - Monitor code changes and maintain specification integrity in real-time

### AI Integration
- `ask <question> [--ai-cmd <claude|codex>]` - Natural language Q&A
- **Semantic Normalization** - AI understands that specifications at different formality layers describe the same requirement

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

All 53 tests verify:
- Node and edge CRUD operations
- Contradiction detection (explicit, structural, inter-universe)
- Omission detection
- Multi-layer specification consistency
- Automatic specification extraction
- Temporal queries and compliance tracking
- Search and terminology resolution
- Serialization and persistence

## License

See LICENSE file.
