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
- Natural language querying via AI integration (claude, codex)
- Terminology resolution and synonym management
- Temporal queries and compliance tracking
- File-based persistence (JSON)
- Comprehensive test coverage (53 tests)

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

### AI Integration
- `ask <question> [--ai-cmd <claude|codex>]` - Natural language Q&A

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
