# Specification Oracle

A next-generation specification description tool with strict graph-based specification management, contradiction detection, and AI-enhanced natural language querying.

## Architecture

- **specd**: Server daemon managing the specification graph via gRPC
- **spec**: Command-line client for interacting with specifications
- **spec-core**: Core library with graph data structures and analysis

## Features

- Graph-based specification storage (nodes: assertions, constraints, scenarios, definitions, domains)
- Relationship tracking (refines, depends_on, contradicts, derives_from, synonym, composes)
- Contradiction detection (explicit and structural)
- Omission detection (isolated nodes, incomplete domains, unsupported scenarios)
- Natural language querying via AI integration (claude, codex)
- Terminology resolution and synonym management
- File-based persistence (JSON)
- Comprehensive test coverage

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
- `resolve-term <term>` - Find definitions and synonyms

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

All 14 tests verify:
- Node and edge CRUD operations
- Contradiction detection
- Omission detection
- Search and terminology resolution
- Serialization and persistence

## License

See LICENSE file.
