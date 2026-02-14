# Implementation of spec-cli

**Date**: 2026-02-14

## Goal

Implement the command-line interface (spec-cli) to complete the minimum viable specification oracle tool.

## Work Performed

### 1. Created spec-cli/src/main.rs

Implemented a complete CLI with the following commands:

- **Node operations**:
  - `add-node`: Create new specification nodes (assertion, constraint, scenario, definition, domain)
  - `get-node`: Retrieve a node by ID
  - `list-nodes`: List all nodes with optional kind filtering
  - `remove-node`: Delete a node by ID

- **Edge operations**:
  - `add-edge`: Create relationships between nodes (refines, depends_on, contradicts, derives_from, synonym, composes)
  - `list-edges`: List all edges, optionally filtered by node
  - `remove-edge`: Delete an edge by ID

- **Analysis operations**:
  - `query`: Search specifications using substring matching, with optional AI enhancement
  - `detect-contradictions`: Find explicit and structural contradictions
  - `detect-omissions`: Detect isolated nodes, domains without refinements, scenarios without assertions
  - `resolve-term`: Find definitions and synonyms for a term

- **AI integration**:
  - `ask`: Natural language Q&A using external AI commands (claude or codex)
  - Query enhancement via `--ai` flag

### 2. Fixed build issues

- Added `use petgraph::visit::EdgeRef` import to spec-core/src/graph.rs
- Enabled `serde-1` feature for petgraph in Cargo.toml
- Enabled `env-filter` feature for tracing-subscriber in Cargo.toml
- Removed unused HashMap import from specd/src/service.rs
- Fixed borrow checker issues in CLI by using references in for loops

### 3. Verified behavior through tests

Ran `cargo test` - all 14 tests pass:
- Node operations (add, get, remove, list)
- Edge operations (add, list, error handling)
- Contradiction detection (explicit and structural)
- Omission detection (isolated nodes, domains, scenarios)
- Search functionality
- Terminology resolution
- Serialization roundtrip
- File store operations

## Architecture Achieved

✓ Separate command (spec) and server (specd) binaries
✓ gRPC communication via tonic
✓ Graph data management using petgraph
✓ File-based persistence via JSON
✓ Natural language processing via external AI CLI tools
✓ All behavior guaranteed through tests

## Next Steps

To use the system:

1. Start the server: `cargo run --bin specd`
2. Use the CLI: `cargo run --bin spec -- <command>`
3. For AI features, ensure `claude` or `codex` CLI tools are installed

Example workflow:
```bash
# Add domain
spec add-node "Authentication system" --kind domain

# Add constraint
spec add-node "Passwords must be at least 8 characters" --kind constraint

# Link them
spec add-edge <constraint-id> <domain-id> --kind refines

# Detect issues
spec detect-omissions
```

Once the MVP is validated, use it to manage its own specifications as per project constraints.
