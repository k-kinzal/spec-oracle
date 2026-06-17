# specORACLE Architecture

## Overview

specORACLE is a reverse mapping engine that constructs U0 (root specification) from diverse artifacts through inverse mappings:

```
Code, Tests, Docs, Proto, Contracts, Types, TLA+ → [f₀ᵢ⁻¹] → U0
```

The system consists of three main components:

1. **specd** - Core engine (daemon)
2. **spec-cli** - Command-line interface
3. **spec-core** - Shared libraries

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                        spec-cli                             │
│  (Natural Language Interface - Pure gRPC Client)             │
└─────────────────┬──────────────────────────────────────────┘
                  │ gRPC (UDA/f operations)
                  ▼
┌─────────────────────────────────────────────────────────────┐
│                         specd                               │
│               (UDA/f Core Engine - Daemon)                  │
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │          ProjectManager (Multi-project support)       │  │
│  │  • Create/Load/Save/Delete projects                   │  │
│  │  • Switch current project                             │  │
│  │  • Project discovery                                  │  │
│  └───────┬────────────────────────────────────────────────┘  │
│          │                                                   │
│          ▼                                                   │
│  ┌───────────────────────────────────────────────────────┐  │
│  │                    Project                            │  │
│  │  ┌──────────────────────┐  ┌────────────────────────┐ │  │
│  │  │   UDAFModel          │  │  SpecRepository        │ │  │
│  │  │  (Formal Layer)      │  │  (Data Layer)          │ │  │
│  │  │  • Universes         │  │  • Nodes (specs)       │ │  │
│  │  │  • Domains           │  │  • Edges (relations)   │ │  │
│  │  │  • AdmissibleSets    │  │  • Graph operations    │ │  │
│  │  │  • Transforms        │  │  • Queries             │ │  │
│  │  └──────────────────────┘  └────────────────────────┘ │  │
│  └───────┬────────────────────────────────────────────────┘  │
│          │                                                   │
│          ▼                                                   │
│  ┌───────────────────────────────────────────────────────┐  │
│  │          StorageBackend (Pluggable)                   │  │
│  │  • LocalFile (default - DirectoryStore format)        │  │
│  │  • Database (future)                                  │  │
│  │  • S3 (future)                                        │  │
│  │  • Git (future)                                       │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────┬───────────────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────────────┐
│                    Local Filesystem                         │
│  ~/.specd/projects/                                         │
│  ├── default/                                               │
│  │   ├── config.ini                                        │
│  │   ├── udaf-model.json                                   │
│  │   ├── nodes/                                            │
│  │   │   ├── <uuid1>.yaml                                  │
│  │   │   └── <uuid2>.yaml                                  │
│  │   └── edges.yaml                                        │
│  └── my-project/                                            │
│      ├── config.ini                                        │
│      ├── udaf-model.json                                   │
│      ├── nodes/                                            │
│      └── edges.yaml                                        │
└─────────────────────────────────────────────────────────────┘
```

## Component Details

### specd (Core Engine)

**Role**: Authoritative UDA/f model manager, similar to dockerd in the docker ecosystem.

**Responsibilities**:
- Manage multiple projects (namespaces)
- Maintain UDA/f model (Universe, Domain, AdmissibleSet, Transform)
- Execute reverse mappings (construct U0 from artifacts)
- Provide gRPC API for all operations
- Persist data through pluggable storage backends

**Key Modules**:
- `main.rs` - Server startup and initialization
- `service.rs` - gRPC service implementation (973 lines)
- `udaf_service.rs` - UDA/f-specific RPC operations (~600 lines, 20 RPCs)
- `project.rs` - Project/namespace management (480 lines)
- `storage/` - Pluggable storage abstraction
  - `mod.rs` - StorageBackend trait (95 lines)
  - `local_file.rs` - LocalFile implementation (215 lines)
- `config.rs` - Configuration management (340 lines)
- `migration.rs` - Legacy .spec/ import (200 lines)

**gRPC Services** (proto/spec_oracle.proto):
1. **Project Management RPCs**: CreateProject, ListProjects, SwitchProject, DeleteProject, GetCurrentProject, ImportProject
2. **Node/Edge RPCs**: AddNode, GetNode, ListNodes, RemoveNode, AddEdge, etc.
3. **UDA/f Model RPCs** (20 operations):
   - Universe operations: CreateUniverse, GetUniverse, ListUniverses, DeleteUniverse
   - Domain operations: CreateDomain, GetDomain, ListDomains, UpdateDomainConstraints
   - AdmissibleSet operations: CreateAdmissibleSet, GetAdmissibleSet, ListAdmissibleSets, VerifyConsistency, VerifyImplication
   - Transform operations: CreateTransform, GetTransform, ListTransforms, VerifyTransformSoundness
   - Projection operations: ConstructU0, SyncModel
   - Verification operations: ValidateModel

### spec-cli (Command-Line Interface)

**Role**: Pure intermediary translating user intent to specd operations. Always communicates via gRPC.

**Characteristics**:
- No standalone mode (removed in Phase 3)
- No direct file access
- All operations go through specd

**Commands**:
```bash
# Project management
spec project create <name> --description "..."
spec project list
spec project use <name>
spec project delete <name>
spec project import --name <name> --path /path/to/.spec

# Node operations (operate on current project)
spec add "specification text"
spec query ...
spec summary

# UDA/f operations
spec universe create --layer 1 --name "TLA+" --description "..."
spec domain create ...
spec extract ./src  # Reverse mapping: code → U0
spec verify consistency ...
```

### spec-core (Shared Libraries)

**Role**: Core data structures and business logic shared between specd and spec-cli.

**Key Modules**:
- `data/` - SpecRepository, Node/Edge graph operations
  - `repository.rs` - Graph-based specification repository
  - `node.rs` - Node types (Assertion, Axiom, Invariant, etc.)
  - `query.rs` - Query types (Contradiction, Omission, etc.)
- `formal/` - UDA/f model implementation
  - `model/model.rs` - UDAFModel core
  - `universe.rs` - Universe types (U0, U1, U2, U3, ...)
  - `domain.rs` - Domain and boundary constraints
  - `admissible_set.rs` - Admissible sets and consistency
  - `transform/transform.rs` - Transform functions (f: U_i → U_j)
  - `transform/projection.rs` - Reverse mapping (Observer >> Extractor pattern)
- `store/` - Low-level persistence (DirectoryStore, FileStore)

## Data Flow

### 1. Project Creation
```
User: spec project create my-app --description "My application"
  ↓
spec-cli: CreateProjectRequest → specd (gRPC)
  ↓
specd: ProjectManager.create_project(...)
  ↓
Project { name, description, udaf_model: UDAFModel::new(), repository: SpecRepository::new() }
  ↓
StorageBackend.save_udaf_model(...) + save_repository(...)
  ↓
Filesystem: ~/.specd/projects/my-app/ created
```

### 2. Adding Specification
```
User: spec add "User can login with email and password"
  ↓
spec-cli: AddNodeRequest → specd (gRPC)
  ↓
specd: Load current project → Add node to repository → Save project
  ↓
Filesystem: New YAML file in ~/.specd/projects/my-app/nodes/
```

### 3. Reverse Mapping (Construct U0)
```
User: spec extract ./src
  ↓
spec-cli: ConstructU0Request (root_space: ArtifactBundle) → specd
  ↓
specd: ProjectManager.load_project(current)
  ↓
UDAFModel.construct_u0(root_space, repository)
  ↓
For each artifact:
  1. Detect universe (U3: Rust code, U2: gRPC proto, etc.)
  2. Apply projection (Observer >> Extractor)
  3. Extract inferred specifications
  4. Add to U0
  ↓
Save updated project
  ↓
Response: List of inferred specifications with confidence scores
```

## Theoretical Foundation: UDA/f Model

The UDA/f model provides the theoretical basis for specORACLE:

- **U (Universe)**: Specification space at a formality level (U0=natural language, U1=formal specs, U2=interfaces, U3=implementation)
- **D (Domain)**: Region a spec covers (constraints on input/state/output)
- **A (Admissible Set)**: Valid implementations satisfying a spec
- **f (Transform)**: Mappings between universes (forward refinement or inverse projection)

**Key Insight**: specORACLE operates primarily through **inverse transforms** (f⁻¹), constructing U0 from concrete artifacts in higher universes.

## Storage Format

### Project Directory Structure (LocalFile backend)
```
~/.specd/projects/<project-name>/
├── config.ini              # Project configuration
├── udaf-model.json         # UDAFModel (serialized)
├── nodes/                  # Specifications (DirectoryStore format)
│   ├── <uuid1>.yaml
│   ├── <uuid2>.yaml
│   └── ...
└── edges.yaml              # Relationships between specs
```

### UDAFModel Format (udaf-model.json)
```json
{
  "universes": {
    "u0": { "layer": 0, "name": "U0", "description": "Root specifications" },
    "u1": { "layer": 1, "name": "TLA+", "description": "Formal specifications" }
  },
  "domains": [...],
  "admissible_sets": {...},
  "transforms": [...],
  "metadata": {}
}
```

### Node Format (nodes/<uuid>.yaml)
```yaml
id: "550e8400-e29b-41d4-a716-446655440000"
content: "User can login with email and password"
kind: Assertion
created_at: 1708000000
updated_at: 1708000000
metadata:
  formality_layer: "0"
  source: "manual"
```

### Edges Format (edges.yaml)
```yaml
- source: "550e8400-e29b-41d4-a716-446655440000"
  target: "550e8400-e29b-41d4-a716-446655440001"
  kind: Implication
  metadata: {}
```

## Concurrency Model

### Thread Safety
- **ProjectManager**: `Arc<Mutex<ProjectManager>>` - exclusive access for mutations
- **StorageBackend**: `Send + Sync` trait - can be safely shared across threads
- **Project**: Loaded on-demand, modified, saved atomically

### Lock Ordering (to prevent deadlocks)
1. ProjectManager lock (top-level)
2. Project-specific locks (if any)
3. Storage backend locks (if any)

## Error Handling Philosophy

### Structured Errors
- All public APIs return `Result<T, E>`
- No `unwrap()` in library code
- Errors propagated with context using `anyhow::Context`

### gRPC Status Mapping
- `NOT_FOUND` - Missing project/node
- `ALREADY_EXISTS` - Duplicate project
- `INVALID_ARGUMENT` - Bad request
- `UNAVAILABLE` - Storage backend failure
- `INTERNAL` - Unexpected errors (sanitized messages)

## Testing Strategy

### Unit Tests (in-module `#[cfg(test)]`)
- **config.rs**: 5 tests - Configuration loading, saving, defaults
- **project.rs**: 10 tests - Project creation, loading, switching, deletion
- **storage/local_file.rs**: 7 tests - Storage operations, edge cases
- **migration.rs**: 3 tests - Legacy import, detection

### Test Coverage
```
Total: 22 tests
Status: ✅ All passing (0 failures)
```

### Integration Testing
Integration tests require a running specd instance. For now, we rely on:
1. Unit tests for component isolation
2. Manual end-to-end testing with real specd + spec-cli

## Performance Characteristics

### Complexity
- **Project switching**: O(1) - pointer update, no I/O
- **List projects**: O(n) - acceptable up to ~1000 projects
- **Add node**: O(1) - append to graph
- **construct_u0**: O(m) - parallelizable with rayon (m = artifact count)

### Scalability
- Projects: Designed for 10-1000 projects per installation
- Nodes per project: Up to 100,000 nodes (petgraph)
- Edges per project: Up to 500,000 edges

## Quality Metrics

### Code Organization
- Clear separation of concerns: config → storage → project → service
- UDAFModel (formal layer) and SpecRepository (data layer) cleanly separated
- No circular dependencies

### Type Safety
- Newtype pattern for identifiers (ProjectId, UniverseId, etc.) - future enhancement
- Enum exhaustiveness checked by compiler
- No raw string IDs in critical paths (except proto compatibility)

### Documentation
- ✅ All public items have doc comments
- ✅ Architecture documented (this file)
- ✅ Theoretical foundation documented (docs/conversation.md)
- ✅ Motivation documented (docs/motivation.md)

## Migration from Legacy .spec/ Directories

### Import Process
1. Detect storage format (DirectoryStore vs FileStore)
2. Load SpecRepository from .spec/
3. Synthesize UDAFModel from repository metadata
4. Create new project with both UDAFModel and SpecRepository
5. Save to specd storage

### Command
```bash
spec project import --name my-app --path /path/to/project/.spec
```

### Safety Guarantees
- Original .spec/ directory is **never modified or deleted**
- Import is read-only operation
- User can verify before deleting old .spec/

## Future Enhancements

### Phase 2.2: Full UDA/f Implementation (Deferred)
- Complete implementation of all 20 UDA/f RPCs
- Z3-backed formal verification
- Projection execution (Observer >> Extractor)

### Storage Backends
- Database backend (PostgreSQL with schema support)
- S3 backend (remote storage)
- Git backend (version control integration)

### Advanced Features
- LLM/AI Agent integration for natural language formalization
- Distributed verification (parallel Z3 proof checking)
- Real-time collaboration (multi-client sync)

## References

- **Theoretical Foundation**: [docs/conversation.md](./conversation.md) - UDA/f model derivation
- **Motivation**: [docs/motivation.md](./motivation.md) - Why specORACLE exists
- **Completion Report**: [PHASES_1-4_COMPLETE.md](../PHASES_1-4_COMPLETE.md) - Implementation summary
- **Plan**: [~/.claude/plans/floating-churning-porcupine.md](#) - Original reorganization plan
