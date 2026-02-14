# Project Separation Design

**Date**: 2026-02-14
**Status**: Design in progress
**Issue**: No project/namespace concept - all specs mixed in one global graph

## Problem Statement

From continuing-goal.md:
> **Problem**: spec-oracle's specifications and demo/example specifications are mixed in one global graph. No namespace or project concept exists.

### Current Data Model
```rust
pub struct SpecNodeData {
    pub id: String,
    pub content: String,
    pub kind: NodeKind,
    pub metadata: HashMap<String, String>,  // Generic metadata only
    pub created_at: i64,
    pub modified_at: i64,
    pub formality_layer: u8,
}
```

**Missing**:
- No `project_id` or `namespace` field
- No way to filter specs by project
- No separate storage per project
- No project switching mechanism

## Requirements

### Real-world Use Case
Users managing multiple projects need:
1. **Separate specification graphs per project**
2. **Ability to switch between projects**
3. **Project-scoped extraction** (`spec extract --project myapp`)
4. **Project-scoped queries** (`spec query --project myapp "auth"`)
5. **Optional cross-project relationship inference**

### Minimum Requirements from CLAUDE.md
The requirements don't explicitly mandate project separation, but real-world usage requires it.

## Design Options

### Option A: Separate Graph Files
Each project has its own file: `~/.spec-oracle/projects/{project-name}/specs.json`

**Pros**:
- Simple implementation
- Natural isolation
- Easy backup/versioning
- Aligns with "multiple projects" mental model

**Cons**:
- Cannot query across projects easily
- Duplicate storage if specs shared
- Server must load/unload projects

**Implementation**:
```
~/.spec-oracle/
├── projects/
│   ├── spec-oracle/
│   │   └── specs.json
│   ├── my-webapp/
│   │   └── specs.json
│   └── demo-examples/
│       └── specs.json
└── config.json (current project, settings)
```

### Option B: Single Graph with Project Metadata
Add `project` field to node metadata, filter at query time.

**Pros**:
- Single storage file
- Easy cross-project queries
- No project loading/switching needed

**Cons**:
- Metadata pollution
- No true isolation
- Large file for many projects
- Edges between projects possible (unintended)

**Implementation**:
```rust
// Add to metadata:
metadata.insert("project", "spec-oracle".to_string());

// Filter at query time:
nodes.iter().filter(|n| n.metadata.get("project") == Some(&current_project))
```

### Option C: Separate Databases per Project
Use actual database (SQLite, etc.) with separate instances.

**Pros**:
- True isolation
- Scalable to large projects
- ACID guarantees

**Cons**:
- Overkill for current needs
- Contradicts "file-based persistence" requirement
- More complex implementation

## Recommended Approach: Option A (Separate Graph Files)

### Rationale
1. **Simplicity**: Easiest to implement and understand
2. **Isolation**: True separation, no cross-contamination
3. **Versioning**: Each project can be git-tracked independently
4. **Aligns with usage**: Users think in terms of "projects"
5. **Minimal changes**: Reuses existing `FileStore` infrastructure

### Implementation Plan

#### 1. File Structure
```
~/.spec-oracle/
├── config.json          # Global config (current project, etc.)
└── projects/
    ├── spec-oracle/
    │   └── specs.json   # spec-oracle's own specifications
    ├── demo-examples/
    │   └── specs.json   # Demo/example specifications
    └── my-webapp/
        └── specs.json   # User's webapp specifications
```

#### 2. Configuration File
`~/.spec-oracle/config.json`:
```json
{
  "current_project": "spec-oracle",
  "projects": {
    "spec-oracle": {
      "path": "/Users/ab/Projects/spec-oracle",
      "description": "spec-oracle tool itself"
    },
    "demo-examples": {
      "path": "/Users/ab/Projects/spec-oracle/examples",
      "description": "Demonstration examples"
    }
  }
}
```

#### 3. API Changes

**Server (specd)**:
```rust
// Server maintains current project context
struct ServerState {
    current_project: String,
    graphs: HashMap<String, SpecGraph>,  // Lazy-loaded
}

// Load project on demand
fn load_project(&mut self, project: &str) -> Result<&SpecGraph> {
    if !self.graphs.contains_key(project) {
        let path = self.get_project_path(project)?;
        let graph = FileStore::load(&path)?;
        self.graphs.insert(project.to_string(), graph);
    }
    Ok(&self.graphs[project])
}
```

**gRPC API** - Add optional `project` field:
```protobuf
message AddNodeRequest {
  string project = 10;      // Optional: defaults to current project
  string content = 1;
  SpecNodeKind kind = 2;
  ...
}

message ListNodesRequest {
  string project = 10;      // Optional: defaults to current project
  SpecNodeKind kind_filter = 1;
}

// New RPCs
rpc CreateProject(CreateProjectRequest) returns (CreateProjectResponse);
rpc SwitchProject(SwitchProjectRequest) returns (SwitchProjectResponse);
rpc ListProjects(ListProjectsRequest) returns (ListProjectsResponse);
```

**CLI Commands**:
```bash
# Project management
spec project create <name> [--path <path>]
spec project list
spec project switch <name>
spec project current

# Existing commands with project scope
spec add-node "..." --project my-webapp
spec list-nodes --project demo-examples
spec extract ./src --project spec-oracle

# Cross-project operations
spec query "auth" --all-projects
```

#### 4. Migration Strategy

**Phase 1: Create projects/ structure**
- Create `~/.spec-oracle/projects/` directory
- Move existing `specs.json` to `projects/spec-oracle/specs.json`
- Create `config.json` with default project

**Phase 2: Update server**
- Add project context to server state
- Implement project loading
- Update all RPC handlers to use project context

**Phase 3: Update CLI**
- Add project commands
- Add `--project` flag to existing commands
- Default to current project from config

**Phase 4: Extract into separate projects**
- Extract spec-oracle's own specs → `spec-oracle` project
- Extract demo examples → `demo-examples` project
- Validate separation

### Backward Compatibility

**No breaking changes**:
- If no project specified, use "default" project
- Existing `~/spec-oracle/specs.json` becomes `~/.spec-oracle/projects/default/specs.json`
- CLI works same as before if user never uses project commands

## Edge Cases

### Cross-Project References
**Question**: What if specs in different projects reference each other?

**Answer**:
- By default: **Not allowed** (edges cannot cross project boundaries)
- Advanced: Add `--allow-cross-project` flag for relationship inference
- Use case: Shared domain definitions across microservices

### Project Discovery
**Question**: How to auto-discover projects?

**Answer**:
- Explicit registration: `spec project create`
- OR: Scan `projects/` directory for `specs.json` files
- Config file maintains project metadata

### Performance
**Question**: Does lazy-loading impact performance?

**Answer**:
- Negligible for typical usage (1-10 projects)
- Projects loaded once per server session
- Consider project unloading if memory becomes issue

## Success Criteria

After implementation:
- ✅ Can separate spec-oracle and demo specs into different projects
- ✅ Can switch between projects
- ✅ Can extract/query scoped to specific project
- ✅ Backward compatible with existing workflow
- ✅ No test failures

## Open Questions

1. **Should server maintain one project at a time or multiple?**
   - Recommendation: Multiple (lazy-loaded) for cross-project queries

2. **How to handle CLI without --project flag?**
   - Recommendation: Use current project from config

3. **Should projects be versioned?**
   - Future: Could add git integration per project
   - Not needed for MVP

## Next Steps

1. Implement config file structure
2. Update FileStore to support project paths
3. Add project management commands to CLI
4. Update server to handle project context
5. Migrate existing data
6. Extract spec-oracle and demo into separate projects
7. Test and validate

---

**Estimated effort**: 4-6 hours
**Priority**: High (unblocks real-world usage)
**Complexity**: Medium (well-defined problem, clear solution)
