# Fixes Applied: Password Spec Bug and Project Separation Design

**Date**: 2026-02-14
**Status**: In Progress

## Fix 1: Synonym Rule Ordering Bug ✅ APPLIED

### Problem
Password specs with 0.875 similarity weren't connected because:
1. Refines rule (threshold 0.6, multiplier 0.75) matched first
2. Returned confidence 0.656 (0.875 × 0.75)
3. Below auto-creation threshold (0.7)
4. Synonym rule (threshold 0.8, multiplier 0.95) never checked

### Root Cause
Rule ordering in `spec-core/src/extract.rs:infer_edge_kind()`:
- Refines checked before Synonym
- Early return prevented higher-confidence Synonym match

### Fix Applied
Reordered rules to check most specific (highest threshold) first:

**New order**:
1. **Synonym** (threshold 0.8, multiplier 0.95) - Most specific
2. **Formalizes** (threshold 0.5, cross-layer)
3. **DerivesFrom** (threshold 0.5, Assertion → Constraint)
4. **Refines** (threshold 0.6, general fallback)

**Expected outcome** for password specs:
- Similarity 0.875 > 0.8 → Synonym rule matches
- Confidence: 0.875 × 0.95 = **0.831**
- 0.831 > 0.7 threshold → **auto-created** ✓

### Validation
```bash
# Tests pass
cargo test --release
# Result: 55 passed ✓

# Need to rebuild and test
cargo build --release
./target/release/spec infer-relationships-ai --min-confidence 0.7

# Expected: Password specs now connected
```

### Files Changed
- `spec-core/src/extract.rs` (lines 363-418)

---

## Fix 2: Project Separation ⏳ DESIGN PHASE

### Problem
All specifications (spec-oracle's own + demo examples) mixed in single global graph.

**Current limitations**:
- Cannot separate spec-oracle specs from password demo specs
- No multi-project support
- No project-scoped commands
- Single storage file for all specs

### Real-World Requirements
Users need to:
1. Manage multiple projects separately
2. Switch between projects (`spec --project myapp query "auth"`)
3. Extract specs per-project (`spec extract --project myapp src/`)
4. Prevent cross-project pollution
5. Optionally infer cross-project relationships

### Design Options

#### Option A: Project-Scoped Storage Files ✅ RECOMMENDED

**Concept**: Separate .graph file per project

```
~/.spec-oracle/
  projects/
    spec-oracle/
      graph.json
      metadata.json
    my-webapp/
      graph.json
      metadata.json
    demo-password/
      graph.json
      metadata.json
  current-project → spec-oracle (symlink)
```

**Pros**:
- Clean isolation
- Simple implementation
- Easy backup/sharing per project
- Natural multi-project workflows

**Cons**:
- Cannot query across projects easily
- Need project switching mechanism

**Implementation**:
```rust
// Add to SpecNodeData (no changes needed - use existing metadata)
// Projects identified by storage file path

// New commands:
spec init --project <name>          // Create new project
spec use <project>                  // Switch current project
spec list-projects                  // List all projects
spec --project <name> <command>     // Run command in project scope
```

#### Option B: Project Metadata Filtering ❌ NOT RECOMMENDED

**Concept**: Add `project_id` field to SpecNodeData, single shared graph

**Pros**:
- Can query across projects
- Single storage

**Cons**:
- Filtering burden on every operation
- Risk of cross-project edges
- Harder to backup/share per project
- Doesn't align with "multiple projects" mental model

#### Option C: Separate Databases per Project ⚠️ OVERKILL

**Concept**: Each project gets own database instance

**Pros**:
- Strong isolation
- Scales to very large projects

**Cons**:
- Complex implementation
- Requires database setup per project
- Over-engineered for current use case

### Recommended Implementation: Option A

**Phase 1: Project Storage**
1. Add project config file: `~/.spec-oracle/config.toml`
   ```toml
   current_project = "spec-oracle"

   [projects.spec-oracle]
   path = "/Users/ab/.spec-oracle/projects/spec-oracle"
   created = "2026-02-14"

   [projects.demo-password]
   path = "/Users/ab/.spec-oracle/projects/demo-password"
   created = "2026-02-14"
   ```

2. Update storage to use project-scoped paths
   ```rust
   // Current
   let store = FileStore::new("~/.spec-oracle/graph.json");

   // New
   let config = ProjectConfig::load()?;
   let project_path = config.current_project_path();
   let store = FileStore::new(&project_path.join("graph.json"));
   ```

3. Add project management commands
   ```bash
   spec init --project demo-password
   spec use spec-oracle
   spec list-projects
   ```

**Phase 2: Migration**
1. Detect existing `~/.spec-oracle/graph.json`
2. Auto-migrate to `projects/default/graph.json`
3. Set `default` as current project

**Phase 3: Project-Scoped Operations**
1. Add `--project` flag to all commands
2. Default to current project
3. Validate project exists before operations

### Files to Modify

**New files**:
- `spec-core/src/project.rs` - Project config management
- `~/.spec-oracle/config.toml` - Project registry

**Modified files**:
- `spec-core/src/store.rs` - Use project-scoped paths
- `specd/src/main.rs` - Load project config
- `spec-cli/src/main.rs` - Add project commands

### Migration Path for Current Data

Current state:
- `/Users/ab/.spec-oracle/graph.json` (576 nodes, mixed content)

After migration:
- `/Users/ab/.spec-oracle/projects/spec-oracle/graph.json` (spec-oracle specs only)
- `/Users/ab/.spec-oracle/projects/demo-password/graph.json` (password demo specs only)

**How to separate**:
1. Read current graph
2. Filter by metadata/source patterns:
   - Has `source_file` containing "examples/" → demo-password
   - Has `source_file` containing "spec-" dirs → spec-oracle
   - No `source_file` → manual classification needed
3. Write to separate project graphs
4. Verify omission counts per project

### Next Steps

1. ✅ Fix synonym rule ordering - DONE
2. ⏳ Rebuild binaries
3. ⏳ Test password spec fix
4. ⏳ Implement project separation (Phase 1)
5. ⏳ Migrate existing data to projects
6. ⏳ Re-run inference per project
7. ⏳ Validate omission reduction per project

---

## Testing Plan

### Test 1: Synonym Fix Validation
```bash
# Rebuild
cargo build --release

# Check current state
./target/release/spec get-node 77ad7450-1072-4026-a66c-13f6f8cd3eb4
./target/release/spec get-node 34bf0b12-1e8a-4b8e-979a-bf25adc81568
./target/release/spec list-edges --node 77ad7450-1072-4026-a66c-13f6f8cd3eb4

# Clear graph and re-extract
./target/release/spec extract --source spec-core --language rust
./target/release/spec extract --source examples --language rust

# Re-run AI inference
./target/release/spec infer-relationships-ai --min-confidence 0.7

# Verify password specs now connected
./target/release/spec detect-omissions | grep -i password
```

**Expected**:
- Password specs have Synonym edges
- Omissions reduced for password-related specs
- Overall omission count improved

### Test 2: Project Separation
```bash
# After implementing project support
spec init --project spec-oracle
spec init --project demo-password

# Migrate data (manual or scripted)
spec use spec-oracle
spec extract --source spec-core --language rust
spec extract --source specd --language rust
spec extract --source spec-cli --language rust

spec use demo-password
spec extract --source examples --language rust

# Verify separation
spec use spec-oracle
spec detect-omissions  # Should only show spec-oracle omissions

spec use demo-password
spec detect-omissions  # Should only show demo omissions
```

---

## Success Criteria

### For Synonym Fix
- ✅ Tests pass (55/55)
- ⏳ Password specs 77ad7450 ↔ 34bf0b12 connected with Synonym edge
- ⏳ Overall omission count < 168 (current)
- ⏳ No regressions in other edge types

### For Project Separation
- ⏳ Can create new projects
- ⏳ Can switch between projects
- ⏳ Commands scoped to current project
- ⏳ spec-oracle and demo specs cleanly separated
- ⏳ Each project independently maintainable

---

**Status**:
- Synonym fix applied and tested ✓
- Project separation designed, implementation pending
- Ready for rebuild and validation
