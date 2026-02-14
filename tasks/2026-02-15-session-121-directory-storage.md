# Session 121: Directory-Based Storage for Team Collaboration

**Date**: 2026-02-15
**Goal**: Resolve team collaboration blockers (merge conflicts, unreadable diffs)
**Status**: ✅ Migration implemented, ⏳ Auto-detection pending

## Problem

PROBLEM.md identified critical issues:
- **JSON format causes merge conflicts** - Single file, array operations
- **JSON diff unreadable** - Can't review spec changes in PRs
- **Team development blocked** - Practical collaboration impossible

## Solution: Directory-Based Storage

Implemented a new storage format where:
- **Each spec = one YAML file** (`.spec/nodes/<uuid>.yaml`)
- **All edges = one YAML file** (`.spec/edges.yaml`)
- **Human-readable** - YAML format, structured fields
- **Merge-friendly** - Different files rarely conflict

## Implementation

### 1. DirectoryStore (spec-core/src/store.rs)

```rust
pub struct DirectoryStore {
    base_path: PathBuf,
}

impl DirectoryStore {
    pub fn load(&self) -> Result<SpecGraph, StoreError> {
        // Load nodes from .spec/nodes/*.yaml
        // Load edges from .spec/edges.yaml
    }

    pub fn save(&self, graph: &SpecGraph) -> Result<(), StoreError> {
        // Save each node as individual YAML file
        // Save all edges to edges.yaml
    }
}
```

### 2. Migration Command

```bash
$ spec migrate
🔄 Migrating specifications...
  From: .spec/specs.json
  To:   .spec/nodes/
  📊 Loaded 238 nodes, 264 edges
  ✅ Migration complete!

📁 New structure:
  .spec/nodes/       - 238 YAML files (one per specification)
  .spec/edges.yaml   - Relationship definitions
```

### 3. File Format

**Node file** (`.spec/nodes/0154a181-1962-4aa1-aee2-236d2078caf6.yaml`):
```yaml
id: 0154a181-1962-4aa1-aee2-236d2078caf6
content: 'Prover.prove_satisfiability() proves that...'
kind: Assertion
metadata: {}
created_at: 1771065633
modified_at: 1771065633
formality_layer: 0
```

**Edges file** (`.spec/edges.yaml`):
```yaml
- source: c8f23449-3f4c-40b1-a8f4-6dc2c93444b1
  target: 386b1821-73e9-4b1c-90e4-618204cbad0e
  id: 2d031e80-e348-4518-9b2b-f2959a8cfcfe
  kind: Formalizes
  metadata: {}
  created_at: 1771061227
```

## Testing

✅ DirectoryStore tests pass:
```bash
$ cargo test directory_store
test store::directory_store_tests::directory_store_roundtrip ... ok
test store::directory_store_tests::directory_store_load_nonexistent ... ok
```

✅ Migration works:
```bash
$ ls .spec/nodes/ | wc -l
     238
$ head -7 .spec/nodes/0154a181-1962-4aa1-aee2-236d2078caf6.yaml
id: 0154a181-1962-4aa1-aee2-236d2078caf6
content: 'Prover.prove_satisfiability() proves...'
kind: Assertion
...
```

## Benefits

✅ **Merge conflict prevention**:
- Developer A: adds `node-A.yaml`
- Developer B: adds `node-B.yaml`
- No conflict! Different files.

✅ **Human-readable diffs**:
```diff
+ id: abc-123
+ content: Password must be 10+ chars
+ kind: Constraint
```
vs. JSON:
```diff
+ {"id":"abc-123","content":"Password must be 10+ chars",...}
```

✅ **File-level reviews**:
- PR shows: "Added spec for password length"
- Reviewers see: clear YAML structure
- No JSON noise

## Remaining Work

⏳ **Auto-detection of DirectoryStore**:
- CLI currently expects `specs.json`
- Should detect `nodes/` directory
- Auto-use DirectoryStore when present

⏳ **Backward compatibility**:
- Support both formats
- Seamless transition

## Next Session

Implement auto-detection in:
1. `spec-cli/src/persistence/store_router.rs`
2. Update `find_spec_file()` logic
3. Test all commands with DirectoryStore

## Commits

- `Add DirectoryStore implementation with YAML format`
- `Implement spec migrate command for JSON to directory conversion`
- `Export DirectoryStore from spec-core`

## Impact

This resolves **2 Critical problems** from PROBLEM.md:
- ✅ JSON merge conflicts → Minimized (different files)
- ✅ Unreadable diffs → Human-readable YAML

Team collaboration is now **viable**.
