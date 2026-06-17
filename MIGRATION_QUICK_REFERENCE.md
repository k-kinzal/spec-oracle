# Migration Quick Reference: Node/Edge → UDA/f Operations

## ⚠️  Deprecation Notice

Node/Edge operations are deprecated and will be removed in v2.0.0. Please migrate to UDA/f operations.

## Quick Migration Table

| Deprecated Command | Replacement | Example |
|-------------------|-------------|---------|
| `spec rpc add-node` | `spec add` or `spec rpc create-admissible-set` | See below ↓ |
| `spec rpc get-node <id>` | `spec rpc get-admissible-set <spec-id>` | See below ↓ |
| `spec rpc list-nodes` | `spec rpc list-admissible-sets` or `spec summary` | See below ↓ |
| `spec rpc remove-node` | Managed through UDA/f lifecycle | N/A |
| `spec rpc add-edge` | `spec rpc create-transform` | See below ↓ |
| `spec rpc list-edges` | `spec rpc list-transforms` | See below ↓ |
| `spec rpc remove-edge` | Managed through UDA/f lifecycle | N/A |
| `spec rpc set-universe` | `spec rpc create-universe` + `create-admissible-set` | See below ↓ |
| `spec rpc filter-by-layer` | `spec rpc list-universes` | See below ↓ |

## Detailed Examples

### 1. Adding a Specification

#### ❌ Old Way (Deprecated)
```bash
spec rpc add-node "Password must be at least 8 characters" --kind constraint
```

#### ✅ New Way
```bash
# Simple: Use high-level command (auto-creates AdmissibleSet in U0)
spec add "Password must be at least 8 characters"

# Advanced: Create explicitly in a specific universe
spec rpc create-admissible-set \
  --spec U1 \
  --constraint "length(password) >= 8"
```

### 2. Getting a Specification

#### ❌ Old Way (Deprecated)
```bash
spec rpc get-node abc123-node-id
```

#### ✅ New Way
```bash
spec rpc get-admissible-set abc123-spec-id
```

### 3. Listing Specifications

#### ❌ Old Way (Deprecated)
```bash
spec rpc list-nodes --kind constraint --layer 1
```

#### ✅ New Way
```bash
# Simple: Summary view
spec summary

# Advanced: List all admissible sets
spec rpc list-admissible-sets

# Filter by universe (which has layer info)
spec rpc list-universes  # Find universe ID
spec rpc list-admissible-sets  # Lists all, can filter by universe_id
```

### 4. Adding Relationships

#### ❌ Old Way (Deprecated)
```bash
spec rpc add-edge source-node-id target-node-id --kind refines
```

#### ✅ New Way
```bash
# For universe-to-universe mappings (formal concept)
spec rpc create-transform \
  --source U1 \
  --target U0 \
  --kind inverse

# For specification relationships
# These are now managed through:
# - VerifyConsistency: Detects contradictions
# - VerifyImplication: Detects implications
# - InferRelationships: Auto-discovers relationships
```

### 5. Listing Relationships

#### ❌ Old Way (Deprecated)
```bash
spec rpc list-edges --node abc123
```

#### ✅ New Way
```bash
# List universe transforms
spec rpc list-transforms

# Or use high-level tracing
spec trace <spec-id>
```

### 6. Working with Universes

#### ❌ Old Way (Deprecated)
```bash
spec rpc set-universe node-id "ui-layer"
```

#### ✅ New Way
```bash
# First, create a universe
spec rpc create-universe \
  --layer 1 \
  --name "UI Layer" \
  --description "User interface specifications"

# Then, create specifications in that universe
spec rpc create-admissible-set \
  --spec <universe-id> \
  --constraint "Button must be clickable"
```

### 7. Filtering by Layer

#### ❌ Old Way (Deprecated)
```bash
spec rpc filter-by-layer --min 1 --max 2
```

#### ✅ New Way
```bash
# List universes (which have layer information)
spec rpc list-universes

# Then list admissible sets for specific universes
spec rpc list-admissible-sets  # Shows all with universe_id
```

## Conceptual Mapping

### What Changed?

**Before** (Node/Edge thinking):
```
Graph with generic nodes and edges
├── Node (generic container)
├── Edge (generic relationship)
└── Metadata (universe, layer, etc.)
```

**After** (UDA/f thinking):
```
Formal model with semantic concepts
├── Universe (U) - Space where specs are defined
├── Domain (D) - Region a spec covers
├── AdmissibleSet (A) - Set of allowed implementations
└── Transform (f) - Mapping between universes
```

### Key Differences

| Node/Edge (Old) | UDA/f (New) | Why? |
|----------------|-------------|------|
| Node is a generic container | AdmissibleSet is a formal concept | Semantic meaning |
| Edge is a generic link | Transform is a mathematical mapping | Formal verification |
| Universe is metadata | Universe is a first-class concept | Proper abstraction |
| Layer is a number | Layer defines universe hierarchy | Structural clarity |

## Understanding the UDA/f Model

### The Four Components

1. **Universe (U)**: The space in which specifications are defined
   - U0: Root universe (natural language requirements)
   - U1: First refinement (TLA+, formal specs)
   - U2: Interface universe (gRPC proto, API specs)
   - U3: Implementation universe (code, tests)

2. **Domain (D)**: The region a specification covers
   - Example: "Authentication module", "User profile API"

3. **AdmissibleSet (A)**: The set of implementations that satisfy a spec
   - Defined by constraints (e.g., "password.length >= 8")
   - Can be verified for consistency (A₁ ∩ A₂ ≠ ∅)
   - Can be verified for implication (A₁ ⊆ A₂)

4. **Transform (f)**: Mapping between universes
   - Forward: Ui → Uj (refinement, more concrete)
   - Inverse: Ui → U0 (reverse mapping, extract requirements)
   - Parallel: Ui → Uj (different aspects, same layer)

### Example Workflow

```bash
# 1. Create universes for different layers
spec rpc create-universe --layer 1 --name "TLA+ Specs" --description "Formal specifications"
spec rpc create-universe --layer 2 --name "gRPC Proto" --description "API interface"
spec rpc create-universe --layer 3 --name "Rust Code" --description "Implementation"

# 2. Add specifications to each universe
spec rpc create-admissible-set --spec U1 --constraint "∀n: n ≥ 1 → valid(n)"
spec rpc create-admissible-set --spec U2 --constraint "message User { int32 id = 1; }"
spec rpc create-admissible-set --spec U3 --constraint "struct User { id: i32 }"

# 3. Create transforms between universes
spec rpc create-transform --source U3 --target U2 --kind forward  # Code → Proto
spec rpc create-transform --source U2 --target U1 --kind forward  # Proto → TLA+
spec rpc create-transform --source U1 --target U0 --kind inverse  # TLA+ → Requirements

# 4. Verify consistency
spec rpc verify-consistency --spec-a <spec1> --spec-b <spec2>

# 5. Construct U0 from all layers (reverse mapping)
spec rpc construct-u0 --artifact src/main.rs --artifact proto/user.proto
```

## Common Patterns

### Pattern 1: Simple Specification Management

```bash
# Old way: Manual node/edge management
spec rpc add-node "spec 1" --kind constraint
spec rpc add-node "spec 2" --kind constraint
spec rpc add-edge <id1> <id2> --kind refines

# New way: High-level commands + auto-inference
spec add "spec 1"
spec add "spec 2"
spec infer-relationships  # Auto-discovers relationships
```

### Pattern 2: Multi-Layer Specification

```bash
# Old way: Nodes with layer metadata
spec rpc add-node "Natural language spec" --kind constraint
# (manually set layer metadata later)

# New way: Explicit universe hierarchy
spec rpc create-universe --layer 0 --name "Requirements" --description "..."
spec rpc create-admissible-set --spec U0 --constraint "Natural language spec"
```

### Pattern 3: Verification

```bash
# Old way: Manual contradiction detection
spec detect-contradictions  # Returns node pairs

# New way: Formal verification
spec rpc verify-consistency --spec-a <id1> --spec-b <id2>
# Returns formal proof: A₁ ∩ A₂ ≠ ∅ or A₁ ∩ A₂ = ∅
```

## FAQ

### Q: Why can't I just keep using Node/Edge?

**A**: Node/Edge operations will be removed in v2.0.0. They expose internal storage format, not domain concepts. UDA/f operations provide:
- Formal verification (Z3 solver)
- Semantic meaning (Universe, Domain, AdmissibleSet)
- Better architecture (separation of concerns)

### Q: What happens to my existing specifications?

**A**: Your data is safe. SpecRepository continues to store data as Node/Edge internally. The only change is the API you use to access it. Use `spec rpc list-admissible-sets` to see your specs.

### Q: Can I mix old and new commands?

**A**: Yes, during Phase 1 & 2. All deprecated commands still work but show warnings. Eventually (v2.0.0), deprecated commands will be removed.

### Q: How do I migrate my scripts?

**A**: Use this guide to replace deprecated commands. Test your scripts with the new commands. If you encounter issues, file an issue on GitHub.

### Q: What about the `spec add` command?

**A**: `spec add` is NOT deprecated. It's a high-level command that internally uses UDA/f operations. Continue using it.

### Q: I used `spec rpc add-node` in my CI pipeline. What should I do?

**A**: Replace it with `spec add` (high-level) or `spec rpc create-admissible-set` (low-level). Example:

```bash
# Old CI pipeline
spec rpc add-node "Test coverage must be > 80%" --kind constraint

# New CI pipeline (option 1: high-level)
spec add "Test coverage must be > 80%"

# New CI pipeline (option 2: low-level)
spec rpc create-admissible-set \
  --spec U0 \
  --constraint "coverage > 0.8"
```

## Getting Help

- **Documentation**: See `docs/architecture-layers.md` for detailed explanation
- **Examples**: Check `examples/` directory for migration examples
- **Issues**: Report problems at https://github.com/your-org/spec-oracle/issues
- **Questions**: Ask on GitHub Discussions

## Timeline

- **Now (Phase 1)**: Deprecated commands show warnings but still work
- **Future (Phase 2)**: CLI migrated to UDA/f operations
- **v2.0.0 (Phase 3)**: Deprecated commands removed

**Recommendation**: Migrate to UDA/f operations now to avoid breaking changes in v2.0.0.
