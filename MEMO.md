# Implementation Notes: UAD/f Type Strictness Refactoring

## Date
2026-02-15

## Summary
Completed comprehensive type-safety refactoring of the UAD/f model to eliminate string-based IDs and enforce naming conventions through the type system.

## Changes Implemented

### Phase 1: New Type System (✅ Complete)
Created three new modules under `spec-core/src/udaf/`:

#### `ids.rs` - Type-Safe ID System
- **UniverseId**: Enforces "U{layer}" format (e.g., "U0", "U1")
  - `root()` for U0
  - `projection(layer)` for U1-UN
  - `layer()` derives layer from ID
  - Parse validation prevents invalid formats

- **DomainId**: UUID-based identifier
  - `new()` generates UUID
  - `parse()` validates UUID format

- **SpecId**: UUID-based identifier for specifications
  - Same pattern as DomainId

- **TransformId**: Enforces "f_{source}_to_{target}" format
  - `inverse(&source)` for f_U1_to_U0 patterns
  - `forward(&source, &target)` for f_U1_to_U2 patterns
  - `source()` and `target()` extract UniverseIds

All ID types implement:
- Serialize/Deserialize for JSON compatibility
- `as_str()` for string conversion
- Display trait for printing
- PartialEq, Eq, Hash for collections

#### `metadata.rs` - Type-Safe Metadata System
- **MetadataKey enum**: Well-known keys (Universe, SourceFile, RpcName, Extractor, etc.) + Custom(String) for extensibility

- **Specialized Metadata types**:
  - `UniverseMetadata`: source_file() accessor
  - `DomainMetadata`: source() accessor
  - `ConstraintMetadata`: pattern(), value(), min(), max(), source() accessors
  - `TransformMetadata`: extractor(), source_file() accessors

All metadata types:
- Wrap HashMap<String, String> internally (backward compatible)
- Provide type-safe accessors for common fields
- Serialize/deserialize transparently

#### `refs.rs` - Type-Safe Reference Sets
- **SpecSet**: Type-safe HashSet<SpecId>
  - `insert(SpecId)`, `contains(&SpecId)`
  - `check_integrity(&HashSet<String>)` validates references
  - Serializes as HashSet<String> for compatibility

- **DomainSet**: Type-safe collection of DomainIds
  - Same API as SpecSet
  - Serializes as Vec<String> to match original format

### Phase 2: UDAF Struct Updates (✅ Complete)
Updated all main structs to use typed IDs:

#### Universe
- ~~`layer: u8`~~ **REMOVED** (redundant, derive from id)
- `id: String` → `id: UniverseId`
- `specifications: HashSet<String>` → `specifications: SpecSet`
- `metadata: HashMap<String, String>` → `metadata: UniverseMetadata`
- Added `layer()` method that derives from `id`

#### Domain
- `id: String` → `id: DomainId`
- `universe_id: String` → `universe_id: UniverseId`
- `covered_by: HashSet<String>` → `covered_by: SpecSet`
- `subdomains: Vec<String>` → `subdomains: DomainSet`
- `metadata: HashMap<String, String>` → `metadata: DomainMetadata`

#### AdmissibleSet
- `spec_id: String` → `spec_id: SpecId`
- `universe_id: String` → `universe_id: UniverseId`
- `contradicts: HashSet<String>` → `contradicts: SpecSet`
- `metadata: HashMap<String, String>` → `metadata: Metadata`

#### Constraint
- `metadata: HashMap<String, String>` → `metadata: ConstraintMetadata`

#### TransformFunction
- `id: String` → `id: TransformId`
- `source_universe: String` → `source_universe: UniverseId`
- `target_universe: String` → `target_universe: UniverseId`
- `metadata: HashMap<String, String>` → `metadata: TransformMetadata`

#### UDAFModel
- `universes: HashMap<String, Universe>` → `HashMap<UniverseId, Universe>`
- `domains: HashMap<String, Domain>` → `HashMap<DomainId, Domain>`
- `admissible_sets: HashMap<String, AdmissibleSet>` → `HashMap<SpecId, AdmissibleSet>`
- `transforms: HashMap<String, TransformFunction>` → `HashMap<TransformId, TransformFunction>`
- `metadata: HashMap<String, String>` → `metadata: Metadata`

Added custom serde modules for HashMap serialization to maintain JSON compatibility.

### Phase 3: Constructor Updates (✅ Complete)
Updated constructors to return Result where parsing can fail:

- `Universe::root()` → unchanged
- `Universe::projection(layer)` → `Result<Universe, IdError>`
- `Universe::layer()` → derives from id.layer()
- `Domain::new(name, desc, universe_id)` → auto-generates DomainId
- `Domain::with_id(id, name, desc, universe_id)` → for loading from storage
- `TransformFunction::inverse(source, desc, strategy)` → uses TransformId::inverse()
- `TransformFunction::forward(source, target, desc, strategy)` → uses TransformId::forward()
- `UDAFModel::add_universe(layer, name, desc)` → `Result<UniverseId, IdError>`

### Phase 4: Internal Implementation Updates (✅ Complete)
Updated all internal methods:

#### `construct_u0()`
- Use `universe_id.layer()` instead of `universe.layer`
- Use `TransformId::inverse(universe_id)` for lookup
- Type-safe iteration over universes

#### `populate_from_graph()`
- Parse universe IDs with `UniverseId::parse()`
- Parse spec IDs with `SpecId::parse()`
- Convert graph metadata to ConstraintMetadata
- Use typed IDs throughout

#### `detect_contradictions()`
- Use `as_str()` for string output
- Type-safe iteration over admissible_sets

#### `extract_constraints_from_text()`
- Build ConstraintMetadata using typed setters
- Use `set_pattern()`, `set_value()`, `set_min()`, `set_max()`, `set_source()`

### Phase 5: Related File Updates (✅ Complete)
Updated dependent code:

#### `spec-cli/src/commands/u0.rs`
- Use `universe.layer()` instead of `universe.layer`
- Use `id.as_str()` for display

#### Other files
- `graph.rs`: Uses string-based metadata (appropriate, not part of UDAF model)
- `extract.rs`: Uses HashMap metadata (appropriate for inference boundary)
- `specd/src/service.rs`: Uses string-based metadata at gRPC boundary (appropriate)

### Phase 6: Validation Method (✅ Complete)
Added `UDAFModel::validate()` method:
- Checks Universe.specifications reference valid SpecIds
- Checks Domain.universe_id reference valid UniverseIds
- Checks Domain.covered_by reference valid SpecIds
- Checks Domain.subdomains reference valid DomainIds
- Checks AdmissibleSet.universe_id reference valid UniverseIds
- Checks AdmissibleSet.contradicts reference valid SpecIds
- Checks Transform source/target universes reference valid UniverseIds
- Returns detailed error messages for all violations

## Benefits

### Type Safety
- **Compile-time checks**: Can't mix up DomainId and SpecId
- **Format enforcement**: UniverseId must be "U0", "U1", etc.
- **ID validation**: Parse errors caught early

### Maintainability
- **Clear intent**: Type signatures document what IDs are expected
- **Refactoring safety**: Compiler catches all usages
- **Metadata consistency**: No typos in metadata keys

### Design Clarity
- **Removed redundancy**: Universe.layer field eliminated
- **Single source of truth**: Layer derived from ID
- **Better encapsulation**: IDs enforce their own invariants

## Backward Compatibility
- JSON serialization format unchanged
- HashMap<String, V> serialized with string keys
- Existing storage files can be loaded without migration
- Serde handles conversion transparently

## Design Decision: Universe.layer Removal

### Rationale
The `layer` field in Universe was redundant because:
1. Universe ID already encodes the layer ("U0", "U1", etc.)
2. Having two sources of truth creates inconsistency risk
3. The ID is the canonical representation

### Alternative Considered
Keep both `id` and `layer`, enforce consistency in constructors.

### Why Rejected
- More code to maintain
- Validation overhead
- Still possibility of manual construction creating inconsistency
- Violates DRY principle

### Implementation
- Removed `layer` field from Universe struct
- Added `layer()` method that parses from ID
- Updated all code using `universe.layer` to `universe.layer()`
- UniverseId.layer() is infallible (ID format validated on construction)

## Testing Strategy
1. Module-level unit tests in ids.rs, metadata.rs, refs.rs
2. Integration tests for UDAFModel operations
3. Serialization round-trip tests
4. Validation tests for reference integrity

## Future Enhancements
- Consider SMT solver integration for constraint satisfiability
- Add more metadata key types as patterns emerge
- Implement graph-level validation using UDAFModel::validate()

## Critical Files Modified
- `spec-core/src/udaf.rs` - Main UDAF implementation
- `spec-core/src/udaf/ids.rs` - New ID types
- `spec-core/src/udaf/metadata.rs` - New metadata types
- `spec-core/src/udaf/refs.rs` - New reference set types
- `spec-core/src/lib.rs` - Export new types
- `spec-cli/src/commands/u0.rs` - CLI integration
