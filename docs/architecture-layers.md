# Architecture: Why SpecRepository and UDAFModel Are Both Necessary

## TL;DR

**SpecRepository** and **UDAFModel** are NOT duplicates. They serve different purposes in a proper layered architecture:
- **SpecRepository**: Data persistence layer (Storage/Retrieval)
- **UDAFModel**: Formal verification layer (In-memory analysis)

## The Question

> "Node/Edgeってなんですか？私の理解ではUDA/fモデルをデータとして扱うためにSpecRepositoryが存在していると思っています。それはNode/Edgeなのですか？2つの同じものを使う必要があるのですか？"
>
> Translation: "What are Node/Edge? I understand that SpecRepository exists to handle UDA/f model as data. Is it Node/Edge? Do we need to use two of the same things?"

## The Answer

**SpecRepository and UDAFModel are NOT the same thing.**

They are two DIFFERENT layers with different responsibilities:

```
┌─────────────────────────────────────────┐
│  UDAFModel (Formal Verification Layer)  │  ← In-memory, semantic reasoning
│  - Performs Z3 SMT solving              │  ← HashMap structure
│  - Verifies consistency                 │  ← Operates on constraints
│  - Proves implications                  │  ← Domain: Formal verification
│  - Validates transforms                 │
└─────────────────────────────────────────┘
              ↕ ModelSync
┌─────────────────────────────────────────┐
│  SpecRepository (Persistence Layer)     │  ← On-disk, data storage
│  - Saves/loads to JSON/YAML             │  ← petgraph structure
│  - CRUD operations                      │  ← Operates on files
│  - Graph traversal                      │  ← Domain: Data persistence
│  - Versioning/history                   │
└─────────────────────────────────────────┘
```

## Detailed Explanation

### SpecRepository: The Persistence Layer

**Purpose**: Save and load specification data to/from disk.

**Data Structure**: `petgraph::DiGraph<SpecNodeData, SpecEdgeData>`
- Optimized for storage and retrieval
- Supports graph traversal
- Enables temporal queries (history, diffs)
- Serializes to JSON/YAML

**Operations**:
```rust
pub fn add_node(&mut self, data: SpecNodeData) -> Result<NodeId>
pub fn get_node(&self, id: &NodeId) -> Option<&SpecNodeData>
pub fn list_nodes(&self) -> Vec<&SpecNodeData>
pub fn add_edge(&mut self, source: NodeId, target: NodeId, kind: EdgeKind) -> Result<EdgeId>
pub fn save_to_disk(&self, path: &Path) -> Result<()>
pub fn load_from_disk(path: &Path) -> Result<Self>
```

**Responsibility**: "How is specification data stored on disk?"

**Analogy**: Like a database ORM - handles persistence, not business logic.

**Node/Edge are internal format**: SpecRepository uses Node/Edge as its INTERNAL data format for storage. This is an implementation detail.

### UDAFModel: The Verification Layer

**Purpose**: Perform formal verification and reasoning about specifications.

**Data Structure**:
```rust
pub struct UDAFModel {
    universes: HashMap<UniverseId, Universe>,           // U
    domains: HashMap<DomainId, Domain>,                  // D
    admissible_sets: HashMap<SpecId, AdmissibleSet>,     // A
    transforms: HashMap<TransformId, TransformFunction>, // f
    prover: Prover,  // Z3 SMT solver
}
```
- Optimized for formal reasoning
- Supports Z3 constraint solving
- Enables semantic verification
- Lives in memory (not serialized directly)

**Operations**:
```rust
pub fn verify_consistency(&self, a: SpecId, b: SpecId) -> ProofResult
pub fn verify_implication(&self, antecedent: SpecId, consequent: SpecId) -> ProofResult
pub fn verify_transform_soundness(&self, transform: TransformId) -> ProofResult
pub fn construct_u0(&mut self, artifacts: Vec<Artifact>) -> Result<Universe>
```

**Responsibility**: "Are these specifications formally consistent?"

**Analogy**: Like a business logic layer - handles domain operations, not persistence.

**UDA/f are semantic concepts**: UDAFModel works with Universe, Domain, AdmissibleSet, Transform. These are the FORMAL concepts from the UDA/f model.

## Why Both Are Necessary

### Data Flow Example: Verify Consistency

```
1. User Request:
   "Verify that spec A and spec B are consistent"

2. Load from Disk (SpecRepository)
   ┌─────────────────────────────┐
   │ SpecRepository.load()       │ ← Reads JSON/YAML files
   │ Returns: DiGraph<Node,Edge> │ ← Storage format
   └─────────────────────────────┘
                ↓
3. Build Verification Model (ModelSync)
   ┌──────────────────────────────────────┐
   │ ModelSync.sync_from_repository()     │ ← Transforms data
   │ Converts: Node → AdmissibleSet       │ ← Semantic mapping
   │ Builds: UDAFModel in memory          │
   └──────────────────────────────────────┘
                ↓
4. Perform Verification (UDAFModel)
   ┌────────────────────────────────────┐
   │ UDAFModel.verify_consistency()     │ ← Z3 solver
   │ Checks: A₁ ∩ A₂ ≠ ∅                │ ← Formal reasoning
   │ Returns: ProofResult               │
   └────────────────────────────────────┘
                ↓
5. Save Results (ModelSync)
   ┌──────────────────────────────────────┐
   │ ModelSync.export_proof_metadata()    │ ← Updates metadata
   │ Writes: Proof results to Node        │
   └──────────────────────────────────────┘
                ↓
6. Persist to Disk (SpecRepository)
   ┌─────────────────────────────┐
   │ SpecRepository.save()       │ ← Writes JSON/YAML
   │ Storage format: Node/Edge   │
   └─────────────────────────────┘
```

**Key Insight**: The same specification exists in TWO DIFFERENT FORMATS for two different purposes:
1. **Storage format** (Node/Edge in petgraph) - for persistence
2. **Semantic format** (AdmissibleSet in HashMap) - for verification

This is NOT duplication - it's **separation of concerns**.

### Real-World Analogy

Think of a web application with a database:

```
┌──────────────────────────────┐
│  Business Logic Layer        │  ← Services, domain models
│  - UserService               │  ← Validates business rules
│  - OrderService              │  ← Performs domain operations
│  - PaymentService            │  ← Reasons about workflows
└──────────────────────────────┘
              ↕ ORM (like ModelSync)
┌──────────────────────────────┐
│  Data Access Layer           │  ← Repository pattern
│  - UserRepository            │  ← CRUD operations
│  - OrderRepository           │  ← SQL queries
│  - PaymentRepository         │  ← Database transactions
└──────────────────────────────┘
              ↕
┌──────────────────────────────┐
│  Database (PostgreSQL)       │  ← Persistent storage
│  - Tables, rows, columns     │  ← Relational format
│  - Indexes, constraints      │  ← Optimized for disk
└──────────────────────────────┘
```

Would you say "Why do we need both UserService and UserRepository? Aren't they duplicates?"

**No!** They serve different purposes:
- **UserRepository**: How to store/retrieve user data (persistence)
- **UserService**: What to do with user data (business logic)

Similarly:
- **SpecRepository**: How to store/retrieve specifications (persistence)
- **UDAFModel**: What to verify about specifications (formal reasoning)

## The Problem with Only Having One

### If we only had SpecRepository (No UDAFModel):
```rust
// How would we verify consistency?
repository.add_node("Password >= 8");
repository.add_node("Password <= 6");

// ❌ SpecRepository has no way to know these contradict!
// It only knows how to store/retrieve data, not reason about it.
```

**Problem**: SpecRepository is a storage layer. It doesn't understand semantic meaning. It can't run Z3 solver. It can't verify constraints.

### If we only had UDAFModel (No SpecRepository):
```rust
// How would we persist to disk?
model.create_admissible_set(constraints);

// ❌ UDAFModel is in-memory only!
// If the program exits, all data is lost.
```

**Problem**: UDAFModel is a verification layer. It doesn't know how to serialize to disk. It doesn't handle file I/O. It can't manage storage.

## Node/Edge Are Implementation Details

**The core misunderstanding**:
> "Is SpecRepository's data format Node/Edge?"

**Yes, internally. But that's an IMPLEMENTATION DETAIL.**

From the client's perspective:
```
❌ BAD (exposing implementation):
   Client → AddNode() → SpecRepository
   "Client directly manipulates storage format"

✅ GOOD (proper abstraction):
   Client → CreateAdmissibleSet() → specd internally uses AddNode()
   "Client works with domain concepts, specd handles storage"
```

**Before Phase 1** (Proto exposed both levels):
```protobuf
service SpecOracle {
  // ❌ LOW-LEVEL: Storage layer (implementation details)
  rpc AddNode(...)
  rpc GetNode(...)
  rpc AddEdge(...)

  // ✅ HIGH-LEVEL: Domain layer (proper abstraction)
  rpc CreateAdmissibleSet(...)
  rpc VerifyConsistency(...)
}
```

**After Phase 1** (Proto only exposes domain concepts):
```protobuf
service SpecOracle {
  // ✅ ONLY expose UDA/f concepts
  rpc CreateUniverse(...)
  rpc CreateDomain(...)
  rpc CreateAdmissibleSet(...)
  rpc CreateTransform(...)
  rpc VerifyConsistency(...)

  // Node/Edge operations are INTERNAL - clients never see them
}
```

## Implementation: How specd Uses Both

When a client calls CreateAdmissibleSet:

```rust
// specd/src/service.rs
pub async fn create_admissible_set(
    &self,
    req: CreateAdmissibleSetRequest,
) -> Result<CreateAdmissibleSetResponse> {
    let project = self.project_manager.load_project(&req.project)?;

    // 1. Add to UDAFModel (verification layer) - SEMANTIC
    let spec_id = project.udaf_model.create_admissible_set(
        req.universe_id,
        req.constraints,
    )?;

    // 2. Save to SpecRepository (persistence layer) - STORAGE
    //    INTERNAL use of Node - client never sees this!
    project.repository.add_node(SpecNodeData {
        id: spec_id.clone(),
        content: format!("{:?}", req.constraints),
        kind: SpecNodeKind::AdmissibleSet,
        formality_layer: 0,
        metadata: HashMap::new(),
    })?;

    // 3. Save to disk
    self.project_manager.save_project(&project)?;

    // 4. Return UDA/f concept (NOT Node details)
    Ok(CreateAdmissibleSetResponse {
        admissible_set: Some(AdmissibleSet {
            spec_id,
            universe_id: req.universe_id,
            constraints: req.constraints,
            contradicts: vec![],
            metadata: HashMap::new(),
        }),
    })
}
```

**Client perspective**: "I created an AdmissibleSet with some constraints."

**Internal reality**: specd stored it as a Node in SpecRepository AND added it as an AdmissibleSet to UDAFModel.

**Client never knows about Nodes** - that's an implementation detail.

## Conclusion

**SpecRepository and UDAFModel are NOT duplicates.**

They implement the classic **separation of concerns**:
- **SpecRepository**: Persistence layer (How to store data)
- **UDAFModel**: Domain layer (How to reason about data)
- **ModelSync**: Bridge between them (How to convert between formats)

**Node/Edge are internal storage format**, not public API concepts.

**UDA/f concepts are public API**, exposed to clients.

This is proper software architecture, not duplication.

## Further Reading

- [Layered Architecture Pattern](https://en.wikipedia.org/wiki/Multitier_architecture)
- [Repository Pattern](https://martinfowler.com/eaaCatalog/repository.html)
- [Domain-Driven Design](https://en.wikipedia.org/wiki/Domain-driven_design)
- [Separation of Concerns](https://en.wikipedia.org/wiki/Separation_of_concerns)
