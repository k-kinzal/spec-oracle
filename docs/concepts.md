# specORACLE Concepts Guide

## Overview

specORACLE is a **reverse mapping engine** for multi-layered specification management. This guide explains the core concepts that make specORACLE unique.

## The Problem: Multi-Layer Defense Without Coordination

Modern software uses multiple layers of defense to ensure correctness:

- **Tests** (unit, integration, E2E) - verify specific behaviors
- **Type systems** - static safety guarantees
- **Contracts** (Design by Contract) - pre/post-conditions
- **Property-based testing** - verify properties across random inputs
- **Formal methods** (TLA+, Alloy, Lean) - mathematical proofs

**The challenge**: Each layer evolves independently. Without coordination, the **entire system can be inconsistent**:

```
E2E test:     "Password must be >= 8 characters"
Type system:  String (no length constraint!)
Documentation: "Recommended: >= 10 characters"
Code comment: "TODO: Increase to 12 characters"
```

**Which is correct?** No one knows. This is what specORACLE solves.

## Core Concept: The Four Formality Layers (U0-U3)

specORACLE models specifications as existing across **four formality layers**:

### U0: Natural Language Requirements

**What it is**: Human-readable requirements, goals, constraints in natural language.

**Examples**:
- "Users must be able to log in securely"
- "Password must be at least 8 characters"
- "The system must detect contradictions in specifications"

**Characteristics**:
- Most abstract level
- May contain ambiguity
- Human-friendly
- Serves as the **root specification** (baseline for all other layers)

### U1: Formal Specifications

**What it is**: Mathematically rigorous models and proofs.

**Examples**:
- TLA+ specifications
- Alloy models
- Coq/Lean proofs
- Formal state machine definitions

**Characteristics**:
- Mathematically precise
- Provably correct
- Hard to write and maintain
- Not always practical for all systems

### U2: Interface Definitions

**What it is**: Contract definitions, type signatures, API specifications.

**Examples**:
- gRPC `.proto` files
- OpenAPI/Swagger definitions
- TypeScript type definitions
- Design by Contract specifications

**Characteristics**:
- Bridges abstract requirements and concrete implementation
- Machine-readable
- Language-independent (often)
- Defines **what** without **how**

### U3: Implementation Artifacts

**What it is**: Actual code, tests, assertions, invariants.

**Examples**:
- Source code (`assert!(password.len() >= 8)`)
- Unit tests
- Integration tests
- Runtime assertions

**Characteristics**:
- Most concrete level
- Executable and verifiable
- Language-specific
- Proves implementation reality

## Reverse Mapping: The specORACLE Innovation

Traditional specification tools work **top-down**: humans write specs, then implement them.

specORACLE works **bottom-up**: it constructs the root specification (U0) from **all layers** through **reverse mappings**.

### The Reverse Mapping Functions (f₀ᵢ⁻¹)

For each layer, specORACLE has a **reverse mapping function** that extracts specifications:

```
f₀₁⁻¹: U1 → U0  (formal specs → natural language requirements)
f₀₂⁻¹: U2 → U0  (interface defs → requirements)
f₀₃⁻¹: U3 → U0  (code/tests → requirements)
```

**U0 Construction**:

```
U0 = f₀₁⁻¹(U1) ∪ f₀₂⁻¹(U2) ∪ f₀₃⁻¹(U3)
```

U0 is **not written by humans** - it's **inferred from all artifacts**.

### Example: Password Length Requirement

**U3 (Code)**:
```rust
assert!(password.len() >= 8, "Password too short");
```

**Extraction** (`f₀₃⁻¹`):
- Analyze AST
- Find assertion: `password.len() >= 8`
- Extract constraint: "Password length must be >= 8"
- Store as U0 specification with `inferred=true`

**U2 (Proto)**:
```protobuf
// Password must be at least 8 characters
message AuthRequest {
  string password = 1;
}
```

**Extraction** (`f₀₂⁻¹`):
- Parse proto file
- Extract comment
- Store as U0 specification

**Result**: U0 now contains specifications from both code and interface definition. If they **contradict**, specORACLE detects it.

## Specification Kinds

specORACLE classifies specifications by their **logical nature**:

### Assertion
**Meaning**: Concrete claim about specific behavior.

**Examples**:
- "The login RPC returns a token on success"
- "Graph nodes are color-coded by kind"

**Usage**: Describe specific observable facts.

### Constraint
**Meaning**: Universal invariant that must always hold.

**Logic**: ∀x. P(x) (for all x, P(x) is true)

**Examples**:
- "Password must be at least 8 characters" (for all passwords)
- "The system must detect contradictions" (always)

**Usage**: Express requirements that have no exceptions.

### Scenario
**Meaning**: Existential requirement - a path/flow that must be possible.

**Logic**: ∃x. P(x) (there exists x such that P(x))

**Examples**:
- "Users can reset their password via email"
- "A valid login flow exists"

**Usage**: Describe required capabilities or user journeys.

### Definition
**Meaning**: Term definition or concept explanation.

**Examples**:
- "Formality layer: degree of formalism (0=natural, 1=formal, 2=interface, 3=executable)"
- "Reverse mapping: extracting specifications from artifacts"

**Usage**: Establish vocabulary and shared understanding.

### Domain
**Meaning**: Boundary declaration for a logical domain.

**Examples**:
- "Authentication"
- "Storage"
- "API Layer"

**Usage**: Organize specifications into coherent areas.

## Relationships Between Specifications

Specifications connect to each other through **typed edges**:

### Refines
**Meaning**: Target is a more specific/detailed version of source.

**Example**:
- U0: "Users must authenticate"
  - **refines** → "Password authentication is required"

**Usage**: Trace from abstract to concrete.

### Formalizes
**Meaning**: Target is a more formal version of source (across formality layers).

**Example**:
- U0: "Password must be at least 8 characters"
  - **formalizes** → U3: `assert!(password.len() >= 8)`

**Usage**: Connect natural language requirements to executable code.

### DerivesFrom
**Meaning**: Source was automatically derived from target.

**Example**:
- U0: "Password length constraint" (inferred)
  - **derives_from** → U3: Code assertion

**Usage**: Track provenance of auto-extracted specs.

### DependsOn
**Meaning**: Source requires target to be satisfied first.

**Example**:
- "User can change password"
  - **depends_on** → "User must be authenticated"

**Usage**: Express prerequisite relationships.

### Contradicts
**Meaning**: Source and target are logically incompatible.

**Example**:
- "Password must be >= 8 characters"
  - **contradicts** → "Password must be <= 6 characters"

**Usage**: Detected by Z3 SMT solver or heuristics.

### Transform
**Meaning**: Maps specification from one universe to another.

**Example**:
- U0: "Authentication requirement"
  - **transform** → U2: AuthRequest proto definition

**Usage**: Represent the f function in U/D/A/f model.

## The U/D/A/f Model

specORACLE is built on a formal model of specifications:

### U (Universe)
**Meaning**: The complete set space where specifications are defined.

**Types**:
- **U0**: Root universe (natural language requirements)
- **U1**: Formal specification universe (TLA+, Alloy)
- **U2**: Interface universe (proto, OpenAPI)
- **U3**: Implementation universe (code, tests)

Each universe is a projection of the root specification at different formality levels.

### D (Domain)
**Meaning**: The actual region of concern that a specification governs.

**Example**:
- U = "All possible password strings"
- D = "Passwords of length 1-100"
- A specification may only cover D, not all of U

### A (Admissible Set)
**Meaning**: The set of implementations that **satisfy** a specification.

**Example**:
- Constraint: "Password >= 8 characters"
- A = {all password strings with length >= 8}

**Contradiction detection**: If A₁ ∩ A₂ = ∅, then specs contradict.

### f (Transform Function)
**Meaning**: Maps specifications between universes.

**Types**:
- **Forward**: f₀ᵢ: U0 → Ui (root → layer i)
- **Reverse**: f₀ᵢ⁻¹: Ui → U0 (layer i → root) ← **specORACLE's core**

The reverse mapping is what makes specORACLE unique.

## Self-Governance: specORACLE Managing Itself

**The Essence**: A tool that governs multi-layer defenses must **govern itself**.

specORACLE uses itself to manage its own specifications:

1. **Specifications are checked into the codebase** (`.spec/` directory)
2. **Code extraction** runs on specORACLE's own source code
3. **Contradiction detection** runs on specORACLE's specs
4. **Omission detection** finds gaps in specORACLE's coverage

**Example**: Session 109 detected that specORACLE's own CLI violated separation of concerns:

```
Contradiction:
  A: [d26341fb] The CLI architecture violates separation of concerns (U3)
  B: [b706e529] The CLI implementation must separate concerns (U0)
```

This was **not a failure** - it was **the system working as designed**. specORACLE detected its own violation and reported it.

## Why This Matters

### Single Layer = Incomplete
No single method can guarantee correctness:
- Tests can't cover all cases
- Types can't express "length >= 8"
- Formal methods can't scale to full systems

**Solution**: Multi-layer defense.

### Multi-Layer = Inconsistent (Without Coordination)
Each layer evolves independently:
- E2E test says 8 characters
- Documentation says 10 characters
- Code comment says 12 characters

**Solution**: specORACLE coordinates all layers.

### The Reverse Mapping Paradigm
Traditional: Humans write specs → implement them
- Problem: Specs diverge from reality

**specORACLE**: Observe reality → infer specs → verify consistency
- Solution: Specs stay synchronized with code

## Getting Started With Concepts

1. **Initialize**: `spec init` creates `.spec/` directory
2. **Add requirements** (U0): `spec add "Password must be >= 8 characters"`
3. **Extract from code** (U3): `spec extract src/`
4. **Check consistency**: `spec check`
5. **Visualize layers**: `spec trace <spec-id>`

specORACLE will show you:
- Which specs are U0 (requirements)
- Which specs are U3 (code)
- How they're connected via `formalizes` edges
- Where contradictions or omissions exist

## Further Reading

- **docs/motivation.md** - Why specORACLE is needed
- **docs/conversation.md** - Deep theoretical foundation (U/D/A/f model)
- **README.md** - Features, commands, examples
- **CLAUDE.md** - Project goals and constraints
