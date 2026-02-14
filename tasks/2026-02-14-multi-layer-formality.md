# Implementing Multi-Layered Formality

**Date**: 2026-02-14
**Goal**: Implement multi-layered conceptual specifications

## Motivation

From `docs/conversation.md`, the fundamental problem:
- Specifications are inherently multi-layered (unit, integration, E2E, formal, etc.)
- Different layers use different formalisms
- No single "ruler" measures correctness across layers
- This is a paradox: you need unified spec but can't have one

The requirement in CLAUDE.md:
> "The managed specifications must possess multi-layered concepts."

## Research Findings

From `tasks/2026-02-14-specification-tools-landscape-research.md`:
**Principle 2**: Multi-Level Formality
- Current tools force binary choice: formal or informal
- Reality: Continuous spectrum needed
- Different stakeholders need different views
- Formality-accessibility is a fundamental trade-off, not a bug

## Proposed Implementation

### Layer Model

Define formality layers:
- **Layer 0** (Natural): Stakeholder-readable natural language
- **Layer 1** (Structured): Semi-formal (typed constraints, structured patterns)
- **Layer 2** (Formal): Mathematical/logical representation (Alloy, TLA+, etc.)
- **Layer 3** (Executable): Concrete tests, properties, monitors

### Data Model Changes

Add to `SpecNodeData`:
```rust
pub formality_layer: u8,  // 0=natural, 1=structured, 2=formal, 3=executable
pub formal_repr: Option<String>,  // Formal representation if layer > 0
pub executable: Option<String>,   // Executable code if layer == 3
```

Add new edge kind:
```rust
EdgeKind::Formalizes,  // Links natural spec to its formal version
```

### Layer Connections

Key insight: Layers are NOT hierarchical - they're different views of the same specification.

Connection pattern:
```
[Natural Layer 0] --formalizes--> [Formal Layer 2]
[Natural Layer 0] --formalizes--> [Executable Layer 3]
[Formal Layer 2] --formalizes--> [Executable Layer 3]
```

This creates a DAG where:
- Multiple formalizations can exist for one natural spec
- Consistency can be checked between layers
- Information loss in translation is explicit

### Implementation Steps

1. **Phase 1**: Add formality_layer field
   - Update SpecNodeData struct
   - Update proto definitions
   - Update service layer
   - Maintain backward compatibility (default to Layer 0)

2. **Phase 2**: Add formal_repr and executable fields
   - Optional fields for formal/executable content
   - Support multiple formal representations

3. **Phase 3**: Add Formalizes edge kind
   - Link specifications across layers
   - Enable cross-layer consistency checking

4. **Phase 4**: Layer-aware queries
   - Filter by formality level
   - Translate between layers (using AI)
   - Detect layer inconsistencies

## Constraints Compliance

- Minimal changes (add 3 fields + 1 edge kind)
- Behavior guaranteed through tests
- Utilize existing tools (LLMs for translation)
- No user questions
- No planning mode

## Next Steps

Start with Phase 1: Add formality_layer field.
