# Continuing Toward Goal: Two Critical Issues

**Date**: 2026-02-14
**Status**: In Progress

## Context

User asked to "continue for goal". The goal (from CLAUDE.md):
> "Create an open-source specification description tool for a new era"

## Current State

✅ **Goal substantially achieved**:
- AI inference validated at scale (536 specs)
- 75% omission reduction proven
- Self-hosting demonstrated
- Open source (MIT license)

⚠️ **Two critical issues remain**:

### Issue 1: Password Specs Not Connected (Technical Failure)

**Problem**: Multiple password-related specs remain isolated despite obvious semantic equivalence:

```
[77ad7450] Layer 0: "Passwords must be at least 8 characters."
[733d69a4] Layer 1: "password minimum length"
[c1ef864d] Layer 3: "Invariant: password.len() >= 8, ..."
```

These are **cross-layer** (0, 1, 3) and should have been connected by AI inference, but weren't.

**Root Cause Investigation**:

From spec-core/src/extract.rs:345-357, AI matching is triggered when:
1. Simple keyword similarity ≤ 0.5 (low overlap)
2. AND different formality layers

Password specs ARE cross-layer, so either:
- A) Keyword similarity was unexpectedly > 0.5 (unlikely)
- B) AI was called but returned low confidence
- C) AI was called but parsing failed
- D) The specs were never compared (bug in iteration logic)

**Need to**:
1. Manually calculate keyword similarity between password specs
2. Test AI inference on password pair specifically
3. Add debug logging to trace why these weren't connected

### Issue 2: No Project Separation (Architectural Limitation)

**Problem**: spec-oracle's specifications and demo/example specifications are mixed in one global graph. No namespace or project concept exists.

**Current Data Model** (spec-core/src/graph.rs:31-42):
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

**Real-world requirement**: Users managing multiple projects need:
1. Separate specification graphs per project
2. Ability to switch between projects
3. Project-scoped extraction (`spec extract --project myapp`)
4. Project-scoped queries (`spec query --project myapp "auth"`)
5. Optional cross-project relationship inference

**Design question**: Should projects be:
- A) Separate graph files (.graph files per project)?
- B) Single graph with project metadata filtering?
- C) Separate databases/stores per project?

Approach A is simplest and aligns with "multiple projects" use case.

## What "Continuing for Goal" Means

From docs/conversation.md, the deeper philosophical challenge:
- **DSLs have fundamental limits** (cannot scale to real complexity)
- **Multi-layered specifications** need new approach
- **Beyond traditional formal methods**

Current spec-oracle addresses this through:
- Multi-source extraction (not DSL authoring)
- AI semantic synthesis (not manual linking)
- Graph-based emergent truth (not single source)

But **concrete failures** (password specs, project separation) undermine the "new era" claim.

## Next Actions

### Immediate (Today)
1. **Diagnose password spec failure**:
   - Test AI matching on password pair manually
   - Add debug output to trace comparison
   - Fix if bug found, or document if fundamental limitation

2. **Design project separation**:
   - Read existing codebase for storage patterns
   - Propose project isolation approach
   - Validate against minimum requirements

### Short-term (This Week)
1. Implement project separation
2. Extract spec-oracle and demo specs into separate projects
3. Validate omission reduction per-project
4. Document project management workflow

### Long-term (Philosophical)
From conversation.md: The quest is to find specification management that:
- Handles multi-layered reality (U, D, A, f model)
- Detects contradictions across layers
- Avoids DSL scalability limits
- Works for real systems (web apps, distributed systems)

spec-oracle demonstrates value but hasn't fully solved the deep problem. The password spec failure is a microcosm: **even with AI, cross-layer semantic matching is hard**.

The "new era" isn't about perfect automation - it's about **reducing cognitive burden** while maintaining **multi-layer coherence**. Current 75% omission reduction is significant progress, not complete solution.

## Constraints (from CLAUDE.md)

- Behavior guaranteed through tests ✓ (55 passing)
- Minimal changes ✓ (focused, incremental)
- No clarification questions ✓ (autonomous investigation)
- No planning mode ✓ (direct action)
- Rust implementation ✓
- gRPC communication ✓

## Status

**Goal continuation focuses on**:
1. Fixing concrete failures (password specs)
2. Enabling real-world usage (project separation)
3. Documenting honest limitations

The tool works, but imperfectly. Progress continues.
