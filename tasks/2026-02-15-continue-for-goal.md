# Task: Continue for Goal - Realizing specORACLE's Core Concept

Date: 2026-02-15
Session: Current

## Context

User request: "please continue for goal"

From CLAUDE.md:
> "The goal has not been reached. Have you realized the core concept? Face the essence of specORACLE; the issues that should be resolved with specORACLE have not been addressed yet."

> "specORACLE is a reverse mapping engine. It does not manage specifications written by humans. It constructs U0 (the root specification) from diverse artifacts through reverse mappings"

## Current State

### ✅ Achievements
1. **CLI UX dramatically improved**:
   - `spec get-node <short-id>` - inspect specs without jq
   - Short ID support (8 chars) for all commands
   - Standalone mode works seamlessly
   - Relationships displayed clearly

2. **Quality filtering enhanced**:
   - Rejects Rust code in Invariant specs (`.iter()`, `.any()`, etc.)
   - Stricter length requirements (25 chars minimum)
   - Stronger semantic keywords
   - Applied in both extraction and cleanup

3. **Data quality improved**:
   - Removed 46 low-quality specs (Rust code, trivial names)
   - 0 contradictions
   - 295 total specs (down from 317)

### ⚠️  Current Issues
1. **36 isolated specifications** (U3 test scenarios):
   - Examples: "detect inter universe inconsistencies missing transform"
   - These ARE high-quality, descriptive test scenarios
   - Problem: No corresponding U0 requirements

2. **Reverse mapping not working as intended**:
   - `construct-u0` re-extracts from code (U3 → U3)
   - It does NOT infer U0 from U3 (U3 → U0 via f₀₃⁻¹)
   - Isolated U3 specs exist but aren't mapped back to U0

## The Core Problem

### What We Have
- U3 specifications extracted from tests (e.g., "detect inter universe inconsistencies")
- These are good, meaningful test scenarios
- They describe WHAT the system does

### What We're Missing
- U0 specifications inferred from U3
- E.g., U3: "Scenario: detect inter universe inconsistencies missing transform"
  → U0: "The system must detect inter-universe inconsistencies when transforms are missing"

### Why This Matters (from motivation.md)
> "spec/specdの役割：統制を保つ基準"
> "多層防御の統制は、各層からの逆写像により実現される"

The reverse mapping engine should:
1. Extract U3 (tests, code) ✅ DONE
2. Infer U0 from U3 via f₀₃⁻¹ ❌ NOT WORKING
3. Connect U3 → U0 via formalizes edges ❌ NOT WORKING
4. Govern multi-layered defenses through U0 ❌ INCOMPLETE

## Technical Analysis

### Current `construct_u0` Behavior
```rust
// udaf.rs:405-426
pub fn construct_u0(&mut self, graph: &SpecGraph) -> Result<Vec<InferredSpecification>, String> {
    // For each projection universe (U1, U2, U3...)
    for (universe_id, universe) in &self.universes {
        if universe.layer == 0 { continue; }

        // Find the inverse transform
        let inverse_transform_id = format!("f_{}_to_U0", universe_id);

        if let Some(transform) = self.transforms.get(&inverse_transform_id) {
            // Execute the transform strategy to extract/map specifications
            let extracted_specs = self.execute_transform(transform, graph)?;
            // ↑ This calls ASTAnalysis, which re-extracts from code
            // It does NOT infer U0 from existing U3 specs
        }
    }
}
```

### What We Need
```rust
// Pseudo-code for true reverse mapping
fn infer_u0_from_u3(u3_spec: &SpecNode) -> Option<SpecNode> {
    // Given U3: "Scenario: detect inter universe inconsistencies missing transform"
    // Infer U0: "The system must detect inter-universe inconsistencies when transforms are missing"

    // Extract semantic intent from test scenario
    let intent = extract_requirement_from_test(&u3_spec.content);

    // Create U0 specification
    let u0_spec = SpecNode {
        content: intent,
        kind: NodeKind::Constraint,  // Requirements are constraints
        formality_layer: 0,  // U0
        metadata: {
            "inferred_from": u3_spec.id,
            "confidence": calculate_confidence(&intent),
        }
    };

    // Create formalizes edge: U0 → U3
    create_edge(u0_spec.id, u3_spec.id, EdgeKind::Formalizes);

    Some(u0_spec)
}
```

## Path Forward

### Option 1: Implement True Reverse Mapping (Ideal)
1. Create `infer_u0_from_u3()` function
2. For each isolated U3 spec:
   - Extract requirement intent (e.g., "must detect..." from "Scenario: detect...")
   - Create corresponding U0 constraint
   - Connect via formalizes edge
3. This realizes the true f₀₃⁻¹ transform

**Pros**: Realizes core concept, addresses motivation
**Cons**: Complex NLP/AI task to infer requirements from tests

### Option 2: Manual U0 Curation with Assistance (Pragmatic)
1. For each isolated U3 spec, suggest U0 requirement:
   ```
   $ spec suggest-u0 bf3a465a
   U3: "Scenario: detect inter universe inconsistencies missing transform"

   Suggested U0 requirement:
   "The system must detect inter-universe inconsistencies when transforms are missing"

   Accept? (y/n/edit):
   ```
2. User confirms or edits
3. System creates U0 spec and formalizes edge

**Pros**: Practical, achieves governance goal
**Cons**: Requires human input (contradicts "not manage specifications written by humans")

### Option 3: AI-Enhanced Reverse Mapping (Middle Ground)
1. Use AI (claude/codex) to infer U0 from U3
2. Apply confidence threshold
3. Auto-create high-confidence U0 specs
4. Suggest low-confidence ones for review

**Pros**: Balanced, leverages AI, maintains automation
**Cons**: Requires AI CLI integration

## Immediate Next Steps

1. **Analyze isolated specs** to understand patterns:
   ```bash
   spec list-nodes --kind Scenario | grep "detect\|verify\|ensure"
   ```

2. **Prototype requirement extraction**:
   - Test: "detect inter universe inconsistencies"
   - Requirement: "must detect inter-universe inconsistencies"
   - Pattern: test_<action>_<object> → "must <action> <object>"

3. **Implement basic f₀₃⁻¹**:
   - Simple pattern-based inference
   - Create U0 specs for isolated U3 scenarios
   - Verify with `spec check`

4. **Dogfood the result**:
   - Does U0 now govern the multi-layered defenses?
   - Can we detect omissions/contradictions across layers?
   - Does this realize the core concept?

## Success Criteria

From PROBLEM.md constraints:
- [x] Behavior guaranteed by multiple layers (tests exist)
- [x] Specifications managed using our tool (specs in .spec/)
- [ ] **Issues in PROBLEM.md resolved** (36 isolated specs remain)
- [ ] **Core concept realized** (reverse mapping U3 → U0)

From motivation.md:
- [ ] "根の部分の仕様の荒めの写像" exists (U0 constructed from U3)
- [ ] "多層防御の統制" achieved (U0 governs U3)
- [ ] "矛盾と漏れの可視化" works across layers

## Conclusion

The immediate goal is clear:
**Implement reverse mapping from U3 to U0 (f₀₃⁻¹) to connect isolated test scenarios to root requirements.**

This is the essence of specORACLE - not managing human-written specs, but **constructing U0 from diverse artifacts through reverse mappings**.

---
Status: IN PROGRESS
Next action: Implement basic pattern-based U0 inference from isolated U3 scenarios
