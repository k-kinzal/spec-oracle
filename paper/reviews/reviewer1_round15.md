# VERDICT: NG

## 1. Blocking Issues

### Critical Semantic Contradiction: U₀ Definition vs. U^wedge Treatment

**Location**: `paper/manuscript/uadf_u0_spec_proof.md` vs. `paper/lean/UadfU0/Definitions/Model.lean:62-63`

**Issue**: The manuscript conflates two distinct semantic objects:

1. **U₀ (Root Coverage Specification)** - Lean definition line 62:
   ```lean
   def U0 (M : Model ι α) : SpecSet α :=
     fun x : α => ∃ i : ι, x ∈ M.lifted i
   ```
   This is the **union of all lifted admissible sets** - a specification object in root space that defines what implementations must cover.

2. **U^wedge (Diagnostic Operator)** - What the manuscript describes as "detecting contradictions":
   The manuscript treats U₀ as if it performs contradiction detection ("inherits contradictory requirements", "when layers disagree"), but this is **semantically incorrect**.

**Contradiction**: The Lean definition shows U₀ is a **union operation** (∃ i, membership). A union **cannot detect contradictions** - it only aggregates coverage. The manuscript's treatment requires an **intersection-based diagnostic operator** U^wedge, which is not present in the Lean model.

**Evidence from Lean**:
- Line 65-67: `Contradictory` is defined as a **separate predicate** on layer pairs, not a property of U₀
- Line 70-71: `Consistent` is also a **separate layer-pair relation**
- The model provides no mechanism for U₀ to "inherit" or "detect" contradictions

**Required Fix**: The manuscript must explicitly separate:
```
U₀ = ⋃ᵢ f₀ᵢ⁻¹(Uᵢ)     -- Root coverage spec (union)
U^wedge = ⋂ᵢ f₀ᵢ⁻¹(Uᵢ)  -- Diagnostic operator (intersection)
```

And state: "U₀ defines required coverage. When U^wedge = ∅ₛ, contradictions exist between layers. U₀ semantics are independent of contradiction status."

---

### must/may Treatment Inconsistency

**Location**: `paper/lean/UadfU0/U0Spec/Construction.lean:147-154` vs. manuscript's treatment of "should"

**Issue**: The Lean proof explicitly handles must/may modalities:

```lean
theorem must_spec_stability (M : Model ι α) (i : ι) :
  ∀ x : α, x ∈ M.lifted i → x ∈ M.U0

theorem may_spec_flexibility (M : Model ι α) (i : ι) :
  ∀ x : α, x ∈ M.U0 → ∃ j : ι, x ∈ M.lifted j
```

But the manuscript uses "should" without clarifying whether this is:
- A **must-spec** (definitive requirement, Construction.lean:147)
- A **may-spec** (permitted but not required, Construction.lean:151)
- Something outside the formal model entirely

**Example**: "system should support password recovery" - is this must or may?

**Required Fix**: Either:
1. Replace all "should" with "must" (definitive requirements only)
2. Or add explicit may-spec notation and prove it aligns with Construction.lean:151-154

---

## 2. Non-Blocking Improvements

1. **Notation Clarity**: Use U₀ vs U⁰ consistently (currently mixed)
2. **f₀ᵢ⁻¹ Explanation**: Add one sentence: "f₀ᵢ⁻¹ is realized by `Model.preimage` (Model.lean:57)"
3. **Layer Carrier Types**: Briefly note that βᵢ types differ per layer (not obvious from manuscript alone)

---

## 3. Final Recommendation

**Status**: VERDICT: NG

**Blocking**: The U₀/U^wedge conflation is a fundamental semantic error that invalidates the manuscript's core claim about "detecting contradictions through U₀". The current Lean model **does not support** this claim.

**Path Forward**:
1. Add U^wedge operator to Lean model (intersection-based)
2. Prove properties about when U^wedge = ∅ₛ
3. Rewrite manuscript sections to clearly separate:
   - U₀ = coverage specification (what implementations must provide)
   - U^wedge = diagnostic tool (detects layer conflicts)
4. Resolve must/may ambiguity by mapping "should" to formal modalities

**Estimated Scope**: 2-3 hours for Lean additions, 1 hour for manuscript rewrite.

**Resubmission**: Ready for re-review once U^wedge is formalized and manuscript clearly distinguishes coverage (U₀) from diagnostics (U^wedge).
