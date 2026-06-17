VERDICT: NG

## (1) Blocking Issues

### 1.1 Scope Discipline Violation: May Semantics Out of Scope
**Location**: Lines 45–52, 79–83, 97–99, 104–115

**Issue**: The manuscript claims to formalize U0 construction from multi-layered defenses, but introduces `preimageMay`, `liftedMay`, `UAndMayOn` without **any theoretical justification** in the accompanying paper. The conversation history shows you repeatedly asked whether "undefined projection should reject or be inconclusive" — this is **fundamental semantics**, not an implementation detail.

**Evidence**:
- `preimageMay` (line 45): treats `proj i x = none` as "inconclusive" vs. must-style rejection
- `UAndMayOn` (line 104): global may-style meet
- Theorems 79–83, 108–115 relate must/may but **never explain when to use which**

**Why blocking**: The paper's Section 3 (U0 Construction) makes no mention of "may semantics". Either:
1. May-semantics is a core design choice → must be explained in paper
2. May-semantics is exploratory → delete from claimed formalization

**Fix**: Remove all `*May` definitions or add Section 3.4 "Operational Semantics Choice: Must vs May" with formal justification.

---

### 1.2 Omega Missing from Code
**Location**: Entire file

**Issue**: Paper promises "operationalized Ω through reverse mappings f₀ᵢ⁻¹" (Motivation §2), but:
- No definition of `Omega` type
- No reverse mapping `f₀ᵢ⁻¹` structure
- `proj : α → Option (carrier i)` is **forward partial map**, not reverse

**Expected**:
```lean
def Omega : SpecSet α := ...  -- root intent
def reverseMap (i : ι) : SpecSet α → SpecSet (carrier i) := ...
-- Correctness: proj preserves reverseMap
```

**Why blocking**: Paper's **entire narrative** is "specORACLE constructs U0 from artifacts via reverse mappings". Code shows only forward projections.

---

### 1.3 U0 vs U^wedge Semantics Confusion
**Location**: Lines 18–28, 95–127

**Issue**: The manuscript conflates two incompatible concepts:

1. **U0 (paper §3.1)**: Join-style root spec where "any layer suffices"
   ```lean
   def U0 : SpecSet α := fun x => ∃ i, x ∈ lifted i  -- line 18
   ```

2. **U^wedge (conversation)**: Meet-style integration where "all layers must hold"
   ```lean
   def UAnd : SpecSet α := fun x => ∀ i, x ∈ lifted i  -- line 99
   ```

**Evidence from conversation**:
- You asked: "Is U0 the join or meet of layers?"
- Answer evolved from "join by default" to "actually we need both"
- Paper §3.2 uses U0 notation exclusively

**Why blocking**: Readers will interpret U0 as meet-style (since multi-layered defense means "all must hold"), but code implements join-style. This is **silent semantic mismatch**.

**Fix**: Either:
- Rename `U0` → `U0_join` and make `UAnd` the primary U0, or
- Add paper §3.1.2 "Join vs Meet Semantics" explaining why join is chosen

---

## (2) Non-Blocking Improvements

### 2.1 Misleading Theorem Names
- `lifted_subset_U0` (line 134): Trivial by construction since U0 = ⋃ᵢ lifted(i)
- Better name: `layer_contributes_to_U0` (emphasizes design choice)

### 2.2 Missing Domain Coverage Lemma
The paper claims "U0 guarantees domain coverage across layers" (§4.2), but code only proves:
```lean
theorem U0_witness_projects_to_some_domain  -- line 141
```
Should add:
```lean
theorem U0_projects_to_all_active_domains (active : ι → Prop) :
  M.U0On active ⊆ (fun x => ∀ i, active i → ∃ y, M.proj i x = some y)
```

### 2.3 Projection Totality Unstated
Lines 6–11 define `proj : α → Option (carrier i)` but never state when `proj` returns `some` vs `none`. Add:
```lean
-- Intended: proj i x = some y ↔ x "observably constrains layer i"
-- Operational: none = "artifact silent on layer i" (may-style)
--              none = "artifact violates layer i" (must-style)
```

---

## (3) Final Recommendation

**Action**: **Reject pending major revision** to manuscript + code synchronization.

**Required changes**:
1. **Paper §3.4**: Add "Operational Semantics" subsection explaining:
   - Why `proj : α → Option` vs total map
   - Must vs may interpretation of `none`
   - When to use join (U0) vs meet (UAnd) root spec

2. **Code**: Either remove all `*May` artifacts OR prove equivalence:
   ```lean
   theorem may_collapses_under_totality (hTotal : ∀ i x, ∃ y, M.proj i x = some y) :
     M.liftedMay i = M.lifted i
   ```

3. **Omega formalization**: Add reverse mapping structure or remove Ω from paper narrative

**Estimated effort**: 2–3 days to align theory/implementation

**Core concern**: The manuscript sells a **"reverse mapping engine that constructs U0 from diverse artifacts"**, but the formalization shows a **forward projection model with unexplained may-semantics**. This gap undermines the paper's central contribution claim.
