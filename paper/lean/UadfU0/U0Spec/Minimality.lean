import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- U0 is an upper bound of all lifted layers. -/
theorem U0_upper_bound (i : ι) :
    M.lifted i ⊆ M.U0 :=
  M.lifted_subset_U0 i

/-- If `B` is an upper bound of all lifted layers, then `U0 ⊆ B`. -/
theorem U0_below_every_upper_bound (B : SpecSet α)
    (hB : ∀ i : ι, M.lifted i ⊆ B) :
    M.U0 ⊆ B := by
  intro x hx
  rcases hx with ⟨i, hxi⟩
  exact hB i hxi

/-- Characterization of upper bounds through `U0`. -/
theorem U0_least_upper_bound_iff (B : SpecSet α) :
    (∀ i : ι, M.lifted i ⊆ B) ↔ M.U0 ⊆ B := by
  constructor
  · intro h
    exact M.U0_below_every_upper_bound B h
  · intro h i x hx
    exact h (show x ∈ M.U0 from ⟨i, hx⟩)

/-- Supremum-style statement in the subset order. -/
theorem U0_is_supremum :
    (∀ i : ι, M.lifted i ⊆ M.U0) ∧
    (∀ B : SpecSet α, (∀ i : ι, M.lifted i ⊆ B) → M.U0 ⊆ B) := by
  constructor
  · intro i
    exact M.U0_upper_bound i
  · intro B hB
    exact M.U0_below_every_upper_bound B hB

/-- Meet-style integrated spec is a lower bound for each active layer. -/
theorem UAndOn_lower_bound
    (active : ι → Prop)
    (i : ι)
    (hi : active i) :
    M.UAndOn active ⊆ M.lifted i := by
  intro x hx
  exact hx i hi

/-- Any common lower bound of active lifted layers is below the meet-style spec. -/
theorem below_UAndOn_of_lower_bounds
    (active : ι → Prop)
    (B : SpecSet α)
    (hB : ∀ i : ι, active i → B ⊆ M.lifted i) :
    B ⊆ M.UAndOn active := by
  intro x hxB i hi
  exact hB i hi hxB

/-- Greatest-lower-bound characterization for meet-style integrated spec. -/
theorem UAndOn_greatest_lower_bound_iff
    (active : ι → Prop)
    (B : SpecSet α) :
    (B ⊆ M.UAndOn active) ↔ (∀ i : ι, active i → B ⊆ M.lifted i) := by
  constructor
  · intro h i hi x hx
    exact (h hx) i hi
  · intro h
    exact M.below_UAndOn_of_lower_bounds active B h

end Model
end UadfU0
