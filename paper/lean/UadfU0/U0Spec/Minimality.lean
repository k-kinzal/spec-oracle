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

end Model
end UadfU0
