import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- U0 is an upper bound of all lifted layers. -/
theorem U0_upper_bound (i : ι) :
    M.lifted i ⊆ M.U0 :=
  M.lifted_subset_U0 i

/-- Least-upper-bound property of U0 over inverse-image family. -/
theorem U0_least_upper_bound_iff (B : Set α) :
    (∀ i : ι, M.lifted i ⊆ B) ↔ M.U0 ⊆ B := by
  constructor
  · intro h x hx
    rcases hx with ⟨i, hxi⟩
    exact h i hxi
  · intro h i x hx
    exact h (show x ∈ M.U0 from ⟨i, hx⟩)

/-- Set-extensional form of the U0 specification equation. -/
theorem U0_eq_union_schema (B : Set α)
    (h1 : ∀ i : ι, M.lifted i ⊆ B)
    (h2 : B ⊆ M.U0) :
    M.U0 = B := by
  apply Set.Subset.antisymm
  · exact (M.U0_least_upper_bound_iff B).1 h1
  · exact h2

end Model
end UadfU0
