import UadfU0.Definitions.Model

namespace UadfU0
namespace Model

universe u v

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Membership in U0 is exactly membership in some inverse image. -/
theorem mem_U0_iff (x : α) :
    x ∈ M.U0 ↔ ∃ i : ι, x ∈ M.lifted i := Iff.rfl

/-- Every inverse image contributes directly to U0. -/
theorem lifted_subset_U0 (i : ι) :
    M.lifted i ⊆ M.U0 := by
  intro x hx
  exact ⟨i, hx⟩

/-- If any layer has at least one witness, U0 is non-empty. -/
theorem U0_nonempty_of_exists_layer_nonempty
    (h : ∃ i : ι, ∃ x : α, x ∈ M.lifted i) :
    ∃ x : α, x ∈ M.U0 := by
  rcases h with ⟨i, x, hx⟩
  exact ⟨x, ⟨i, hx⟩⟩

end Model
end UadfU0
