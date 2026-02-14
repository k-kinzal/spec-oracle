import UadfU0.U0Spec.Minimality

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Contradiction is equivalent to absence of a common witness. -/
theorem contradictory_iff_not_consistent (i j : ι) :
    M.Contradictory i j ↔ ¬ M.Consistent i j := by
  constructor
  · intro hContra hCons
    rcases hCons with ⟨x, hxi, hxj⟩
    exact hContra x hxi hxj
  · intro hNot x hxi hxj
    exact hNot ⟨x, hxi, hxj⟩

/-- A consistent pair guarantees that U0 is non-empty. -/
theorem consistent_implies_U0_nonempty (i j : ι)
    (h : M.Consistent i j) :
    ∃ x : α, x ∈ M.U0 := by
  rcases h with ⟨x, hxi, _⟩
  exact ⟨x, ⟨i, hxi⟩⟩

/-- If two layers are contradictory, they cannot share a witness. -/
theorem contradictory_implies_no_shared_witness (i j : ι)
    (h : M.Contradictory i j) :
    ¬ ∃ x : α, x ∈ M.lifted i ∧ x ∈ M.lifted j := by
  intro hx
  rcases hx with ⟨x, hxi, hxj⟩
  exact h x hxi hxj

end Model
end UadfU0
