import UadfU0.Definitions.Model

namespace UadfU0
namespace Model

universe u v

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Expand membership of an induced inverse image. -/
theorem mem_preimage_iff (i : ι) (S : SpecSet α) (x : α) :
    x ∈ M.preimage i S ↔ ∃ y : α, M.proj i x = some y ∧ y ∈ S := Iff.rfl

/-- Inverse images induced by `proj` are monotone. -/
theorem preimage_monotone (i : ι) {S T : SpecSet α}
    (hST : S ⊆ T) :
    M.preimage i S ⊆ M.preimage i T := by
  intro x hx
  rcases hx with ⟨y, hproj, hyS⟩
  exact ⟨y, hproj, hST hyS⟩

/-- Inverse image preserves binary unions. -/
theorem preimage_union (i : ι) (S T : SpecSet α) :
    M.preimage i (S ∪ₛ T) = M.preimage i S ∪ₛ M.preimage i T := by
  apply set_ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨y, hproj, hyST⟩
    cases hyST with
    | inl hyS =>
        exact Or.inl ⟨y, hproj, hyS⟩
    | inr hyT =>
        exact Or.inr ⟨y, hproj, hyT⟩
  · intro hx
    cases hx with
    | inl hxS =>
        rcases hxS with ⟨y, hproj, hyS⟩
        exact ⟨y, hproj, Or.inl hyS⟩
    | inr hxT =>
        rcases hxT with ⟨y, hproj, hyT⟩
        exact ⟨y, hproj, Or.inr hyT⟩

/-- Membership in U0 is exactly membership in some lifted layer. -/
theorem mem_U0_iff (x : α) :
    x ∈ M.U0 ↔ ∃ i : ι, x ∈ M.lifted i := Iff.rfl

/-- Every lifted layer contributes directly to U0. -/
theorem lifted_subset_U0 (i : ι) :
    M.lifted i ⊆ M.U0 := by
  intro x hx
  exact ⟨i, hx⟩

/-- If any lifted layer has a witness, U0 is non-empty. -/
theorem U0_nonempty_of_exists_layer_nonempty
    (h : ∃ i : ι, ∃ x : α, x ∈ M.lifted i) :
    ∃ x : α, x ∈ M.U0 := by
  rcases h with ⟨i, x, hx⟩
  exact ⟨x, ⟨i, hx⟩⟩

end Model
end UadfU0
