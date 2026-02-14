import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Semantic pullback induced by an explicit extraction relation. -/
def semanticPullback
    {i : ι}
    (E : α → M.carrier i → Prop)
    (S : SpecSet (M.carrier i)) :
    SpecSet α :=
  fun x => ∃ y : M.carrier i, E x y ∧ y ∈ S

/--
Adequacy transfer theorem.

If partial projection and extraction relation are pointwise equivalent,
the induced inverse image equals semantic pullback.
-/
theorem preimage_eq_semanticPullback
    (i : ι)
    (E : α → M.carrier i → Prop)
    (hEq : ∀ x : α, ∀ y : M.carrier i, M.proj i x = some y ↔ E x y)
    (S : SpecSet (M.carrier i)) :
    M.preimage i S = M.semanticPullback E S := by
  apply set_ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨y, hproj, hyS⟩
    exact ⟨y, (hEq x y).1 hproj, hyS⟩
  · intro hx
    rcases hx with ⟨y, hExy, hyS⟩
    exact ⟨y, (hEq x y).2 hExy, hyS⟩

end Model
end UadfU0
