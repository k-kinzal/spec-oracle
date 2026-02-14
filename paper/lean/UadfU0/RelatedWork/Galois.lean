import UadfU0.Definitions.Model

namespace UadfU0
namespace Model

universe u v w

/-- Universal set over predicate-based set encoding. -/
def sUniv {α : Type v} : SpecSet α :=
  fun _ => True

/-- G has a left adjoint F on predicate sets if F S ⊆ T ↔ S ⊆ G T. -/
def HasLeftAdjoint
    {α : Type v}
    {β : Type w}
    (G : SpecSet β → SpecSet α) : Prop :=
  ∃ F : SpecSet α → SpecSet β, ∀ S T, F S ⊆ T ↔ S ⊆ G T

/--
If projection is undefined at some root witness, existential preimage cannot
be a right adjoint on full powersets.
-/
theorem no_left_adjoint_of_partial
    {ι : Type u}
    {α : Type v}
    (M : Model ι α)
    (i : ι)
    (x0 : α)
    (hnone : M.proj i x0 = none) :
    ¬ HasLeftAdjoint (M.preimage i) := by
  intro hAdj
  rcases hAdj with ⟨F, hGC⟩
  let S : SpecSet α := fun x => x = x0
  let T : SpecSet (M.carrier i) := sUniv
  have hLeft : F S ⊆ T := by
    intro y hy
    trivial
  have hRight : S ⊆ M.preimage i T := (hGC S T).1 hLeft
  have hxInS : x0 ∈ S := by
    show x0 = x0
    rfl
  have hxInPre : x0 ∈ M.preimage i T := hRight hxInS
  rcases hxInPre with ⟨y, hproj, _hyInT⟩
  have hproj' : M.proj i x0 = some y := hproj
  simp [hnone] at hproj'

/-- Concrete one-layer model with an undefined projection point. -/
abbrev partialProjectionModel : Model Unit Nat where
  carrier := fun _ => Nat
  layer _ :=
    {
      D := fun _ : Nat => True
      A := fun _ : Nat => True
      admissible_subset_domain := by
        intro x hx
        trivial
    }
  proj _ x := if x = 0 then none else some x

example : ¬ HasLeftAdjoint (partialProjectionModel.preimage ()) := by
  refine no_left_adjoint_of_partial (M := partialProjectionModel) () 0 ?hnone
  simp [partialProjectionModel]

end Model
end UadfU0
