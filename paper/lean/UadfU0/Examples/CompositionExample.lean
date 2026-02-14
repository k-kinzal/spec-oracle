import UadfU0.InterLayer.Composition

namespace UadfU0
namespace Examples

open Model

abbrev compositionModel : Model Bool Nat where
  carrier
  | true => Nat
  | false => Bool
  layer
  | true =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n ≥ 1
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | false =>
      {
        D := fun _ : Bool => True
        A := fun b : Bool => b = true
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj
  | true, x => some x
  | false, x => if x % 2 = 0 then some true else some false

def gParity : compositionModel.carrier true → Option (compositionModel.carrier false) :=
  fun n => if n % 2 = 0 then some true else some false

theorem proj_compose_holds :
    ∀ x : Nat, compositionModel.proj false x = Option.bind (compositionModel.proj true x) gParity := by
  intro x
  simp [compositionModel, gParity]

example (S : SpecSet (compositionModel.carrier false)) :
    compositionModel.preimage false S =
      compositionModel.preimage true (compositionModel.pullbackVia gParity S) := by
  exact Model.preimage_compose (M := compositionModel) true false gParity proj_compose_holds S

end Examples
end UadfU0
