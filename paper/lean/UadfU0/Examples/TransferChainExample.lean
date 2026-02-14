import UadfU0.InterLayer.Transfer

namespace UadfU0
namespace Examples

open Model

inductive ChainIx where
  | req
  | api
  | code
deriving DecidableEq, Repr

abbrev transferChainModel : Model ChainIx Nat where
  carrier := fun _ => Nat
  layer
  | .req =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n >= 1
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | .api =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n >= 3
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | .code =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n >= 5
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj _ x := some x

def eqRel (x y : Nat) : Prop := x = y

theorem transfer_code_to_api :
    transferChainModel.lifted .code ⊆ transferChainModel.lifted .api := by
  refine Model.lifted_transfer (M := transferChainModel) .api .code eqRel ?hproj ?hA
  · intro x yj hproj
    exact ⟨yj, by simpa [transferChainModel] using hproj, rfl⟩
  · intro yi yj hRel hyjA
    have hyi_eq_yj : yi = yj := by
      simpa [eqRel] using hRel
    have hyi_ge_five : yi >= 5 := by
      simpa [hyi_eq_yj] using hyjA
    exact Nat.le_trans (by decide : 3 <= 5) hyi_ge_five

theorem transfer_api_to_req :
    transferChainModel.lifted .api ⊆ transferChainModel.lifted .req := by
  refine Model.lifted_transfer (M := transferChainModel) .req .api eqRel ?hproj ?hA
  · intro x yj hproj
    exact ⟨yj, by simpa [transferChainModel] using hproj, rfl⟩
  · intro yi yj hRel hyjA
    have hyi_eq_yj : yi = yj := by
      simpa [eqRel] using hRel
    have hyi_ge_three : yi >= 3 := by
      simpa [hyi_eq_yj] using hyjA
    exact Nat.le_trans (by decide : 1 <= 3) hyi_ge_three

example :
    transferChainModel.lifted .code ⊆ transferChainModel.lifted .req := by
  intro x hxCode
  exact transfer_api_to_req (transfer_code_to_api hxCode)

end Examples
end UadfU0
