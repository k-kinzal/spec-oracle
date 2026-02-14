import UadfU0.InterLayer.Transfer

namespace UadfU0
namespace Examples

open Model

abbrev transferModel : Model Bool Nat where
  carrier := fun _ => Nat
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
        D := fun _ : Nat => True
        A := fun n : Nat => n ≥ 2
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj _ x := some x

theorem transfer_false_to_true :
    transferModel.lifted false ⊆ transferModel.lifted true := by
  refine Model.lifted_transfer (M := transferModel) true false (fun yi yj => yi = yj) ?hproj ?hA
  · intro x yj hproj
    exact ⟨yj, by simpa [transferModel] using hproj, rfl⟩
  · intro yi yj hEq hyjA
    have hyj_ge_two : yj ≥ 2 := hyjA
    have hyi_ge_two : yi ≥ 2 := by simpa [hEq] using hyj_ge_two
    exact Nat.le_trans (by decide : 1 ≤ 2) hyi_ge_two

example :
    transferModel.Consistent false false → transferModel.Consistent true false := by
  intro hCons
  exact Model.consistent_transport_left (M := transferModel) true false false transfer_false_to_true hCons

end Examples
end UadfU0
