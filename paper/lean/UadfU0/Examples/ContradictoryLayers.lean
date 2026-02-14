import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Examples

open Model

abbrev contradictoryModel : Model Bool Nat where
  carrier := fun _ => Nat
  layer
  | true =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n = 0
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | false =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n = 1
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj _ x := some x

theorem contradictoryModel_is_contradictory :
    contradictoryModel.Contradictory true false := by
  intro x hx0 hx1
  rcases hx0 with ⟨y0, hy0, hyEq0⟩
  rcases hx1 with ⟨y1, hy1, hyEq1⟩
  have hx_y0 : x = y0 := by
    simpa [contradictoryModel] using hy0
  have hx_y1 : x = y1 := by
    simpa [contradictoryModel] using hy1
  have hxEq0 : x = 0 := by
    calc
      x = y0 := hx_y0
      _ = 0 := hyEq0
  have hxEq1 : x = 1 := by
    calc
      x = y1 := hx_y1
      _ = 1 := hyEq1
  have h01 : (0 : Nat) = 1 := by
    calc
      0 = x := hxEq0.symm
      _ = 1 := hxEq1
  exact Nat.zero_ne_one h01

example : ¬ contradictoryModel.Consistent true false :=
  (Model.contradictory_iff_not_consistent (M := contradictoryModel) true false).1
    contradictoryModel_is_contradictory

end Examples
end UadfU0
