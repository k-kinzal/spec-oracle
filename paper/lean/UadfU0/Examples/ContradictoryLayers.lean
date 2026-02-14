import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Examples

open Model

def contradictoryModel : Model Bool Nat where
  Ui
  | true => fun n => n = 0
  | false => fun n => n = 1
  proj _ x := some x

theorem contradictoryModel_is_contradictory :
    contradictoryModel.Contradictory true false := by
  intro x hx0 hx1
  rcases hx0 with ⟨y0, hy0, hyEq0⟩
  rcases hx1 with ⟨y1, hy1, hyEq1⟩
  have hy0x : y0 = x := by
    exact Option.some.inj hy0
  have hy1x : y1 = x := by
    exact Option.some.inj hy1
  have hxEq0 : x = 0 := by
    simpa [hy0x] using hyEq0
  have hxEq1 : x = 1 := by
    simpa [hy1x] using hyEq1
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
