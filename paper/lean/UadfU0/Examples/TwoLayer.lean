import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Examples

open Model

def twoLayerModel : Model Bool Nat where
  Ui
  | true => {n | n ≥ 1}
  | false => {n | n % 2 = 0}
  inv _ S := S

example : 2 ∈ twoLayerModel.U0 := by
  refine ⟨true, ?_⟩
  decide

example : 0 ∈ twoLayerModel.U0 := by
  refine ⟨false, ?_⟩
  decide

example : twoLayerModel.Consistent true false := by
  refine ⟨2, ?_, ?_⟩
  · decide
  · decide

example : ¬ twoLayerModel.Contradictory true false := by
  intro hContra
  have hCons : twoLayerModel.Consistent true false := by
    refine ⟨2, ?_, ?_⟩
    · decide
    · decide
  exact (Model.contradictory_iff_not_consistent (M := twoLayerModel) true false).1 hContra hCons

end Examples
end UadfU0
