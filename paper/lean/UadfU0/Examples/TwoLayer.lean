import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Examples

open Model

def twoLayerModel : Model Bool Nat where
  Ui
  | true => fun n => n ≥ 1
  | false => fun n => n % 2 = 0
  proj _ x := some x

example : 2 ∈ twoLayerModel.U0 := by
  refine ⟨true, ?_⟩
  refine ⟨2, rfl, ?_⟩
  decide

example : 0 ∈ twoLayerModel.U0 := by
  refine ⟨false, ?_⟩
  refine ⟨0, rfl, ?_⟩
  decide

example : twoLayerModel.Consistent true false := by
  refine ⟨2, ?_, ?_⟩
  · exact ⟨2, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩

example : ¬ twoLayerModel.Contradictory true false := by
  intro hContra
  have hCons : twoLayerModel.Consistent true false := by
    refine ⟨2, ?_, ?_⟩
    · exact ⟨2, rfl, by decide⟩
    · exact ⟨2, rfl, by decide⟩
  exact (Model.contradictory_iff_not_consistent (M := twoLayerModel) true false).1 hContra hCons

end Examples
end UadfU0
