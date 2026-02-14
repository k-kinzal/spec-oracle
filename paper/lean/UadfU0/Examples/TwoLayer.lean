import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Examples

open Model

abbrev twoLayerTypedModel : Model Bool Nat where
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

example : 2 ∈ twoLayerTypedModel.U0 := by
  refine ⟨true, ?_⟩
  refine ⟨2, rfl, ?_⟩
  change 2 ≥ 1
  decide

example : 2 ∈ twoLayerTypedModel.UAnd := by
  intro i hi
  cases i with
  | false =>
      refine ⟨true, ?_, rfl⟩
      simp [twoLayerTypedModel]
  | true =>
      refine ⟨2, rfl, ?_⟩
      change 2 ≥ 1
      decide

example : 0 ∈ twoLayerTypedModel.U0 := by
  refine ⟨false, ?_⟩
  refine ⟨true, ?_, rfl⟩
  simp [twoLayerTypedModel]

example : twoLayerTypedModel.Consistent true false := by
  refine ⟨2, ?_, ?_⟩
  · refine ⟨2, rfl, ?_⟩
    change 2 ≥ 1
    decide
  · refine ⟨true, ?_, rfl⟩
    simp [twoLayerTypedModel]

example : ¬ twoLayerTypedModel.Contradictory true false := by
  intro hContra
  have hCons : twoLayerTypedModel.Consistent true false := by
    refine ⟨2, ?_, ?_⟩
    · refine ⟨2, rfl, ?_⟩
      change 2 ≥ 1
      decide
    · refine ⟨true, ?_, rfl⟩
      simp [twoLayerTypedModel]
  exact (Model.contradictory_iff_not_consistent (M := twoLayerTypedModel) true false).1 hContra hCons

example : twoLayerTypedModel.UAnd ⊆ twoLayerTypedModel.U0 := by
  have hsub :
      twoLayerTypedModel.UAndOn (fun _ : Bool => True) ⊆
        twoLayerTypedModel.U0On (fun _ : Bool => True) :=
    Model.UAndOn_subset_U0On (M := twoLayerTypedModel) (active := fun _ : Bool => True) ⟨true, trivial⟩
  intro x hx
  have hxAndOn : x ∈ twoLayerTypedModel.UAndOn (fun _ : Bool => True) := by
    simpa [Model.UAnd_eq_UAndOn_all (M := twoLayerTypedModel)] using hx
  have hxU0On : x ∈ twoLayerTypedModel.U0On (fun _ : Bool => True) := hsub hxAndOn
  simpa [Model.U0_eq_U0On_all (M := twoLayerTypedModel)] using hxU0On

end Examples
end UadfU0
