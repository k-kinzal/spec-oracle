import UadfU0.InterLayer.Transfer

namespace UadfU0
namespace Examples

open Model

def isEven (n : Nat) : Bool :=
  n % 2 == 0

inductive HLayer where
  | natL
  | boolL
deriving DecidableEq

abbrev heteroTransferModel : Model HLayer Nat where
  carrier
  | .natL => Nat
  | .boolL => Bool
  layer
  | .natL =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => isEven n = true
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | .boolL =>
      {
        D := fun _ : Bool => True
        A := fun b : Bool => b = true
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj
  | .natL, x => some x
  | .boolL, x => some (isEven x)

def natBoolRel (n : heteroTransferModel.carrier .natL) (b : heteroTransferModel.carrier .boolL) : Prop :=
  b = isEven n

theorem heterogeneous_lifted_transfer :
    heteroTransferModel.lifted .boolL ⊆ heteroTransferModel.lifted .natL := by
  refine Model.lifted_transfer (M := heteroTransferModel) .natL .boolL natBoolRel ?hproj ?hA
  · intro x yb hProjBool
    refine ⟨x, by simp [heteroTransferModel], ?_⟩
    unfold natBoolRel
    have hyb : yb = isEven x := by
      simpa [heteroTransferModel, isEven] using hProjBool.symm
    simp [hyb]
  · intro yi yb hRel hybA
    unfold natBoolRel at hRel
    have hEven : isEven yi = true := by
      simpa [hRel] using hybA
    simpa [heteroTransferModel] using hEven

end Examples
end UadfU0
