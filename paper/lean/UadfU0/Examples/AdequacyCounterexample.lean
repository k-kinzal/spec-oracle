import UadfU0.InterLayer.Adequacy

namespace UadfU0
namespace Examples

open Model

/--
Single-layer model used to show that one-sided adequacy is non-trivial
when `E` is intentionally different from projection equality.
-/
abbrev oneLayerNatModel : Model Unit Nat where
  carrier := fun _ => Nat
  layer := fun _ =>
    {
      D := fun _ : Nat => True
      A := fun _ : Nat => True
      admissible_subset_domain := by
        intro _ _
        trivial
    }
  proj := fun _ x => some x

def onlyOne : Unit := ()

/--
`EPlus1` is strictly weaker than projection equality:
it allows either exact identity or `+1`.
-/
def EPlus1 (x y : Nat) : Prop :=
  y = x ∨ y = x + 1

def singletonOne : SpecSet Nat :=
  fun y => y = 1

theorem EPlus1_sound :
    ∀ x y : Nat, oneLayerNatModel.proj onlyOne x = some y → EPlus1 x y := by
  intro x y h
  have hy : y = x := by
    simpa [oneLayerNatModel, onlyOne] using h.symm
  exact Or.inl hy

theorem EPlus1_not_complete :
    ¬ (∀ x y : Nat, EPlus1 x y → oneLayerNatModel.proj onlyOne x = some y) := by
  intro hComplete
  have hE : EPlus1 0 1 := by
    exact Or.inr rfl
  have hProj : oneLayerNatModel.proj onlyOne 0 = some 1 := hComplete 0 1 hE
  have hSome : (some 0 : Option Nat) = some 1 := by
    exact hProj
  have : (0 : Nat) = 1 := Option.some.inj hSome
  exact Nat.zero_ne_one this

theorem preimage_subset_semanticPullback_EPlus1 :
    oneLayerNatModel.preimage onlyOne singletonOne ⊆
      oneLayerNatModel.semanticPullback (i := onlyOne) EPlus1 singletonOne := by
  exact oneLayerNatModel.preimage_subset_semanticPullback_of_sound onlyOne EPlus1 EPlus1_sound singletonOne

theorem semanticPullback_not_subset_preimage_EPlus1 :
    ¬ (oneLayerNatModel.semanticPullback (i := onlyOne) EPlus1 singletonOne ⊆
        oneLayerNatModel.preimage onlyOne singletonOne) := by
  intro hSubset
  have hInSemantic :
      0 ∈ oneLayerNatModel.semanticPullback (i := onlyOne) EPlus1 singletonOne := by
    refine ⟨1, ?_, rfl⟩
    exact Or.inr rfl
  have hInPreimage : 0 ∈ oneLayerNatModel.preimage onlyOne singletonOne := hSubset hInSemantic
  rcases hInPreimage with ⟨y, hProj, hyOne⟩
  have hyZero : y = 0 := by
    simpa [oneLayerNatModel, onlyOne] using hProj.symm
  have : (0 : Nat) = 1 := by
    calc
      0 = y := by symm; exact hyZero
      _ = 1 := hyOne
  exact Nat.zero_ne_one this

end Examples
end UadfU0
