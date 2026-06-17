import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Examples

open Model

/--
Counterexample showing that admissibility-side reasoning alone does not imply
`lifted(j) ⊆ lifted(i)` when same-root linkage is absent.
-/
abbrev transferCounterModel : Model Bool Nat where
  carrier := fun _ => Nat
  layer := fun b =>
    if b then
      {
        D := fun _ : Nat => True
        A := fun y : Nat => y = 0
        admissible_subset_domain := by
          intro y hy
          trivial
      }
    else
      {
        D := fun _ : Nat => True
        A := fun _ : Nat => True
        admissible_subset_domain := by
          intro y hy
          trivial
      }
  proj := fun b x =>
    if b then some 0 else none

def iLayer : Bool := false
def jLayer : Bool := true

def RTrivial : Nat → Nat → Prop := fun _ _ => True

theorem hA_trivial :
    ∀ yi yj : transferCounterModel.carrier iLayer,
      RTrivial yi yj → yj ∈ transferCounterModel.Ui jLayer → yi ∈ transferCounterModel.Ui iLayer := by
  intro yi yj hR hyj
  trivial

theorem zero_in_lifted_j :
    (0 : Nat) ∈ transferCounterModel.lifted jLayer := by
  refine ⟨0, ?_, ?_⟩
  · simp [transferCounterModel, jLayer]
  · show (0 : Nat) = 0
    rfl

theorem zero_not_in_lifted_i :
    (0 : Nat) ∉ transferCounterModel.lifted iLayer := by
  intro hz
  rcases hz with ⟨y, hyProj, hyA⟩
  simp [transferCounterModel, iLayer] at hyProj

theorem transfer_fails_without_hproj :
    ¬ (transferCounterModel.lifted jLayer ⊆ transferCounterModel.lifted iLayer) := by
  intro hSub
  exact zero_not_in_lifted_i (hSub zero_in_lifted_j)

end Examples
end UadfU0
