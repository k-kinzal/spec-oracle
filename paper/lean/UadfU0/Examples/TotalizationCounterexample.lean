import UadfU0.Definitions.Model

namespace UadfU0
namespace Examples

open Model

inductive One where
  | only
deriving DecidableEq

abbrev partialModel : Model One Nat where
  carrier := fun _ => Nat
  layer
  | .only =>
      {
        D := fun _ : Nat => True
        A := fun n : Nat => n = 42
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj
  | .only, x => if x = 0 then none else some x

def totalizedProj (default : Nat) (x : Nat) : Nat :=
  Option.getD (partialModel.proj .only x) default

def totalizedPreimage (default : Nat) : SpecSet Nat :=
  fun x => totalizedProj default x = 42

theorem naive_totalization_adds_spurious_witness :
    (0 ∈ totalizedPreimage 42) ∧
      (0 ∉ partialModel.preimage .only (partialModel.A .only)) := by
  constructor
  · change totalizedProj 42 0 = 42
    unfold totalizedProj
    simp
  · intro h
    rcases h with ⟨y, hproj, _⟩
    simp at hproj

end Examples
end UadfU0
