import UadfU0.InterLayer.Consistency

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/--
Layer-transfer theorem.

If every root witness projected to layer `j` can be related to some projection in layer `i`,
and that relation preserves admissibility from `j` to `i`,
then every `j`-lifted witness is also `i`-lifted.
-/
theorem lifted_transfer
    (i j : ι)
    (R : M.carrier i → M.carrier j → Prop)
    (hproj :
      ∀ x : α, ∀ yj : M.carrier j,
        M.proj j x = some yj →
        ∃ yi : M.carrier i, M.proj i x = some yi ∧ R yi yj)
    (hA :
      ∀ yi : M.carrier i, ∀ yj : M.carrier j,
        R yi yj → yj ∈ M.Ui j → yi ∈ M.Ui i) :
    M.lifted j ⊆ M.lifted i := by
  intro x hxj
  rcases hxj with ⟨yj, hproj_j, hyjA⟩
  rcases hproj x yj hproj_j with ⟨yi, hproj_i, hR⟩
  exact ⟨yi, hproj_i, hA yi yj hR hyjA⟩

/--
Consistency transport on the left argument:
if `lifted(j) ⊆ lifted(i)`, any witness consistent with `k` through `j`
is also consistent through `i`.
-/
theorem consistent_transport_left
    (i j k : ι)
    (hsub : M.lifted j ⊆ M.lifted i) :
    M.Consistent j k → M.Consistent i k := by
  intro hCons
  rcases hCons with ⟨x, hxj, hxk⟩
  exact ⟨x, hsub hxj, hxk⟩

end Model
end UadfU0
