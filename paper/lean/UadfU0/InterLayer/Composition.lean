import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Pull back a target-layer set through a partial inter-layer map. -/
def pullbackVia
    {i j : ι}
    (g : M.carrier i → Option (M.carrier j))
    (S : SpecSet (M.carrier j)) :
    SpecSet (M.carrier i) :=
  fun yi => ∃ yj : M.carrier j, g yi = some yj ∧ yj ∈ S

/--
Composition law for induced inverse images.

If `proj_j = bind(proj_i, g)`, then inverse image at layer `j`
equals inverse image at layer `i` of the pullback through `g`.
-/
theorem preimage_compose
    (i j : ι)
    (g : M.carrier i → Option (M.carrier j))
    (hcomm : ∀ x : α, M.proj j x = Option.bind (M.proj i x) g)
    (S : SpecSet (M.carrier j)) :
    M.preimage j S = M.preimage i (M.pullbackVia g S) := by
  apply set_ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨yj, hprojJ, hyjS⟩
    by_cases hSome : ∃ yi : M.carrier i, M.proj i x = some yi
    · rcases hSome with ⟨yi, hprojI⟩
      refine ⟨yi, hprojI, ?_⟩
      refine ⟨yj, ?_, hyjS⟩
      have hEqBind : Option.bind (M.proj i x) g = some yj := by
        calc
          Option.bind (M.proj i x) g = M.proj j x := (hcomm x).symm
          _ = some yj := hprojJ
      simpa [hprojI] using hEqBind
    · have hNone : M.proj i x = none := by
        by_cases hpi : M.proj i x = none
        · exact hpi
        · exfalso
          cases hVal : M.proj i x with
          | none =>
              exact hpi hVal
          | some yi =>
              exact hSome ⟨yi, hVal⟩
      have hEqBind : Option.bind (M.proj i x) g = some yj := by
        calc
          Option.bind (M.proj i x) g = M.proj j x := (hcomm x).symm
          _ = some yj := hprojJ
      simp [hNone] at hEqBind
  · intro hx
    rcases hx with ⟨yi, hprojI, hpb⟩
    rcases hpb with ⟨yj, hgyi, hyjS⟩
    refine ⟨yj, ?_, hyjS⟩
    have hEqBind : Option.bind (M.proj i x) g = some yj := by
      simpa [hprojI] using hgyi
    calc
      M.proj j x = Option.bind (M.proj i x) g := hcomm x
      _ = some yj := hEqBind

/-- Lifted-set inclusion derived from an inter-layer composition law. -/
theorem lifted_subset_of_compose
    (i j : ι)
    (g : M.carrier i → Option (M.carrier j))
    (hcomm : ∀ x : α, M.proj j x = Option.bind (M.proj i x) g)
    (hA : M.pullbackVia g (M.Ui j) ⊆ M.Ui i) :
    M.lifted j ⊆ M.lifted i := by
  intro x hxj
  have hEq := M.preimage_compose i j g hcomm (M.Ui j)
  have hxj' : x ∈ M.preimage i (M.pullbackVia g (M.Ui j)) := by
    exact (hEq ▸ hxj)
  exact M.preimage_monotone i hA hxj'

end Model
end UadfU0
