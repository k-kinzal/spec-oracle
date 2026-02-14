import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Semantic pullback induced by an explicit extraction relation. -/
def semanticPullback
    {i : ι}
    (E : α → M.carrier i → Prop)
    (S : SpecSet (M.carrier i)) :
    SpecSet α :=
  fun x => ∃ y : M.carrier i, E x y ∧ y ∈ S

/--
Soundness-only variant:
if every projected witness satisfies `E`, preimage is included in semantic pullback.
-/
theorem preimage_subset_semanticPullback_of_sound
    (i : ι)
    (E : α → M.carrier i → Prop)
    (hSound : ∀ x : α, ∀ y : M.carrier i, M.proj i x = some y → E x y)
    (S : SpecSet (M.carrier i)) :
    M.preimage i S ⊆ M.semanticPullback E S := by
  intro x hx
  rcases hx with ⟨y, hproj, hyS⟩
  exact ⟨y, hSound x y hproj, hyS⟩

/--
Completeness-only variant:
if every `E`-witness is realized by projection, semantic pullback is included in preimage.
-/
theorem semanticPullback_subset_preimage_of_complete
    (i : ι)
    (E : α → M.carrier i → Prop)
    (hComplete : ∀ x : α, ∀ y : M.carrier i, E x y → M.proj i x = some y)
    (S : SpecSet (M.carrier i)) :
    M.semanticPullback E S ⊆ M.preimage i S := by
  intro x hx
  rcases hx with ⟨y, hExy, hyS⟩
  exact ⟨y, hComplete x y hExy, hyS⟩

/--
Adequacy transfer theorem.

If partial projection and extraction relation are pointwise equivalent,
the induced inverse image equals semantic pullback.
-/
theorem preimage_eq_semanticPullback
    (i : ι)
    (E : α → M.carrier i → Prop)
    (hEq : ∀ x : α, ∀ y : M.carrier i, M.proj i x = some y ↔ E x y)
    (S : SpecSet (M.carrier i)) :
    M.preimage i S = M.semanticPullback E S := by
  apply set_ext
  intro x
  constructor
  · intro hx
    exact M.preimage_subset_semanticPullback_of_sound i E (fun x y h => (hEq x y).1 h) S hx
  · intro hx
    exact M.semanticPullback_subset_preimage_of_complete i E (fun x y h => (hEq x y).2 h) S hx

end Model
end UadfU0
