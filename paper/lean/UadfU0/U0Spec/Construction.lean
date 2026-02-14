import UadfU0.Definitions.Model

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Expand membership of an induced inverse image. -/
theorem mem_preimage_iff (i : ι) (S : SpecSet (M.carrier i)) (x : α) :
    x ∈ M.preimage i S ↔ ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ S := Iff.rfl

/-- Inverse images induced by typed partial projection are monotone. -/
theorem preimage_monotone (i : ι) {S T : SpecSet (M.carrier i)}
    (hST : S ⊆ T) :
    M.preimage i S ⊆ M.preimage i T := by
  intro x hx
  rcases hx with ⟨y, hproj, hyS⟩
  exact ⟨y, hproj, hST hyS⟩

/-- Inverse image preserves binary unions. -/
theorem preimage_union (i : ι) (S T : SpecSet (M.carrier i)) :
    M.preimage i (S ∪ₛ T) = M.preimage i S ∪ₛ M.preimage i T := by
  apply set_ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨y, hproj, hyST⟩
    cases hyST with
    | inl hyS =>
        exact Or.inl ⟨y, hproj, hyS⟩
    | inr hyT =>
        exact Or.inr ⟨y, hproj, hyT⟩
  · intro hx
    cases hx with
    | inl hxS =>
        rcases hxS with ⟨y, hproj, hyS⟩
        exact ⟨y, hproj, Or.inl hyS⟩
    | inr hxT =>
        rcases hxT with ⟨y, hproj, hyT⟩
        exact ⟨y, hproj, Or.inr hyT⟩

/-- Because each layer satisfies `A ⊆ D`, lifted admissible points stay in lifted domains. -/
theorem lifted_subset_preimage_domain (i : ι) :
    M.lifted i ⊆ M.preimage i (M.D i) := by
  have hAD : M.Ui i ⊆ M.D i := (M.layer i).admissible_subset_domain
  exact M.preimage_monotone i hAD

/-- Membership in U0 is exactly membership in some lifted layer. -/
theorem mem_U0_iff (x : α) :
    x ∈ M.U0 ↔ ∃ i : ι, x ∈ M.lifted i := Iff.rfl

/-- Root specification induced by a selected subset of layers. -/
def U0On (active : ι → Prop) : SpecSet α :=
  fun x : α => ∃ i : ι, active i ∧ x ∈ M.lifted i

/-- Meet-style integrated specification: all active layers must hold simultaneously. -/
def UAndOn (active : ι → Prop) : SpecSet α :=
  fun x : α => ∀ i : ι, active i → x ∈ M.lifted i

/-- Global meet-style integrated specification over all layers. -/
def UAnd : SpecSet α :=
  M.UAndOn (fun _ : ι => True)

/-- If the active layer set grows, the induced root specification grows. -/
theorem U0On_monotone {J K : ι → Prop}
    (hJK : ∀ i : ι, J i → K i) :
    M.U0On J ⊆ M.U0On K := by
  intro x hx
  rcases hx with ⟨i, hJi, hix⟩
  exact ⟨i, hJK i hJi, hix⟩

/-- `U0` is the special case where all layers are active. -/
theorem U0_eq_U0On_all :
    M.U0 = M.U0On (fun _ : ι => True) := by
  apply set_ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨i, hix⟩
    exact ⟨i, trivial, hix⟩
  · intro hx
    rcases hx with ⟨i, _, hix⟩
    exact ⟨i, hix⟩

/-- `UAnd` is the special case where all layers are active. -/
theorem UAnd_eq_UAndOn_all :
    M.UAnd = M.UAndOn (fun _ : ι => True) := by
  rfl

/--
If the active-layer predicate grows, meet-style integration becomes stricter.
Equivalently, `UAndOn` is antitone in the active predicate.
-/
theorem UAndOn_antitone {J K : ι → Prop}
    (hJK : ∀ i : ι, J i → K i) :
    M.UAndOn K ⊆ M.UAndOn J := by
  intro x hx i hi
  exact hx i (hJK i hi)

/--
With no active layers, meet-style integration is vacuously true for every root point.
-/
theorem UAndOn_empty_eq_univ :
    M.UAndOn (fun _ : ι => False) = (fun _ : α => True) := by
  apply set_ext
  intro x
  constructor
  · intro _hx
    trivial
  · intro _hx i hi
    exact False.elim hi

/--
If all active layers hold at `x` and at least one active layer exists,
then `x` is included in the corresponding join-style root spec.
-/
theorem UAndOn_subset_U0On
    {active : ι → Prop}
    (hActive : ∃ i : ι, active i) :
    M.UAndOn active ⊆ M.U0On active := by
  intro x hx
  rcases hActive with ⟨i, hi⟩
  exact ⟨i, hi, hx i hi⟩

/--
For any pair of layers, consistency is equivalent to non-emptiness of
the pair-restricted meet-style integrated specification.
-/
theorem consistent_iff_exists_UAndOn_pair (i j : ι) :
    M.Consistent i j ↔ ∃ x : α, x ∈ M.UAndOn (fun k : ι => k = i ∨ k = j) := by
  constructor
  · intro hCons
    rcases hCons with ⟨x, hxi, hxj⟩
    refine ⟨x, ?_⟩
    intro k hk
    cases hk with
    | inl hki =>
        simpa [hki] using hxi
    | inr hkj =>
        simpa [hkj] using hxj
  · intro h
    rcases h with ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · exact hx i (Or.inl rfl)
    · exact hx j (Or.inr rfl)

/-- Every lifted layer contributes directly to U0. -/
theorem lifted_subset_U0 (i : ι) :
    M.lifted i ⊆ M.U0 := by
  intro x hx
  exact ⟨i, hx⟩

/-- If any lifted layer has a witness, U0 is non-empty. -/
theorem U0_nonempty_of_exists_layer_nonempty
    (h : ∃ i : ι, ∃ x : α, x ∈ M.lifted i) :
    ∃ x : α, x ∈ M.U0 := by
  rcases h with ⟨i, x, hx⟩
  exact ⟨x, ⟨i, hx⟩⟩

/-- Any U0 witness projects into some layer domain. -/
theorem U0_witness_projects_to_some_domain (x : α)
    (hx : x ∈ M.U0) :
    ∃ i : ι, ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ M.D i := by
  rcases hx with ⟨i, hxi⟩
  have hdom : x ∈ M.preimage i (M.D i) :=
    M.lifted_subset_preimage_domain i hxi
  rcases hdom with ⟨y, hproj, hydom⟩
  exact ⟨i, y, hproj, hydom⟩

end Model
end UadfU0
