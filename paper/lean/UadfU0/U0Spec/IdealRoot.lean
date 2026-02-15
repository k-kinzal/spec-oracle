import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

/-- Root points where layer `i` is observable (projection is defined). -/
def projDom (i : ι) : SpecSet α :=
  fun x => ∃ y : M.carrier i, M.proj i x = some y

/-- Root points observable for every active layer. -/
def projDomOn (active : ι → Prop) : SpecSet α :=
  fun x => ∀ i : ι, active i → x ∈ M.projDom i

/--
`UStar` denotes an intended (possibly unknown) ideal root specification.
If every active layer gives a necessary condition for `UStar`,
then `UStar` is included in meet-style integration over active layers.
-/
theorem UStar_subset_UAndOn
    {active : ι → Prop}
    (UStar : SpecSet α)
    (hNecessary : ∀ i : ι, active i → UStar ⊆ M.lifted i) :
    UStar ⊆ M.UAndOn active := by
  intro x hx i hi
  exact hNecessary i hi hx

/--
Domain-restricted necessary-condition assumption:
for each active layer, only the observable part of `UStar` is required to
satisfy the layer-level lifted predicate.
-/
theorem UStar_inter_projDomOn_subset_UAndOn
    {active : ι → Prop}
    (UStar : SpecSet α)
    (hNecessaryOnDom :
      ∀ i : ι, active i →
        (fun x : α => x ∈ UStar ∧ x ∈ M.projDom i) ⊆ M.lifted i) :
    (fun x : α => x ∈ UStar ∧ x ∈ M.projDomOn active) ⊆ M.UAndOn active := by
  intro x hx i hi
  have hxDom : x ∈ M.projDom i := hx.2 i hi
  exact hNecessaryOnDom i hi ⟨hx.1, hxDom⟩

/--
Under a non-empty active set, the same necessary-condition assumption implies
`UStar` is also included in join-style root coverage over active layers.
-/
theorem UStar_subset_U0On_of_nonempty_active
    {active : ι → Prop}
    (UStar : SpecSet α)
    (hNecessary : ∀ i : ι, active i → UStar ⊆ M.lifted i)
    (hActive : ∃ i : ι, active i) :
    UStar ⊆ M.U0On active := by
  have hMeet : UStar ⊆ M.UAndOn active :=
    M.UStar_subset_UAndOn (active := active) UStar hNecessary
  exact subset_trans hMeet (M.UAndOn_subset_U0On (active := active) hActive)

/--
Domain-restricted variant:
if each active layer is required only on its observable subdomain, then
the observable part of `UStar` is included in active-layer join coverage.
-/
theorem UStar_inter_projDomOn_subset_U0On_of_nonempty_active
    {active : ι → Prop}
    (UStar : SpecSet α)
    (hNecessaryOnDom :
      ∀ i : ι, active i →
        (fun x : α => x ∈ UStar ∧ x ∈ M.projDom i) ⊆ M.lifted i)
    (hActive : ∃ i : ι, active i) :
    (fun x : α => x ∈ UStar ∧ x ∈ M.projDomOn active) ⊆ M.U0On active := by
  have hMeet :
      (fun x : α => x ∈ UStar ∧ x ∈ M.projDomOn active) ⊆ M.UAndOn active :=
    M.UStar_inter_projDomOn_subset_UAndOn (active := active) UStar hNecessaryOnDom
  exact subset_trans hMeet (M.UAndOn_subset_U0On (active := active) hActive)

/--
May-style necessary-condition assumption:
if each active layer gives a may-style necessary condition for `UStar`,
then `UStar` is included in may-style meet integration.
-/
theorem UStar_subset_UAndMayOn
    {active : ι → Prop}
    (UStar : SpecSet α)
    (hNecessaryMay : ∀ i : ι, active i → UStar ⊆ M.liftedMay i) :
    UStar ⊆ M.UAndMayOn active := by
  intro x hx i hi
  exact hNecessaryMay i hi hx

/--
Global special case: if each layer is a necessary condition for `UStar`,
then `UStar` is included in global meet-style integration.
-/
theorem UStar_subset_UAnd
    (UStar : SpecSet α)
    (hNecessaryAll : ∀ i : ι, UStar ⊆ M.lifted i) :
    UStar ⊆ M.UAnd := by
  intro x hx i _hi
  exact hNecessaryAll i hx

end Model
end UadfU0
