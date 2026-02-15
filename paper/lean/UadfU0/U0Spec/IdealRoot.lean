import UadfU0.U0Spec.Construction

namespace UadfU0
namespace Model

universe u v w

variable {ι : Type u} {α : Type v}
variable (M : Model ι α)

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
