namespace UadfU0

universe u v

abbrev SpecSet (α : Type v) : Type v := α → Prop

instance {α : Type v} : Membership α (SpecSet α) where
  mem s x := s x

instance {α : Type v} : HasSubset (SpecSet α) where
  Subset s t := ∀ ⦃x : α⦄, x ∈ s → x ∈ t

def sUnion {α : Type v} (A B : SpecSet α) : SpecSet α :=
  fun x => x ∈ A ∨ x ∈ B

def sInter {α : Type v} (A B : SpecSet α) : SpecSet α :=
  fun x => x ∈ A ∧ x ∈ B

def sEmpty {α : Type v} : SpecSet α :=
  fun _ => False

infixr:65 " ∪ₛ " => sUnion
infixr:70 " ∩ₛ " => sInter
notation "∅ₛ" => sEmpty

theorem subset_refl {α : Type v} (A : SpecSet α) : A ⊆ A := by
  intro x hx
  exact hx

theorem subset_trans {α : Type v} {A B C : SpecSet α} :
    A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hx
  exact hBC (hAB hx)

theorem set_ext {α : Type v} {A B : SpecSet α} :
    (∀ x : α, x ∈ A ↔ x ∈ B) → A = B := by
  intro h
  funext x
  exact propext (h x)

/--
Minimal UAD/f model.

- `Ui`: layer-specific specification predicates.
- `proj`: forward projections from root space `α` to each layer (`none` means undefined).
Inverse images `f₀ᵢ⁻¹` are derived from `proj`, not postulated.
-/
structure Model (ι : Type u) (α : Type v) where
  Ui : ι → SpecSet α
  proj : ι → α → Option α

namespace Model

variable {ι : Type u} {α : Type v}

/-- Set-level inverse image induced by `proj`. -/
def preimage (M : Model ι α) (i : ι) (S : SpecSet α) : SpecSet α :=
  fun x => ∃ y : α, M.proj i x = some y ∧ y ∈ S

/-- Lift one projection universe into the U0 candidate space. -/
def lifted (M : Model ι α) (i : ι) : SpecSet α :=
  M.preimage i (M.Ui i)

/-- U0 is the union of all lifted layers. -/
def U0 (M : Model ι α) : SpecSet α :=
  fun x : α => ∃ i : ι, x ∈ M.lifted i

/-- Contradiction criterion: no shared witness between two lifted layers. -/
def Contradictory (M : Model ι α) (i j : ι) : Prop :=
  ∀ x : α, x ∈ M.lifted i → x ∈ M.lifted j → False

/-- Consistency criterion: at least one shared witness between two layers. -/
def Consistent (M : Model ι α) (i j : ι) : Prop :=
  ∃ x : α, x ∈ M.lifted i ∧ x ∈ M.lifted j

end Model
end UadfU0
