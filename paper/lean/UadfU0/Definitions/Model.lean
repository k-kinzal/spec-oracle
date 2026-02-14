namespace UadfU0

universe u v w

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
Layer in UAD/f:
- `D`: domain predicate
- `A`: admissible predicate
- `A ⊆ D`: admissible values stay inside the domain.
-/
structure Layer (β : Type w) where
  D : SpecSet β
  A : SpecSet β
  admissible_subset_domain : A ⊆ D

/--
Typed UAD/f model:
- root space `α`
- per-layer carrier type `carrier i = βᵢ`
- partial forward map `proj i : α → Option βᵢ`

`f₀ᵢ⁻¹` is represented by `preimage i`.
-/
structure Model (ι : Type u) (α : Type v) where
  carrier : ι → Type w
  layer : (i : ι) → Layer (carrier i)
  proj : (i : ι) → α → Option (carrier i)

namespace Model

variable {ι : Type u} {α : Type v}

def D (M : Model ι α) (i : ι) : SpecSet (M.carrier i) :=
  (M.layer i).D

def A (M : Model ι α) (i : ι) : SpecSet (M.carrier i) :=
  (M.layer i).A

/-- Compatibility alias. -/
def Ui (M : Model ι α) (i : ι) : SpecSet (M.carrier i) :=
  M.A i

/-- Set-level inverse image induced by typed partial projection. -/
def preimage (M : Model ι α) (i : ι) (S : SpecSet (M.carrier i)) : SpecSet α :=
  fun x => ∃ y : M.carrier i, M.proj i x = some y ∧ y ∈ S

/-- Lift one layer admissible set into root space. -/
def lifted (M : Model ι α) (i : ι) : SpecSet α :=
  M.preimage i (M.Ui i)

/-- U0 is the union of all lifted sets in root space. -/
def U0 (M : Model ι α) : SpecSet α :=
  fun x : α => ∃ i : ι, x ∈ M.lifted i

/-- Contradiction: no shared root witness across two lifted layers. -/
def Contradictory (M : Model ι α) (i j : ι) : Prop :=
  ∀ x : α, x ∈ M.lifted i → x ∈ M.lifted j → False

/-- Consistency: at least one shared root witness exists. -/
def Consistent (M : Model ι α) (i j : ι) : Prop :=
  ∃ x : α, x ∈ M.lifted i ∧ x ∈ M.lifted j

end Model
end UadfU0
