namespace UadfU0

universe u v

/-- Minimal UAD/f model for U0 specification proofs. -/
structure Model (ι : Type u) (α : Type v) where
  /-- Projection universes Ui. -/
  Ui : ι → Set α
  /-- Inverse mappings f₀ᵢ⁻¹ : Ui → U0 (set-level form). -/
  inv : ι → Set α → Set α

namespace Model

variable {ι : Type u} {α : Type v}

/-- Lift one projection universe into the U0 candidate space. -/
def lifted (M : Model ι α) (i : ι) : Set α :=
  M.inv i (M.Ui i)

/-- U0 is the union of lifted layers. -/
def U0 (M : Model ι α) : Set α :=
  {x : α | ∃ i : ι, x ∈ M.lifted i}

/-- Contradiction criterion between two layers: no shared witness in U0. -/
def Contradictory (M : Model ι α) (i j : ι) : Prop :=
  ∀ x : α, x ∈ M.lifted i → x ∈ M.lifted j → False

/-- Consistency criterion between two layers: at least one shared witness. -/
def Consistent (M : Model ι α) (i j : ι) : Prop :=
  ∃ x : α, x ∈ M.lifted i ∧ x ∈ M.lifted j

end Model
end UadfU0
