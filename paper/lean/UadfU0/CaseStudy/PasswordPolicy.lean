import UadfU0.InterLayer.Adequacy

namespace UadfU0
namespace CaseStudy

open Model

inductive LayerIx where
  | req
  | api
  | code
deriving DecidableEq, Repr

structure ReqArtifact where
  minLen : Nat
  maxLen : Nat

structure ApiArtifact where
  minLen : Nat

structure CodeArtifact where
  maxLen : Nat

def reqAdmissible (r : ReqArtifact) : SpecSet Nat :=
  fun n => r.minLen ≤ n ∧ n ≤ r.maxLen

def apiAdmissible (a : ApiArtifact) : SpecSet Nat :=
  fun n => a.minLen ≤ n

def codeAdmissible (c : CodeArtifact) : SpecSet Nat :=
  fun n => n ≤ c.maxLen

abbrev passwordModel (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) :
    Model LayerIx Nat where
  carrier := fun _ => Nat
  layer
  | .req =>
      {
        D := fun _ : Nat => True
        A := reqAdmissible r
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | .api =>
      {
        D := fun _ : Nat => True
        A := apiAdmissible a
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  | .code =>
      {
        D := fun _ : Nat => True
        A := codeAdmissible c
        admissible_subset_domain := by
          intro x hx
          trivial
      }
  proj _ n := some n

def extractedLower (r : ReqArtifact) (a : ApiArtifact) : Nat :=
  Nat.max r.minLen a.minLen

def extractedUpper (r : ReqArtifact) (c : CodeArtifact) : Nat :=
  Nat.min r.maxLen c.maxLen

def checkConsistent (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) : Bool :=
  decide (extractedLower r a ≤ extractedUpper r c)

def allThreeConsistent (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) : Prop :=
  let M := passwordModel r a c
  ∃ n : Nat,
    n ∈ M.lifted .req ∧ n ∈ M.lifted .api ∧ n ∈ M.lifted .code

def reqExtractRel (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) :
    Nat → (passwordModel r a c).carrier .req → Prop :=
  fun x y => y = x

theorem req_projection_adequacy
    (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) :
    (passwordModel r a c).preimage .req (reqAdmissible r) =
      (passwordModel r a c).semanticPullback (reqExtractRel r a c) (reqAdmissible r) := by
  refine Model.preimage_eq_semanticPullback (M := passwordModel r a c) .req (reqExtractRel r a c) ?hEq (reqAdmissible r)
  intro x y
  constructor
  · intro hproj
    exact (by simpa [passwordModel] using hproj : x = y).symm
  · intro hrel
    have hyx : y = x := by
      simpa [reqExtractRel] using hrel
    simp [passwordModel, hyx]

theorem checkConsistent_true_implies_allThree
    (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact)
    (h : checkConsistent r a c = true) :
    allThreeConsistent r a c := by
  unfold checkConsistent at h
  have hLe : extractedLower r a ≤ extractedUpper r c := by
    exact of_decide_eq_true h
  refine ⟨extractedLower r a, ?_, ?_, ?_⟩
  · refine ⟨extractedLower r a, rfl, ?_⟩
    constructor
    · exact Nat.le_max_left r.minLen a.minLen
    · have hUpperReq : extractedUpper r c ≤ r.maxLen := Nat.min_le_left r.maxLen c.maxLen
      exact Nat.le_trans hLe hUpperReq
  · refine ⟨extractedLower r a, rfl, ?_⟩
    exact Nat.le_max_right r.minLen a.minLen
  · refine ⟨extractedLower r a, rfl, ?_⟩
    have hUpperCode : extractedUpper r c ≤ c.maxLen := Nat.min_le_right r.maxLen c.maxLen
    exact Nat.le_trans hLe hUpperCode

theorem allThree_implies_checkConsistent_true
    (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact)
    (h : allThreeConsistent r a c) :
    checkConsistent r a c = true := by
  rcases h with ⟨n, hReq, hApi, hCode⟩
  rcases hReq with ⟨nr, hProjReq, hReqA⟩
  rcases hApi with ⟨na, hProjApi, hApiA⟩
  rcases hCode with ⟨nc, hProjCode, hCodeA⟩
  have hnr : nr = n := by
    symm
    simpa [passwordModel] using hProjReq
  have hna : na = n := by
    symm
    simpa [passwordModel] using hProjApi
  have hnc : nc = n := by
    symm
    simpa [passwordModel] using hProjCode
  have hReqBounds : r.minLen ≤ n ∧ n ≤ r.maxLen := by
    simpa [reqAdmissible, hnr] using hReqA
  have hApiMin : a.minLen ≤ n := by
    simpa [apiAdmissible, hna] using hApiA
  have hCodeMax : n ≤ c.maxLen := by
    simpa [codeAdmissible, hnc] using hCodeA
  have hLowerLeN : extractedLower r a ≤ n := by
    exact (Nat.max_le).2 ⟨hReqBounds.1, hApiMin⟩
  have hNLeUpper : n ≤ extractedUpper r c := by
    exact (Nat.le_min).2 ⟨hReqBounds.2, hCodeMax⟩
  have hFinal : extractedLower r a ≤ extractedUpper r c := Nat.le_trans hLowerLeN hNLeUpper
  unfold checkConsistent
  exact by simpa using (show decide (extractedLower r a ≤ extractedUpper r c) = true from
    by exact decide_eq_true hFinal)

theorem checkConsistent_iff_allThree
    (r : ReqArtifact) (a : ApiArtifact) (c : CodeArtifact) :
    checkConsistent r a c = true ↔ allThreeConsistent r a c := by
  constructor
  · exact checkConsistent_true_implies_allThree r a c
  · exact allThree_implies_checkConsistent_true r a c

def exConsistentReq : ReqArtifact := { minLen := 8, maxLen := 64 }
def exConsistentApi : ApiArtifact := { minLen := 10 }
def exConsistentCode : CodeArtifact := { maxLen := 128 }

example : checkConsistent exConsistentReq exConsistentApi exConsistentCode = true := by
  native_decide

def exContradictReq : ReqArtifact := { minLen := 8, maxLen := 12 }
def exContradictApi : ApiArtifact := { minLen := 16 }
def exContradictCode : CodeArtifact := { maxLen := 10 }

example : checkConsistent exContradictReq exContradictApi exContradictCode = false := by
  native_decide

end CaseStudy
end UadfU0
