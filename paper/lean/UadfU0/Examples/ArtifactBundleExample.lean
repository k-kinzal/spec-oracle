import UadfU0.InterLayer.Adequacy

namespace UadfU0
namespace Examples

open Model

inductive LayerTag where
  | req
  | api
  | code
deriving DecidableEq

open LayerTag

structure ReqArtifact where
  lower : Nat
  upper : Nat

structure ApiArtifact where
  lower : Nat
  upper : Nat

structure CodeArtifact where
  max : Nat

structure ReqIR where
  lower : Nat
  upper : Nat

structure ApiIR where
  lower : Nat
  upper : Nat

structure CodeIR where
  max : Nat

structure ArtifactBundle where
  reqDoc : Option ReqArtifact
  apiDoc : Option ApiArtifact
  codeDoc : Option CodeArtifact

def Gamma : LayerTag → Type
  | req => ReqArtifact
  | api => ApiArtifact
  | code => CodeArtifact

def Beta : LayerTag → Type
  | req => ReqIR
  | api => ApiIR
  | code => CodeIR

def obs : (i : LayerTag) → ArtifactBundle → Option (Gamma i)
  | req, x => x.reqDoc
  | api, x => x.apiDoc
  | code, x => x.codeDoc

def extract : (i : LayerTag) → Gamma i → Option (Beta i)
  | req, g =>
      if g.lower ≤ g.upper then
        some ⟨g.lower, g.upper⟩
      else
        none
  | api, g =>
      if g.lower ≤ g.upper then
        some ⟨g.lower, g.upper⟩
      else
        none
  | code, g =>
      some ⟨g.max⟩

def projFromObsExtract (i : LayerTag) (x : ArtifactBundle) : Option (Beta i) :=
  Option.bind (obs i x) (extract i)

def layerOf : (i : LayerTag) → Layer (Beta i)
  | req =>
      {
        D := fun y : ReqIR => y.lower ≤ y.upper
        A := fun y : ReqIR => y.lower ≤ y.upper ∧ y.upper ≤ 63
        admissible_subset_domain := by
          intro y hy
          exact hy.1
      }
  | api =>
      {
        D := fun y : ApiIR => y.lower ≤ y.upper
        A := fun y : ApiIR => y.lower ≤ y.upper ∧ y.upper ≤ 63
        admissible_subset_domain := by
          intro y hy
          exact hy.1
      }
  | code =>
      {
        D := fun _ : CodeIR => True
        A := fun y : CodeIR => y.max ≤ 63
        admissible_subset_domain := by
          intro y hy
          trivial
      }

abbrev artifactBundleModel : Model LayerTag ArtifactBundle where
  carrier := Beta
  layer := layerOf
  proj := projFromObsExtract

theorem proj_bind_decomposition (i : LayerTag) (x : ArtifactBundle) :
    artifactBundleModel.proj i x = Option.bind (obs i x) (extract i) := by
  rfl

/--
Concrete semantic extraction relation induced by `obs/extract`.
This is used as a concrete adequacy instantiation witness.
-/
def Eextract (i : LayerTag) (x : ArtifactBundle) (y : artifactBundleModel.carrier i) : Prop :=
  ∃ γ : Gamma i, obs i x = some γ ∧ extract i γ = some y

theorem Eextract_sound
    (i : LayerTag) :
    ∀ x : ArtifactBundle, ∀ y : artifactBundleModel.carrier i,
      artifactBundleModel.proj i x = some y → Eextract i x y := by
  intro x y hProj
  unfold artifactBundleModel at hProj
  unfold projFromObsExtract at hProj
  unfold Eextract
  cases hObs : obs i x with
  | none =>
      simp [hObs] at hProj
  | some γ =>
      have hExtract : extract i γ = some y := by
        simpa [hObs] using hProj
      exact ⟨γ, by simp, hExtract⟩

theorem Eextract_complete
    (i : LayerTag) :
    ∀ x : ArtifactBundle, ∀ y : artifactBundleModel.carrier i,
      Eextract i x y → artifactBundleModel.proj i x = some y := by
  intro x y hE
  rcases hE with ⟨γ, hObs, hExtract⟩
  unfold artifactBundleModel
  unfold projFromObsExtract
  simp [hObs, hExtract]

theorem preimage_eq_semanticPullback_Eextract
    (i : LayerTag)
    (S : SpecSet (artifactBundleModel.carrier i)) :
    artifactBundleModel.preimage i S =
      artifactBundleModel.semanticPullback (Eextract i) S := by
  apply artifactBundleModel.preimage_eq_semanticPullback i (Eextract i)
  intro x y
  constructor
  · intro hProj
    exact Eextract_sound i x y hProj
  · intro hE
    exact Eextract_complete i x y hE

def goodBundle : ArtifactBundle where
  reqDoc := some ⟨1, 63⟩
  apiDoc := some ⟨1, 63⟩
  codeDoc := some ⟨63⟩

def brokenReqBundle : ArtifactBundle where
  reqDoc := some ⟨64, 63⟩
  apiDoc := some ⟨1, 63⟩
  codeDoc := some ⟨63⟩

example : goodBundle ∈ artifactBundleModel.U0 := by
  refine ⟨LayerTag.req, ?_⟩
  refine ⟨⟨1, 63⟩, ?_, ?_⟩
  · simp [artifactBundleModel, projFromObsExtract, obs, extract, goodBundle]
  · change 1 ≤ 63 ∧ 63 ≤ 63
    decide

example : goodBundle ∈ artifactBundleModel.UAnd := by
  intro i hi
  cases i with
  | req =>
      refine ⟨⟨1, 63⟩, ?_, ?_⟩
      · simp [artifactBundleModel, projFromObsExtract, obs, extract, goodBundle]
      · change 1 ≤ 63 ∧ 63 ≤ 63
        decide
  | api =>
      refine ⟨⟨1, 63⟩, ?_, ?_⟩
      · simp [artifactBundleModel, projFromObsExtract, obs, extract, goodBundle]
      · change 1 ≤ 63 ∧ 63 ≤ 63
        decide
  | code =>
      refine ⟨⟨63⟩, ?_, ?_⟩
      · simp [artifactBundleModel, projFromObsExtract, obs, extract, goodBundle]
      · change 63 ≤ 63
        decide

example : brokenReqBundle ∉ artifactBundleModel.lifted LayerTag.req := by
  intro hx
  rcases hx with ⟨y, hproj, _⟩
  simp [artifactBundleModel, projFromObsExtract, obs, extract, brokenReqBundle] at hproj

example : brokenReqBundle ∈ artifactBundleModel.liftedMay LayerTag.req := by
  change artifactBundleModel.proj LayerTag.req brokenReqBundle = none ∨
      ∃ y : artifactBundleModel.carrier LayerTag.req,
        artifactBundleModel.proj LayerTag.req brokenReqBundle = some y ∧ y ∈ artifactBundleModel.Ui LayerTag.req
  left
  simp [artifactBundleModel, projFromObsExtract, obs, extract, brokenReqBundle]

end Examples
end UadfU0
