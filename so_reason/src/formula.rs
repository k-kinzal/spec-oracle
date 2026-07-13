//! The formula layer: symbolic Boolean structure over opaque atoms.
//!
//! This module is the structural precondition for sound graph edges — the
//! twice-raised prerequisite for *refines*, *composes*, and *contradicts*
//! meaning something checkable. It gives every behavioral sentence a
//! propositional shape: which guard atoms scope it, how they conjoin and
//! disjoin, where the exception negates, and what the claim atom is.
//!
//! Deliberately NOT here: decision procedures over these formulas. The
//! conservative structural judgments (implies / contradicts / refines) live
//! in [`crate::relate`] since round 5, comparing atoms by their
//! [`Proposition`] — the logical key; SMT grounding of the atoms remains
//! future work. Atoms carry skeleton-level digests ([`ClauseSkeleton`] for
//! applicability, [`BehaviorAtom`] for the claim) for indexing, plus a
//! lossless `source` anchor (see below). Raw sentence text stays
//! authoritative; every formula is a derived view.
//!
//! # Index vs logic
//!
//! The skeleton ([`crate::semantics::Skeleton`]) is the surface INDEX: it
//! records what was written (`no daemon` keeps [`Quantifier::Negative`]).
//! The formula layer is normalized LOGIC: a subject `no` quantifies
//! universally over a denied predicate (`no X: P` ≡ `¬∃X P` ≡ `∀X ¬P`), so
//! a behavior atom built from a `no` subject carries
//! [`Quantifier::Universal`], and the negation is carried EXACTLY ONCE, by
//! the formula's `Not` wrapper — composed per atom with the claim-level
//! site (see [`claim_formula`]). The two views intentionally differ on
//! `no`.
//!
//! **Quantifier scope convention.** A behavior atom is not a closed
//! proposition: its subject quantifier always OUT-SCOPES the atom's own
//! `Not` wrapper. `Not` here is claim-level (predicate) negation — a
//! per-individual denial — so `Not(atom{subject: ∀X, P})` reads `∀X ¬P(X)`
//! and never `¬∀X P(X)`. This is uniform, not special to `no`: `Each
//! daemon shall not sleep.` also yields `Not(atom{daemon, Universal})`
//! meaning every daemon refrains. Coordination connectives sit outside the
//! per-item atoms, each of which carries its own subject, so no wider
//! scope interaction arises. A downstream solver grounding these atoms in
//! first-order form must apply the negation inside the subject quantifier.
//!
//! # Anchors
//!
//! Every atom carries a lossless `source` anchor: the canonical render of
//! the material the atom is derived from (the clause render for guard
//! atoms; the core render with this item as sole subject — no frames, no
//! exception, no purpose — for behavior and admissibility atoms). The
//! anchor keeps the SURFACE negation sites (a deontic `not`, a subject
//! `no`), so it carries strictly more than the atom's digest fields: the
//! negation the formula structure expresses through the `Not` wrapper and
//! the `Universal` normalization is still visible in the anchor text.
//!
//! The safe consumption rule is therefore RE-DERIVATION, not substitution:
//! re-parse the anchor and take ITS [`claim_formula`] — that reproduces
//! exactly the atom's enclosing sub-formula (the atom together with its
//! own `Not` wrapper, with this item as sole subject), never the bare
//! atom. Reading the anchor text as the atom's un-negated content
//! double-counts the negation; and anchors are not atom-identity keys —
//! logically equivalent sentences keep distinct anchors (`no request shall
//! not be logged` vs `each request shall be logged`) even where their
//! normalized digests meet. The digests stay for indexing, but they are
//! lossy (modifiers, prepositions, nested-clause detail are dropped);
//! downstream equality or entailment checking must compare formulas
//! re-derived from the anchors (or the ASTs they re-parse to), never the
//! digest alone and never the anchor strings alone.

use crate::semantics::{
    claim_atoms, claim_polarity, clause_group_skeletons, denote, force, speech_act,
    subject_skeleton_of, Atom, Claim, ClauseSkeleton, Denotation, Force, Polarity, Quantifier,
    SpeechAct, SubjectSkeleton,
};
use serde::{Deserialize, Serialize};
use so_lang::ast::*;
use thiserror::Error;

/// A propositional formula over opaque atoms. Connectives are n-ary where
/// the surface language is (`And`/`Or` mirror clause groups, frame stacking,
/// and subject coordination); `Top` is the empty conjunction (an ubiquitous
/// sentence's applicability), `Bottom` its dual.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
// The atom payload dwarfs the connectives (round 6 widened digests with
// full-identity strings and structured comparisons). Boxing it would break
// every `Formula::Atom { atom: AtomRef::… }` pattern across the crate and
// its consumers for a size win that does not matter at these volumes —
// formulas are per-sentence derived views, not bulk storage.
#[allow(clippy::large_enum_variant)]
pub enum Formula {
    /// One opaque atom. A struct variant (not a newtype): an internally
    /// tagged enum cannot serialize a newtype variant holding some payloads,
    /// and the rest of the crate keeps struct variants for that reason.
    Atom {
        atom: AtomRef,
    },
    And {
        items: Vec<Formula>,
    },
    Or {
        items: Vec<Formula>,
    },
    Not {
        inner: Box<Formula>,
    },
    Top,
    Bottom,
}

impl Formula {
    fn not(inner: Formula) -> Formula {
        Formula::Not {
            inner: Box::new(inner),
        }
    }
}

/// What a formula atom refers to — skeleton-level digests for indexing, each
/// with its lossless `source` anchor (module docs, § Anchors).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AtomRef {
    /// An applicability atom: one guard clause's digest, anchored by that
    /// clause's canonical render, carrying the FRAME ROLE it guards under
    /// (round 10): `While the pump runs,` and `When the pump runs,` are
    /// different conditions — a state throughout vs an instant of change —
    /// so the role is part of the atom's identity (equality, canonical
    /// sort key, overlap witnessing all see it).
    Guard {
        clause: ClauseSkeleton,
        source: String,
        /// The frame role (round 10). Serde: pre-round-10 guard atoms
        /// carry no `role` field and load as [`GuardRole::State`] — the
        /// documented PRE-ROUND-10 READING, in which all guard families
        /// digested alike (so a legacy atom keeps exactly the identity it
        /// was recorded with, rather than being silently promoted into a
        /// finer one); derived views are re-derived from raw text anyway,
        /// which refreshes the role honestly.
        #[serde(default = "legacy_guard_role")]
        role: GuardRole,
    },
    /// The claim atom: the GRAMMATICAL subject and its behavior digest.
    /// (For a passive with a stated agent the grammatical subject is the
    /// PATIENT — the agent lands in the role tail, not here; the
    /// round-10 RESPONSIBLE view is a separate derivation,
    /// [`crate::semantics::responsible_subject_keys`], and feeds
    /// [`SubjectRelation`], not this atom.)
    Behavior { behavior: BehaviorAtom },
    /// An admissibility atom — a permission's claim. It bounds tolerated
    /// environment behavior (what the component must withstand) and can
    /// never witness occurrence: nothing is obliged to happen, so an
    /// admissibility atom can never DISCHARGE an assumption (no
    /// [`EdgeKind::GuaranteeDischarge`] edge ends here); it only widens the
    /// envelope an assumption must tolerate.
    Admissibility { behavior: BehaviorAtom },
}

/// The frame role a guard atom guards under (round 10): which circumstance
/// family the clause was written in. `Where` scopes, `While` states a
/// condition that HOLDS THROUGHOUT, `When`/`If` trigger at an INSTANT
/// (the trigger kind — event vs contingency — is kept: `If` marks EARS'
/// unwanted-behaviour form), and `unless` carves an exception (its atom
/// sits under the applicability formula's `Not`). The role is part of
/// guard-atom IDENTITY: two guards over the same written clause but
/// different roles are different atoms, never witnesses for one another
/// (see [`crate::relate`] — the conservative cross-role rule).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum GuardRole {
    /// A `Where` frame.
    Scope,
    /// A `While` frame.
    State,
    /// The `When`/`If` trigger frame, with its kind. On the wire the kind
    /// field is named `"trigger"` (`{ "kind": "trigger", "trigger":
    /// "event" }`): the enum is internally tagged by `"kind"`, so the
    /// field cannot also be `"kind"` — noted in the serde table.
    Trigger {
        #[serde(rename = "trigger")]
        kind: TriggerKind,
    },
    /// The `unless` carve-out.
    Exception,
}

/// The serde default for [`AtomRef::Guard::role`]: pre-round-10 guard atoms
/// digested every frame family alike, and [`GuardRole::State`] is
/// DOCUMENTED as that legacy reading (see the field's doc — this is a
/// recorded fact about old data, not a guess about what was meant).
fn legacy_guard_role() -> GuardRole {
    GuardRole::State
}

/// The claim as an atom: subject, behavior kernel, force, and speech act —
/// the same skeleton-level material [`crate::semantics::Skeleton`] carries,
/// minus what the formula structure itself expresses (polarity is a `Not`
/// wrapper; guards are the applicability formula) — plus the lossless
/// `source` anchor.
///
/// For a coordinated subject the sentence yields one atom PER ITEM (same
/// kernel, per-item subject), combined by the coordination's own
/// conjunction; `both`/`either` group markers are recorded in the AST but do
/// not change the logic (`both A and B` conjoins exactly as `A and B` does).
/// Subject-`no` quantifiers are normalized here (module docs, § Index vs
/// logic).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BehaviorAtom {
    pub subject: SubjectSkeleton,
    pub atom: Atom,
    pub force: Option<Force>,
    pub act: SpeechAct,
    /// The lossless anchor: the canonical render of the core with this
    /// item as sole subject (no frames, no exception, no purpose),
    /// INCLUDING its surface negation sites. Re-parsing it and re-deriving
    /// its claim formula reproduces this atom's enclosing sub-formula —
    /// the atom with its own `Not` wrapper — not the bare atom (module
    /// docs, § Anchors). Downstream equality/entailment must compare
    /// formulas re-derived from anchors (or the ASTs), never the digest
    /// fields alone and never anchor strings alone.
    pub source: String,
}

/// The canonical LOGICAL projection of a behavior (or admissibility) atom:
/// the subject digest (quantifier + restrictor + head) and the behavior
/// kernel (words, manner, objects, roles) — WITHOUT the speech act, the
/// force, and the source anchor. This is the logical KEY of an atom: two
/// atoms with equal propositions state the same thing about the same
/// subject, even when one arrived as an obligation and the other as a
/// prohibition's negated body or a description (`The request shall be
/// logged.` / `The request is logged.` / the atom under `The request shall
/// not be logged.`). Act, force, and anchor are surface provenance and stay
/// on [`BehaviorAtom`]; [`crate::relate`] compares propositions, never
/// anchors and never acts.
///
/// LOSSINESS-AWARE (round 6): the subject digest and every object/role
/// digest carry a full-fidelity identity string (`full` — lowercased
/// render of modifiers + head + `of`-chain + relative, determiner
/// excluded), so proposition equality is NOT satisfied by a coarse
/// (quantifier + head) match alone. Two atoms whose coarse digests meet
/// but whose `full` strings differ — `each request that is authenticated`
/// vs `each request that is unauthenticated` — have UNEQUAL propositions,
/// and [`crate::relate`] answers `Unknown` for them: never `Yes` (the
/// relatives differ), and never `No` (disjointness of the restrictions is
/// not provable syntactically).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proposition {
    pub subject: SubjectSkeleton,
    pub atom: Atom,
}

impl BehaviorAtom {
    /// The atom's [`Proposition`] — its logical key (see there).
    pub fn proposition(&self) -> Proposition {
        Proposition {
            subject: self.subject.clone(),
            atom: self.atom.clone(),
        }
    }
}

/// The sentence-internal contract shape: an assumption (trivially `Top` at
/// ingest — non-trivial assumptions arrive only by pairing between
/// sentences, see [`ContractFormula::paired`]) and a guarantee that is the
/// sentence's own conditional, applicability → claim.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContractFormula {
    /// `Top` at ingest. When graph-side pairing later selects real
    /// assumption sources for this guarantee, the paired (A, G) SUPERSEDES
    /// this lone (⊤, G) — the two are never conjoined; [`Self::paired`]
    /// encodes that doctrine by REPLACING the assumption.
    ///
    /// DERIVED from [`Self::sources`]: always the conjunction of the
    /// CONTRACT-FORMING source RELIED formulas — non-envelope AND PROVEN
    /// (round 9) AND not merely RECOMMENDED AND responsible-subject keys
    /// DISJOINT (round 10; see
    /// [`AssumptionSource::contract_forming`] and [`Self::paired`]).
    /// Round 7: A is built from the
    /// reliances, not from the source formulas, which are evidence; `Top`
    /// for none, the lone reliance for one. Envelope sources are
    /// compatibility data, not assumption conjuncts (round 6), and
    /// UNPROVEN sources are CANDIDATES the graph layer must confirm —
    /// they are retained in [`Self::sources`] but leave the assumption
    /// unchanged (round 9). [`Self::paired`] keeps the two in sync.
    pub assumption: Formula,
    /// `applicability → claim`, i.e. `Or(Not(applicability), claim)` — with
    /// the `Top` applicability simplified away: an unconditional sentence's
    /// guarantee is its claim.
    pub guarantee: Formula,
    /// The typed assumption sources the assumption was derived from — empty
    /// at ingest. Round 5: [`Self::paired`] RETAINS its sources so the edge
    /// kind of each conjunct stays checkable (a permission stays visibly an
    /// envelope, a reliance stays visibly undischargeable) instead of being
    /// erased into an untyped `And`. `#[serde(default)]` keeps pre-round-5
    /// serialized contracts readable.
    #[serde(default)]
    pub sources: Vec<AssumptionSource>,
}

/// How an assumption source relates to the guarantee it is paired with —
/// the typed edges of the causal pair {A₁…Aₗ} ⇒ G. Which sentence supplies
/// which source, and whether a candidate source is valid, is daemon/graph
/// work; this crate only fixes the vocabulary and the pairing algebra.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    /// The guarantee relies on an environment occurrence actually taking
    /// place, or on an assumed state actually holding (occurrence/state
    /// reliance). A reliance is an assumption only; nothing here can
    /// discharge another contract's assumption.
    OccurrenceReliance,
    /// Another component's guarantee discharges this assumption — the ONLY
    /// edge kind that can discharge: a guarantee asserts occurrence, so it
    /// can witness what an assumption awaits.
    GuaranteeDischarge,
    /// An admissibility bounds the environment behavior this guarantee must
    /// tolerate. An envelope only WIDENS the tolerated environment behavior
    /// (a permission never narrows what must be withstood); being
    /// admissibility (see [`AtomRef::Admissibility`]), it never witnesses
    /// occurrence and never discharges. Round 6: an envelope source is
    /// retained in [`ContractFormula::sources`] but NEVER enters the paired
    /// assumption formula — it is compatibility data, not an assumption
    /// conjunct, so saturation never negates it (see
    /// [`ContractFormula::paired`]).
    AdmissibilityEnvelope,
}

/// How a source's responsible-subject keys relate to its target's
/// (round 10): computed from
/// [`crate::semantics::responsible_subject_keys`] on BOTH sides — a
/// passive's stated agent, not its patient — by
/// [`AssumptionSource::for_guarantee`]. DOCTRINE: so-lang REPORTS, never
/// decides. The keys are the TENTATIVE textual identity (aliases — `specd`
/// vs `the daemon` — and two components sharing a head word are daemon-side
/// component-identity work), so [`SubjectRelation::SharedKeys`] is a RED
/// FLAG the graph layer must resolve with real component identity before
/// forming the edge, not a proof of self-reliance — and
/// [`SubjectRelation::DisjointKeys`] is not a proof of distinctness either.
/// Conservatively, only [`SubjectRelation::DisjointKeys`] sources can be
/// contract-forming ([`AssumptionSource::contract_forming`]); shared-key
/// sources construct fine and ride as candidates. This supersedes the
/// round-6 hard rejection (`PairingError::SameSubject`, removed): subject
/// keys were documented candidate-only data, and hard-rejecting on a
/// textual collision guaranteed false rejections for aliases and shared
/// head words while pretending to a certainty the keys never had.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SubjectRelation {
    /// No responsible-subject key is shared between source and target.
    DisjointKeys,
    /// At least one responsible-subject key is shared: a red flag for the
    /// graph layer — candidate only, never contract-forming.
    SharedKeys,
}

/// One selected assumption source: the edge kind it arrives by, the formula
/// it contributes to the paired assumption, and — round 5 — the provenance
/// needed to VALIDATE that pairing: the source sentence's speech act and
/// force. The act × kind matrix is API-encoded in [`Self::from_sentence`],
/// so a permission can no longer be quietly treated as occurrence evidence,
/// nor a recommendation as a discharge. Responsible-subject identity checks
/// (is the discharging guarantee really about the awaited component?) remain
/// daemon-side future work — the caveat on [`crate::semantics::subject_keys`]
/// is unchanged; round 10 records the textual comparison as
/// [`Self::subject_relation`] instead of deciding on it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AssumptionSource {
    pub kind: EdgeKind,
    /// The source sentence's own formula — the EVIDENCE the edge rests on:
    /// what the source sentence claims, under its own circumstances.
    pub formula: Formula,
    /// What the paired guarantee actually RELIES ON (round 7). The edge is
    /// evidence + reliance: `formula` is the evidence, `relied` the
    /// reliance, and [`ContractFormula::paired`] conjoins the RELIED
    /// formulas (contract-forming only: non-envelope AND proven, round 9;
    /// AND not merely recommended AND responsible-subject keys disjoint,
    /// round 10 — see [`Self::contract_forming`])
    /// into A — the assumption trusts exactly what
    /// the guarantee needs, not everything the source happens to say.
    /// DEFAULT: the constructors that take no explicit reliance set
    /// `relied` to the source formula (documented default — relying on the
    /// whole of what the source claims), which reproduces the round-6
    /// pairing exactly; [`Self::for_guarantee_with_relied`] narrows it,
    /// validating that the source formula provably does not FAIL to entail
    /// the reliance. Pre-round-7 serialized sources carry no `relied`
    /// field and deserialize to the default.
    pub relied: Formula,
    /// The speech act of the source sentence.
    pub act: SpeechAct,
    /// The normative force of the source sentence, when it has one.
    pub force: Option<Force>,
    /// Whether the reliance is PROVEN (round 8): `true` iff
    /// [`crate::relate::implies`]`(formula, relied)` answered
    /// [`crate::relate::Ternary::Yes`] at construction (`Unknown` builds
    /// with `false` — accepted, per the round-7 conservatism, but visibly
    /// unproven). DOCTRINE: only proven reliances should become
    /// contract-forming edges; an unproven source is a CANDIDATE the
    /// graph layer must confirm or discard — this flag makes the
    /// distinction visible instead of leaving it implicit in a judgment
    /// the constructor already ran and threw away. The default-relied
    /// constructors ([`Self::from_sentence`], [`Self::for_guarantee`])
    /// still compute it honestly (relying on the whole source formula is
    /// self-entailment, so it is `true` there). Serde: pre-round-8
    /// serialized sources carry no `proven` field and deserialize to
    /// `false` (documented: an old edge is treated as unproven until
    /// re-derived, never silently promoted to proven).
    #[serde(default)]
    pub proven: bool,
    /// How the source's responsible-subject keys relate to the target's
    /// (round 10, see [`SubjectRelation`]): candidate data, reported not
    /// decided. [`Self::contract_forming`] requires
    /// [`SubjectRelation::DisjointKeys`] — a shared-key source rides as a
    /// candidate until the graph layer resolves component identity. Serde:
    /// pre-round-10 sources carry no field and load as `DisjointKeys` —
    /// the documented pre-round-10 reading (a stored `for_guarantee` edge
    /// could only exist GRAMMATICALLY disjoint, because the removed
    /// rejection compared grammatical `subject_keys`; a passive-agent
    /// source that is SharedKeys under the round-10 RESPONSIBLE reading
    /// was constructible then and still loads as `DisjointKeys`;
    /// a stored `from_sentence` edge entered A regardless, and
    /// `DisjointKeys` preserves exactly that behavior until re-derivation
    /// refreshes it honestly). The default lives in the manual
    /// `Deserialize` below.
    pub subject_relation: SubjectRelation,
    /// Whether the reliance was selected EXPLICITLY (round 11, change 3):
    /// `true` only for sources built through
    /// [`Self::for_guarantee_with_relied`] — the graph-edge entry point,
    /// where the target's awaited assumption is passed as the `relied`
    /// formula. The default-relied constructors ([`Self::from_sentence`],
    /// [`Self::for_guarantee`]) set `false`: their reliance is the WHOLE
    /// source conditional (a migration/evidence default, round 10
    /// doctrine), and [`Self::contract_forming`] now requires
    /// `explicit_relied`, so a default-relied source is a PERMANENT
    /// CANDIDATE — visible evidence, never an assumption conjunct — until
    /// re-derived with an explicit reliance. Serde: pre-round-11 sources
    /// carry no field and load as `false` — the CONSERVATIVE direction
    /// (old JSON edges become candidates rather than silently keeping the
    /// power to relieve a guarantee; re-derivation with an explicit
    /// reliance restores contract forming honestly).
    #[serde(default)]
    pub explicit_relied: bool,
}

impl SubjectRelation {
    /// The serde/legacy default: see [`AssumptionSource::subject_relation`].
    fn default_legacy() -> SubjectRelation {
        SubjectRelation::DisjointKeys
    }
}

// Manual Deserialize: `relied` defaults to the SOURCE FORMULA (the sibling
// field), which `#[serde(default)]` cannot express — pre-round-7 sources
// must keep their round-6 meaning (rely on the whole source formula).
impl<'de> Deserialize<'de> for AssumptionSource {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Raw {
            kind: EdgeKind,
            formula: Formula,
            #[serde(default)]
            relied: Option<Formula>,
            act: SpeechAct,
            #[serde(default)]
            force: Option<Force>,
            // Round 8: pre-round-8 sources carry no `proven` field and
            // load as UNPROVEN — even when `relied` defaults to the source
            // formula (which a re-derivation would prove). Deserialization
            // restores what was recorded; it never runs judgments.
            #[serde(default)]
            proven: bool,
            // Round 10: pre-round-10 sources carry no `subject_relation`
            // and load as DisjointKeys — the documented pre-round-10
            // reading (see the field's doc on [`AssumptionSource`]).
            #[serde(default = "SubjectRelation::default_legacy")]
            subject_relation: SubjectRelation,
            // Round 11: pre-round-11 sources carry no `explicit_relied`
            // and load as `false` — the conservative direction: an old
            // edge is a candidate until re-derived with an explicit
            // reliance (see the field's doc on [`AssumptionSource`]).
            #[serde(default)]
            explicit_relied: bool,
        }
        let raw = Raw::deserialize(deserializer)?;
        let relied = raw.relied.unwrap_or_else(|| raw.formula.clone());
        Ok(AssumptionSource {
            kind: raw.kind,
            formula: raw.formula,
            relied,
            act: raw.act,
            force: raw.force,
            proven: raw.proven,
            subject_relation: raw.subject_relation,
            explicit_relied: raw.explicit_relied,
        })
    }
}

/// Why a candidate assumption source is invalid for the requested edge kind.
/// Every variant names the doctrine it enforces; `kind()` gives the stable
/// snake_case name for telemetry.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum PairingError {
    /// A permission paired as anything but an admissibility envelope.
    #[error("a permission only widens the admissibility envelope: it never witnesses occurrence and never discharges, so pair it as an admissibility envelope or not at all")]
    PermissionOnlyEnvelope,
    /// A recommendation paired as a discharge or an envelope.
    #[error("a recommendation is not binding: it can be relied on as an occurrence, but it can never discharge an assumption and it is no admissibility envelope")]
    RecommendationOnlyReliance,
    /// A binding obligation/prohibition paired as an envelope.
    #[error("a binding sentence asserts behavior: pair it as a guarantee discharge or an occurrence reliance, never as an admissibility envelope")]
    BindingNoEnvelope,
    /// A description (capability included) paired as a discharge or envelope.
    #[error("a description states how the system is: it can be relied on as state, but it carries no normative force to discharge an assumption and it is no admissibility envelope")]
    DescriptionOnlyReliance,
    /// A definition offered as an assumption source at all.
    #[error("a definition establishes vocabulary: it has no behavioral content to serve as an assumption source")]
    NotBehavioral,
    // Round 10: the round-6 `SameSubject` variant is REMOVED — a shared
    // responsible-subject key no longer rejects construction; it is
    // recorded as [`SubjectRelation::SharedKeys`], candidate-only data the
    // graph layer resolves with real component identity (see
    // [`SubjectRelation`]).
    /// An explicit reliance the source formula PROVABLY does not entail
    /// (round 7): [`crate::relate::implies`] answered `No`. `Unknown` is
    /// allowed — conservative: the structural rules often cannot prove an
    /// entailment that holds, and a pairing is daemon/graph-validated
    /// anyway — but a proven non-entailment means the edge's evidence does
    /// not support its reliance.
    #[error("the source sentence provably does not entail the relied formula: an edge's evidence must support its reliance — rely on what the source actually claims, or pick a source that claims it")]
    SourceDoesNotSupportRelied,
    /// A relied formula that is (or simplifies to) `Bottom` (round 8): a
    /// vacuous reliance makes the paired assumption unsatisfiable, so the
    /// saturated form `G ∨ ¬A` is a tautology — the guarantee is erased
    /// rather than conditioned. Supersedes the round-7 pin that accepted
    /// `relied: Bottom` under the Unknown-is-accepted conservatism: the
    /// erasure is provable from the shape alone, so accepting it was never
    /// conservative.
    #[error("the relied formula is unsatisfiable (⊥): a vacuous reliance erases the guarantee — the saturated form G ∨ ¬A becomes a tautology — so rely on what the guarantee actually needs, or drop the pairing")]
    VacuousRelied,
}

impl PairingError {
    /// A stable snake_case name for telemetry.
    pub fn kind(&self) -> &'static str {
        match self {
            PairingError::PermissionOnlyEnvelope => "permission_only_envelope",
            PairingError::RecommendationOnlyReliance => "recommendation_only_reliance",
            PairingError::BindingNoEnvelope => "binding_no_envelope",
            PairingError::DescriptionOnlyReliance => "description_only_reliance",
            PairingError::NotBehavioral => "not_behavioral",
            PairingError::SourceDoesNotSupportRelied => "source_does_not_support_relied",
            PairingError::VacuousRelied => "vacuous_relied",
        }
    }
}

impl AssumptionSource {
    /// Build a VALIDATED assumption source from a source sentence — the act
    /// × kind matrix, API-encoded:
    ///
    /// * Permission → only [`EdgeKind::AdmissibilityEnvelope`];
    /// * Recommendation → only [`EdgeKind::OccurrenceReliance`] (never a
    ///   discharge: nothing merely recommended witnesses occurrence);
    /// * Obligation / Prohibition (binding) → [`EdgeKind::GuaranteeDischarge`]
    ///   or [`EdgeKind::OccurrenceReliance`];
    /// * Description (capability included) → [`EdgeKind::OccurrenceReliance`]
    ///   (state reliance);
    /// * Definition → [`PairingError::NotBehavioral`].
    ///
    /// The source formula is the sentence's own conditional, applicability →
    /// claim — the same shape a guarantee takes (see
    /// [`contract_formula`]) — so what the assumption trusts is exactly what
    /// the source sentence claims, under its own circumstances.
    ///
    /// SUPERSEDED AS THE ENTRY POINT (round 6, documented choice): prefer
    /// [`Self::for_guarantee`], which additionally OBSERVES the
    /// source-vs-target responsible-subject relation (round 10:
    /// [`SubjectRelation`] — recorded, no longer a rejection). This
    /// constructor is kept — `#[doc(hidden)]` rather than deprecated — for
    /// callers that genuinely have no target sentence in hand (bulk
    /// re-derivation of stored sources); it applies the act × kind matrix
    /// only. With no target to compare against, `subject_relation` is set
    /// to [`SubjectRelation::DisjointKeys`] — LEGISLATED, round 10: the
    /// same reading the serde default gives a stored pre-round-10 edge
    /// (this constructor never checked subjects, and its sources always
    /// entered A; a caller that has the target must use
    /// [`Self::for_guarantee`], which observes the relation honestly).
    #[doc(hidden)]
    pub fn from_sentence(
        kind: EdgeKind,
        sentence: &Sentence,
    ) -> Result<AssumptionSource, PairingError> {
        let act = speech_act(sentence);
        validate_act_kind(kind, act)?;
        let formula = guarded_claim(sentence).expect("a non-definition sentence has a claim");
        // Documented default: the reliance is the whole source formula —
        // self-entailment, so the reliance is proven (round 8).
        let relied = formula.clone();
        let proven = crate::relate::implies(&formula, &relied) == crate::relate::Ternary::Yes;
        Ok(AssumptionSource {
            kind,
            formula,
            relied,
            act,
            force: force(sentence),
            proven,
            subject_relation: SubjectRelation::DisjointKeys,
            // Round 11: the default reliance is not an explicit selection —
            // this source is a permanent candidate (migration/evidence
            // only, see the field doc).
            explicit_relied: false,
        })
    }

    /// Build a VALIDATED assumption source for a specific target guarantee
    /// (round 6). Applies the full [`Self::from_sentence`] act × kind matrix,
    /// PLUS the target-awareness observation (round 10, superseding the
    /// round-6 hard rejection): an assumption is about the target subject's
    /// ENVIRONMENT, so the source's and target's RESPONSIBLE subject keys
    /// ([`crate::semantics::responsible_subject_keys`] — a passive's stated
    /// agent, not its patient, on both sides) are compared and the result
    /// RECORDED as [`Self::subject_relation`]. A shared key no longer
    /// rejects construction ([`PairingError::SameSubject`] is removed):
    /// keys are tentative textual identity, so a collision is a red flag
    /// for the graph layer, not a proof of self-reliance — and
    /// [`Self::contract_forming`] keeps A safe by requiring
    /// [`SubjectRelation::DisjointKeys`], so a shared-key source rides as
    /// a candidate. A definition on either side is
    /// [`PairingError::NotBehavioral`].
    ///
    /// Subject keys are still the TENTATIVE textual identity (aliases and
    /// component identity are daemon-side future work); full
    /// interface-direction and entailment validation of a pairing remains
    /// daemon/graph work. [`Self::advisory_reliance_check`] is offered as
    /// the conservative language-level piece of that work.
    ///
    /// GRAPH EDGES MUST SELECT THEIR RELIANCE EXPLICITLY (round 10,
    /// doctrine): this constructor's DEFAULT reliance is the WHOLE source
    /// conditional (`¬guard ∨ claim`), which imports the source's
    /// conditional shape into A — the target ends up assuming "whenever
    /// the source's own guard holds, its claim holds", not the occurrence
    /// or state the target actually awaits. That default exists for
    /// migration and tests; a graph edge must be built with
    /// [`Self::for_guarantee_with_relied`], passing the target's awaited
    /// assumption as the explicit `relied` formula, so A trusts exactly
    /// what the guarantee needs and the pairing validates that the source
    /// supports it.
    ///
    /// CONSEQUENCE UPDATE (round 10, superseding the round-8 reachability
    /// note): with the hard rejection gone, a same-subject envelope CAN be
    /// constructed here (recorded as [`SubjectRelation::SharedKeys`]), so
    /// [`crate::relate::envelope_compatible`]'s provable `No` arm is now
    /// reachable through this constructor as well as through graph-layer
    /// edges.
    pub fn for_guarantee(
        kind: EdgeKind,
        source: &Sentence,
        target: &Sentence,
    ) -> Result<AssumptionSource, PairingError> {
        if speech_act(target) == SpeechAct::Definition {
            return Err(PairingError::NotBehavioral);
        }
        let act = speech_act(source);
        validate_act_kind(kind, act)?;
        // Round 10: the environment question is asked of the RESPONSIBLE
        // subjects — a passive's stated agent, not its patient — on BOTH
        // sides ([`crate::semantics::responsible_subject_keys`]) — and the
        // answer is RECORDED, not decided on (see [`SubjectRelation`]).
        let source_keys = crate::semantics::responsible_subject_keys(source);
        let target_keys = crate::semantics::responsible_subject_keys(target);
        let subject_relation = if source_keys.iter().any(|k| target_keys.contains(k)) {
            SubjectRelation::SharedKeys
        } else {
            SubjectRelation::DisjointKeys
        };
        let formula = guarded_claim(source).expect("a non-definition sentence has a claim");
        // Documented default: the reliance is the whole source formula —
        // self-entailment, so the reliance is proven (round 8).
        let relied = formula.clone();
        let proven = crate::relate::implies(&formula, &relied) == crate::relate::Ternary::Yes;
        Ok(AssumptionSource {
            kind,
            formula,
            relied,
            act,
            force: force(source),
            proven,
            subject_relation,
            // Round 11: the default reliance is not an explicit selection —
            // this source is a permanent candidate (migration/evidence
            // only, see the field doc).
            explicit_relied: false,
        })
    }

    /// Build a VALIDATED assumption source with an EXPLICIT reliance
    /// (round 7): everything [`Self::for_guarantee`] validates, plus the
    /// evidence-supports-reliance rule — the source formula must not
    /// PROVABLY fail to entail `relied`
    /// ([`crate::relate::implies`] answering
    /// [`crate::relate::Ternary::No`] is
    /// [`PairingError::SourceDoesNotSupportRelied`]).
    /// [`crate::relate::Ternary::Unknown`] is ACCEPTED — conservative,
    /// documented: the structural rules often cannot prove an entailment
    /// that holds, and full entailment validation of a pairing remains
    /// daemon/graph work; a caller wanting proof can require `Yes` via
    /// [`Self::advisory_reliance_check`].
    /// ROUND 8: a relied formula that is (or simplifies to) `Bottom` is
    /// rejected as [`PairingError::VacuousRelied`] — an unsatisfiable
    /// reliance makes the saturated form `G ∨ ¬A` a tautology, erasing the
    /// guarantee (supersedes the round-7 accept-Bottom pin). The result's
    /// [`Self::proven`] flag records whether the entailment was actually
    /// proven (`Yes`) rather than merely not disproven (`Unknown`).
    ///
    /// THIS is the graph-edge entry point (round 10, doctrine — see the
    /// note on [`Self::for_guarantee`]): an edge's `relied` is the target's
    /// awaited assumption, selected explicitly; the default-relied
    /// constructors are for migration and tests only.
    pub fn for_guarantee_with_relied(
        kind: EdgeKind,
        source: &Sentence,
        target: &Sentence,
        relied: Formula,
    ) -> Result<AssumptionSource, PairingError> {
        let mut built = Self::for_guarantee(kind, source, target)?;
        if crate::relate::simplifies_to_bottom(&relied) {
            return Err(PairingError::VacuousRelied);
        }
        match crate::relate::implies(&built.formula, &relied) {
            crate::relate::Ternary::No => return Err(PairingError::SourceDoesNotSupportRelied),
            verdict => built.proven = verdict == crate::relate::Ternary::Yes,
        }
        built.relied = relied;
        // Round 11 (change 3): only this constructor selects the reliance
        // explicitly, so only its sources can be contract-forming.
        built.explicit_relied = true;
        Ok(built)
    }

    /// Is this source CONTRACT-FORMING (round 9) — does its reliance enter
    /// the paired assumption? True exactly for a non-envelope,
    /// non-RECOMMENDED source whose reliance is [`Self::proven`]: envelopes
    /// are compatibility data (round 6), an unproven reliance is a
    /// CANDIDATE edge that must not relieve the guarantee (see
    /// [`ContractFormula::paired`]), and — round 10 — a RECOMMENDED source
    /// never forms A: `should` states a preference, not an environmental
    /// fact, and conjoining it into A would silently harden the
    /// recommendation into something the guarantee is relieved by
    /// (saturation `G ∨ ¬A` reads ¬A as "the environment broke its
    /// promise", which a recommendation never made). Recommendations
    /// therefore never DISCHARGE (round 5 act × kind matrix) and never
    /// form A (round 10); a recommended reliance rides in
    /// [`ContractFormula::sources`] as a visible candidate only. Binding
    /// sources and force-free descriptions qualify as before; permission
    /// is already envelope-only. Round 10 also requires
    /// [`SubjectRelation::DisjointKeys`]: a shared-key source is a red
    /// flag the graph must resolve with component identity first, so it
    /// too rides as a candidate — this keeps A safe (conservative) without
    /// hard-rejecting construction.
    /// [`crate::relate::assumption_satisfiable`] judges the same set, so
    /// the satisfiability verdict is about the assumption actually formed.
    ///
    /// ROUND 11 (change 3): contract forming additionally requires
    /// [`Self::explicit_relied`] — the reliance must have been SELECTED
    /// (through [`Self::for_guarantee_with_relied`], passing the target's
    /// awaited assumption), not defaulted to the whole source conditional.
    /// A default reliance imports the source's own conditional shape into
    /// A ("whenever the source's guard holds, its claim holds"), which is
    /// rarely what the guarantee actually awaits; defaulted sources are
    /// therefore PERMANENT CANDIDATES (migration/evidence only), and the
    /// well-formed proven pairing ([`ContractFormula::well_formed`]) is
    /// the one place the full definition lives.
    pub fn contract_forming(&self) -> bool {
        self.kind != EdgeKind::AdmissibilityEnvelope
            && self.explicit_relied
            && self.proven
            && self.force != Some(Force::Recommended)
            && self.subject_relation == SubjectRelation::DisjointKeys
    }

    /// ADVISORY check that this source actually supplies what a guarantee
    /// relies on: does the source's formula entail `relied` (the formula the
    /// target's assumption awaits)? Conservative by construction — it is
    /// [`crate::relate::implies`] over the source formula, so
    /// [`crate::relate::Ternary::Yes`] is a proof by structural rule,
    /// [`crate::relate::Ternary::No`] a proven non-entailment, and
    /// [`crate::relate::Ternary::Unknown`] the honest default that must
    /// never be read as `No`. Advisory only: a `Yes` here does not make the
    /// pairing valid by itself (edge-kind and subject validity are the
    /// constructors' job; full entailment validation is daemon/graph work).
    pub fn advisory_reliance_check(&self, relied: &Formula) -> crate::relate::Ternary {
        crate::relate::implies(&self.formula, relied)
    }
}

/// The act × kind matrix shared by [`AssumptionSource::from_sentence`] and
/// [`AssumptionSource::for_guarantee`].
fn validate_act_kind(kind: EdgeKind, act: SpeechAct) -> Result<(), PairingError> {
    let allowed = match act {
        SpeechAct::Definition => return Err(PairingError::NotBehavioral),
        SpeechAct::Permission => matches!(kind, EdgeKind::AdmissibilityEnvelope),
        SpeechAct::Recommendation => matches!(kind, EdgeKind::OccurrenceReliance),
        SpeechAct::Obligation | SpeechAct::Prohibition => matches!(
            kind,
            EdgeKind::GuaranteeDischarge | EdgeKind::OccurrenceReliance
        ),
        SpeechAct::Description => matches!(kind, EdgeKind::OccurrenceReliance),
    };
    if !allowed {
        return Err(match act {
            SpeechAct::Permission => PairingError::PermissionOnlyEnvelope,
            SpeechAct::Recommendation => PairingError::RecommendationOnlyReliance,
            SpeechAct::Obligation | SpeechAct::Prohibition => PairingError::BindingNoEnvelope,
            SpeechAct::Description => PairingError::DescriptionOnlyReliance,
            SpeechAct::Definition => PairingError::NotBehavioral,
        });
    }
    Ok(())
}

impl ContractFormula {
    /// The saturated form `G ∨ ¬A` — the theory's `G ∪ ¬A` in symbolic
    /// form: what the component owes once environments that break the
    /// assumption relieve it. With the ingest assumption `Top`, this is the
    /// guarantee itself.
    pub fn saturated(&self) -> Formula {
        if self.assumption == Formula::Top {
            return self.guarantee.clone();
        }
        Formula::Or {
            items: vec![
                self.guarantee.clone(),
                Formula::not(self.assumption.clone()),
            ],
        }
    }

    /// The paired contract: the causal pair {A₁…Aₗ} ⇒ G. Returns a NEW
    /// contract whose assumption is the conjunction of the
    /// CONTRACT-FORMING source RELIED formulas — the sources that are
    /// non-envelope, not merely RECOMMENDED (round 10 — a proven
    /// recommended reliance rides as a candidate; conjoining it would
    /// silently harden a `should` into an environmental assumption, see
    /// [`AssumptionSource::contract_forming`]), AND
    /// [`AssumptionSource::proven`] (round 9, superseding
    /// the round-7/8 shape that conjoined every non-envelope reliance:
    /// the round-8 doctrine already said only proven reliances should
    /// become contract-forming edges, and conjoining an unproven reliance
    /// into A let saturation `G ∨ ¬A` RELIEVE the guarantee on the
    /// strength of an edge whose evidence never supported it). Round 7:
    /// the edge is evidence + reliance, and A is built from the reliances
    /// — see [`AssumptionSource::relied`]; with the default reliance this
    /// is exactly the round-6 conjunction of source formulas. A single
    /// proven reliance stands alone; none — envelope-only or
    /// candidate-only pairing included — is the unchanged `Top`. The
    /// result REPLACES the provisional ingest assumption — the
    /// supersession doctrine: a paired (A, G) supersedes the lone (⊤, G),
    /// and the two are never conjoined into one contract. The guarantee
    /// is untouched. [`Self::saturated`] over the result gives
    /// `G ∨ ¬(∧ᵢAᵢ)`.
    ///
    /// UNPROVEN SOURCES ARE CANDIDATES (round 9): they are RETAINED in
    /// [`Self::sources`] — visibly unproven, for the graph layer to
    /// confirm (re-derive at `Yes`) or discard — but they never enter A:
    /// a candidate edge does not relieve the guarantee of anything.
    ///
    /// ENVELOPES ARE NOT ASSUMPTION CONJUNCTS (round 6, superseding the
    /// round-5 shape that conjoined them): an
    /// [`EdgeKind::AdmissibilityEnvelope`] source is COMPATIBILITY data —
    /// the environment MAY do this, and the pairing must stay compatible
    /// with it — so it only WIDENS the tolerated environment behavior.
    /// Conjoining it into A and then negating it under [`Self::saturated`]
    /// (`G ∨ ¬A`) would read the permission as a behavior-set complement,
    /// which a permission is not. Envelope sources are therefore RETAINED
    /// in [`Self::sources`] (compatibility checking needs them) but never
    /// enter the assumption formula and never get negated by saturation;
    /// their formal denotation (widening A) is graph-layer future work.
    ///
    /// Only [`EdgeKind::GuaranteeDischarge`] sources can later be
    /// discharged; reliance sources merely state what the environment is
    /// trusted to do. Selecting sources is daemon/graph work; per-source
    /// act × kind validity is API-encoded in
    /// [`AssumptionSource::for_guarantee`]. The result RETAINS its sources
    /// (round 5): `assumption` stays the derived conjunction of the
    /// contract-forming (non-envelope AND proven, round 9; AND not merely
    /// recommended AND responsible-subject keys disjoint, round 10 —
    /// [`AssumptionSource::contract_forming`]) source RELIED
    /// formulas, and `sources` keeps each
    /// conjunct's edge kind, evidence formula, and provenance checkable.
    pub fn paired(&self, sources: &[AssumptionSource]) -> ContractFormula {
        if sources.is_empty() {
            return self.clone();
        }
        let mut items: Vec<Formula> = sources
            .iter()
            .filter(|s| s.contract_forming())
            .map(|s| s.relied.clone())
            .collect();
        let assumption = match items.len() {
            0 => Formula::Top,
            1 => items.remove(0),
            _ => Formula::And { items },
        };
        ContractFormula {
            assumption,
            guarantee: self.guarantee.clone(),
            sources: sources.to_vec(),
        }
    }

    /// The WELL-FORMED PROVEN PAIRING summary — the one API for pairing
    /// well-formedness AND verification status (round 11, changes 3–4,
    /// folded: one judgment, one name). DATA ONLY: the graph layer
    /// decides; nothing here rejects or repairs.
    ///
    /// # Definition (rustdoc anchor — the single normative statement,
    /// mirrored in `docs/grammar/semantics.md` § "The well-formed proven
    /// pairing"; everything else cross-links here)
    ///
    /// A paired contract is a WELL-FORMED PROVEN pairing when every
    /// assumption-side (non-envelope) source satisfies all of:
    ///
    /// 1. **Explicit non-Bottom relied** — the reliance was selected
    ///    through [`AssumptionSource::for_guarantee_with_relied`]
    ///    ([`AssumptionSource::explicit_relied`]; Bottom is already
    ///    rejected at construction, [`PairingError::VacuousRelied`]).
    /// 2. **Proven** — the source formula entails the relied formula at
    ///    [`crate::relate::Ternary::Yes`] ([`AssumptionSource::proven`]).
    /// 3. **Environment-side** — the source's and target's RESPONSIBLE
    ///    subject keys are disjoint
    ///    ([`SubjectRelation::DisjointKeys`]).
    /// 4. **Act/force admissible** — the act × kind matrix holds
    ///    (API-encoded at construction) and the source is not merely
    ///    RECOMMENDED (a `should` never forms A).
    ///
    /// and the pairing as a whole satisfies:
    ///
    /// 5. **Assumption satisfiability not refuted** —
    ///    [`crate::relate::assumption_satisfiable`] is not
    ///    [`crate::relate::Ternary::No`] (`Unknown` is the good case —
    ///    satisfiability is never provable syntactically).
    ///
    /// # Verification doctrine (change 4)
    ///
    /// `refines`/`assess` over a paired contract whose assumption
    /// satisfiability is REFUTED (`No`) is VACUOUS — the saturated form
    /// `G ∨ ¬A` is a tautology — and must not be reported as a proven
    /// relation: [`crate::relate::refines`] returns `Unknown` when either
    /// side's formed assumption is refuted. `Unknown` satisfiability
    /// means downstream results carry that caveat (not disproven, never
    /// certified).
    ///
    /// # Fields (legislated, round 11; COMPLETED round 12, change 2 —
    /// superseding the round-11 field note that carried only conditions
    /// 1, 2, and 5)
    ///
    /// The booleans quantify over the NON-ENVELOPE sources (envelopes
    /// are compatibility data, never assumption conjuncts) and are
    /// vacuously `true` when no such source exists; the two ternaries are
    /// the crate's existing refutation-only judgments. Round 12 adds the
    /// AGGREGATE: [`WellFormedness::all_sources_contract_forming`] gates
    /// on ALL FOUR per-source conditions at once (it is
    /// [`AssumptionSource::contract_forming`] quantified over the
    /// assumption side), so the environment-side (condition 3) and
    /// act/force (condition 4) gates the round-11 fields omitted are now
    /// in the summary — a pairing whose sources are all explicit and
    /// proven but SHARED-KEY or merely RECOMMENDED shows `false` there.
    /// [`WellFormedness::source_issues`] itemizes WHY, per source.
    pub fn well_formed(&self) -> WellFormedness {
        let assumption_side = || {
            self.sources
                .iter()
                .filter(|s| s.kind != EdgeKind::AdmissibilityEnvelope)
        };
        let source_issues = self
            .sources
            .iter()
            .enumerate()
            .filter_map(|(index, s)| {
                let mut reasons = Vec::new();
                if s.kind == EdgeKind::AdmissibilityEnvelope {
                    // BY DESIGN, not a defect: an envelope is compatibility
                    // data and never an assumption conjunct (round 6). The
                    // reason is recorded so the itemization is total over
                    // the sources, and the per-source gates below are not
                    // judged for it (they are assumption-side questions).
                    reasons.push(SourceIssueReason::EnvelopeKind);
                } else {
                    if !s.explicit_relied {
                        reasons.push(SourceIssueReason::NotExplicitRelied);
                    }
                    if !s.proven {
                        reasons.push(SourceIssueReason::NotProven);
                    }
                    if s.subject_relation == SubjectRelation::SharedKeys {
                        reasons.push(SourceIssueReason::SharedSubjectKeys);
                    }
                    if s.force == Some(Force::Recommended) {
                        reasons.push(SourceIssueReason::RecommendedForce);
                    }
                }
                (!reasons.is_empty()).then_some(SourceIssue { index, reasons })
            })
            .collect();
        WellFormedness {
            all_contract_forming_explicit: assumption_side().all(|s| s.explicit_relied),
            all_proven: assumption_side().all(|s| s.proven),
            all_sources_contract_forming: assumption_side().all(AssumptionSource::contract_forming),
            source_issues,
            assumption_satisfiability: crate::relate::assumption_satisfiable(self),
            envelope_compatibility: crate::relate::envelope_compatible(self),
        }
    }
}

/// The verification summary of a paired contract — see
/// [`ContractFormula::well_formed`] (the definition anchor). Data only;
/// the graph layer decides what to do with it.
///
/// THE ONE-CALL VERDICT (round 12, change 2):
/// [`Self::all_sources_contract_forming`] is the aggregate boolean — a
/// consumer asking "does this pairing contract-form as paired?" reads
/// that field and the two ternaries; every other field is a DIAGNOSTIC
/// that itemizes or narrows the aggregate, never a substitute for it
/// (the round-11 booleans alone displayed `true` for pairings whose
/// sources were shared-key or merely recommended — nothing was actually
/// forming).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WellFormedness {
    /// DIAGNOSTIC: every non-envelope source carries an EXPLICITLY
    /// selected reliance ([`AssumptionSource::explicit_relied`]).
    /// Vacuously true with no non-envelope sources.
    pub all_contract_forming_explicit: bool,
    /// DIAGNOSTIC: every non-envelope source's reliance is PROVEN
    /// ([`AssumptionSource::proven`]). Vacuously true with no
    /// non-envelope sources.
    pub all_proven: bool,
    /// THE AGGREGATE (round 12, change 2): every non-envelope source is
    /// [`AssumptionSource::contract_forming`] — explicit AND proven AND
    /// environment-side ([`SubjectRelation::DisjointKeys`]) AND not
    /// merely recommended: the full per-source half of the well-formed
    /// proven pairing definition, in one boolean. Vacuously true with no
    /// non-envelope sources (LEGISLATED: envelopes are compatibility
    /// data by design and never count against the aggregate — their
    /// judgment is [`Self::envelope_compatibility`]). Serde: absent in
    /// pre-round-12 JSON and loads as `false` — the conservative
    /// direction (an old summary is re-derived rather than trusted to
    /// have formed).
    #[serde(default)]
    pub all_sources_contract_forming: bool,
    /// DIAGNOSTIC (round 12, change 2): the per-source itemization of
    /// everything the aggregate saw, by source index into
    /// [`ContractFormula::sources`]. A source with no issues has no
    /// entry. Envelope sources carry the single reason
    /// [`SourceIssueReason::EnvelopeKind`] — recorded so the itemization
    /// is total, DOCUMENTED AS BY-DESIGN, not a defect (an envelope is
    /// never an assumption conjunct, round 6). Serde: absent in
    /// pre-round-12 JSON and loads as empty.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_issues: Vec<SourceIssue>,
    /// [`crate::relate::assumption_satisfiable`] over this contract:
    /// `No` is a refutation (the pairing is vacuous), `Unknown` the good
    /// case; `Yes` is never produced.
    pub assumption_satisfiability: crate::relate::Ternary,
    /// [`crate::relate::envelope_compatible`] over this contract: `No` is
    /// a proven envelope violation, `Unknown` the good case; `Yes` is
    /// never produced.
    pub envelope_compatibility: crate::relate::Ternary,
}

/// One source's issues in a [`WellFormedness`] summary (round 12,
/// change 2): the index of the source in [`ContractFormula::sources`]
/// and every reason it does not contract-form, in the fixed order of
/// [`SourceIssueReason`]'s declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceIssue {
    pub index: usize,
    pub reasons: Vec<SourceIssueReason>,
}

/// Why a source in a [`WellFormedness`] summary does not contract-form
/// (round 12, change 2). The first four mirror the per-source conditions
/// of the well-formed proven pairing ([`ContractFormula::well_formed`]);
/// the last records the envelope kind — BY-DESIGN data, not a defect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SourceIssueReason {
    /// The reliance was defaulted, not selected
    /// ([`AssumptionSource::explicit_relied`] is `false`) — condition 1.
    NotExplicitRelied,
    /// The source formula does not provably entail the reliance
    /// ([`AssumptionSource::proven`] is `false`) — condition 2.
    NotProven,
    /// The source and target share a responsible-subject key
    /// ([`SubjectRelation::SharedKeys`]) — condition 3.
    SharedSubjectKeys,
    /// The source is merely RECOMMENDED (`should` never forms A) —
    /// condition 4.
    RecommendedForce,
    /// The source is an [`EdgeKind::AdmissibilityEnvelope`] — recorded
    /// for totality, DOCUMENTED AS BY-DESIGN: an envelope is
    /// compatibility data, never an assumption conjunct (round 6), so
    /// this reason is not a defect and never counts against
    /// [`WellFormedness::all_sources_contract_forming`].
    EnvelopeKind,
}

/// The formula of one clause group: a single guard atom, or the group's own
/// `and`/`or` over its items — the surface structure preserved, not
/// flattened. Each guard atom is anchored by its clause's canonical render
/// and carries the frame role it guards under (round 10).
fn group_formula(group: &ClauseGroup, role: GuardRole) -> Formula {
    let mut items: Vec<Formula> = clause_group_skeletons(group)
        .into_iter()
        .zip(&group.items)
        .map(|(clause, ast)| Formula::Atom {
            atom: AtomRef::Guard {
                clause,
                source: ast.render(),
                role,
            },
        })
        .collect();
    if items.len() == 1 {
        return items.remove(0);
    }
    match group.conj {
        Some(Conj::Or) => Formula::Or { items },
        // `and`, or the unreachable conj-less multi-item group.
        _ => Formula::And { items },
    }
}

/// The applicability formula of a sentence: scopes ∧ states ∧ trigger ∧
/// ¬exception, each frame's clause group keeping its own `and`/`or`
/// structure, each guard atom carrying its frame's [`GuardRole`]
/// (round 10 — the flattening no longer erases WHICH circumstance family
/// a clause guarded under). An ubiquitous sentence (no frames, no
/// exception) is `Top`.
pub fn applicability(sentence: &Sentence) -> Formula {
    let mut parts: Vec<Formula> = Vec::new();
    for frame in &sentence.frames.scopes {
        parts.push(group_formula(&frame.clause, GuardRole::Scope));
    }
    for frame in &sentence.frames.states {
        parts.push(group_formula(&frame.clause, GuardRole::State));
    }
    if let Some(trigger) = &sentence.frames.trigger {
        parts.push(group_formula(
            &trigger.clause,
            GuardRole::Trigger { kind: trigger.kind },
        ));
    }
    if let Some(exception) = &sentence.exception {
        parts.push(Formula::not(group_formula(
            &ClauseGroup::single(exception.clone()),
            GuardRole::Exception,
        )));
    }
    match parts.len() {
        0 => Formula::Top,
        1 => parts.remove(0),
        _ => Formula::And { items: parts },
    }
}

/// The per-item subject digest of a behavior atom, with the subject-`no`
/// normalization (module docs, § Index vs logic): a `no` determiner becomes
/// [`Quantifier::Universal`] because the negation it contributes is already
/// carried — exactly once — by the combined claim polarity's `Not` wrapper.
fn normalized_subject(np: &Np) -> SubjectSkeleton {
    let mut subject = subject_skeleton_of(np);
    if subject.quantifier == Quantifier::Negative {
        subject.quantifier = Quantifier::Universal;
    }
    subject
}

/// The lossless anchor of one behavior atom: the canonical render of the
/// core with THIS item as its whole subject — and, for an `either … or …`
/// deontic (round 6), THIS alternative as its whole verb phrase — exactly
/// the material the atom digests, no frames, no exception, no purpose.
/// Re-parseable as a sentence core.
fn atom_anchor(core: &Core, np: &Np, alternative: Option<&Vp>) -> String {
    let subject = NpGroup::Single(np.clone());
    match core {
        Core::Description {
            copula,
            adverb,
            predicate,
            agent,
            roles,
            ..
        } => Core::Description {
            subject,
            copula: *copula,
            adverb: *adverb,
            predicate: predicate.clone(),
            agent: agent.clone(),
            roles: roles.clone(),
        }
        .render(),
        Core::Deontic {
            modal, negated, vp, ..
        } => Core::Deontic {
            subject,
            modal: *modal,
            negated: *negated,
            vp: match alternative {
                Some(alt) => VpGroup::Single(alt.clone()),
                None => vp.clone(),
            },
        }
        .render(),
        // Unreachable from `claim_formula`: definitions have no claim.
        Core::Definition { .. } => core.render(),
    }
}

/// The claim formula of a sentence: its behavior (or admissibility) atom,
/// negated when its polarity is negative. A coordinated subject yields one
/// atom per item — same kernel, per-item subject digest and anchor —
/// combined by the subject's own conjunction (`and`/`both` → `And`,
/// `or`/`either` → `Or`; the group marker does not change the logic), and
/// negation is composed PER ITEM: the claim-level site (a deontic `not` or
/// a description `never`) XORs with each item's OWN `no` determiner, so
/// `shall not run` over and-subjects is ∧ᵢ ¬run(subjectᵢ), while `No pump
/// and the valve shall run.` is ¬run(pump) ∧ run(valve) — a sibling
/// item's `no` never leaks onto a plain item. (The COMBINED polarity of
/// [`crate::semantics::claim_polarity`] flips on "any item is a `no`
/// item", which is right for a single subject; here the group flip is
/// XORed back out and re-composed with each item's own determiner.)
/// `None` only for definitions: vocabulary has no claim.
pub fn claim_formula(sentence: &Sentence) -> Option<Formula> {
    let assertion = match denote(sentence) {
        Denotation::Vocabulary { .. } => return None,
        Denotation::Behavior(assertion) | Denotation::Admissibility(assertion) => assertion,
    };
    let kernels = claim_atoms(&assertion.claim);
    // Round 6: an `either … or …` deontic yields one kernel PER ALTERNATIVE;
    // each pairs with its own verb phrase for the anchor. Single-vp claims
    // (state, capability, single deontic) pair their one kernel with `None`
    // — the anchor is the core as written.
    let alternatives: Vec<Option<&Vp>> = match &assertion.claim {
        Claim::Action {
            vp: VpGroup::Alternatives { items },
            ..
        }
        | Claim::Admissible {
            vp: VpGroup::Alternatives { items },
        } => items.iter().map(Some).collect(),
        _ => vec![None],
    };
    debug_assert_eq!(kernels.len(), alternatives.len());
    // Recover the claim-level negation site by XORing the group-level `no`
    // flip back out of the combined polarity; each atom then re-composes it
    // with its own item's determiner.
    let combined = claim_polarity(&assertion.claim, &assertion.subject);
    let site_negative = (combined == Polarity::Negative) != assertion.subject.has_no_item();
    let admissible = matches!(assertion.claim, Claim::Admissible { .. });
    let act = speech_act(sentence);
    let force = force(sentence);
    let one_atom = |np: &Np, kernel: &Atom, alternative: Option<&Vp>| {
        let behavior = BehaviorAtom {
            subject: normalized_subject(np),
            atom: kernel.clone(),
            force,
            act,
            source: atom_anchor(&sentence.core, np, alternative),
        };
        Formula::Atom {
            atom: if admissible {
                AtomRef::Admissibility { behavior }
            } else {
                AtomRef::Behavior { behavior }
            },
        }
    };
    // Per subject item: the alternatives' `Or` (a single kernel stands
    // alone), then the item's own negation OUTSIDE the disjunction. The
    // grammar rejects `not` over alternatives (round 6, legislated:
    // NegatedAlternatives — write two prohibitions), so a negated `Or`
    // arises only from hand-built trees, where ¬(A ∨ B) is the coherent
    // reading.
    let one_item = |np: &Np| {
        let mut atoms: Vec<Formula> = kernels
            .iter()
            .zip(&alternatives)
            .map(|(kernel, alternative)| one_atom(np, kernel, *alternative))
            .collect();
        let inner = if atoms.len() == 1 {
            atoms.remove(0)
        } else {
            Formula::Or { items: atoms }
        };
        if site_negative != (np.det == Some(Det::No)) {
            Formula::not(inner)
        } else {
            inner
        }
    };
    Some(match &assertion.subject {
        NpGroup::Single(np) => one_item(np),
        NpGroup::Coordinated { conj, items, .. } => {
            let items: Vec<Formula> = items.iter().map(one_item).collect();
            match conj {
                Conj::And => Formula::And { items },
                Conj::Or => Formula::Or { items },
            }
        }
    })
}

/// The guarded claim of a sentence: `applicability → claim`, i.e.
/// `Or(Not(applicability), claim)` with a `Top` applicability simplified
/// away. This is the shape a guarantee takes in [`contract_formula`] AND the
/// shape an assumption source contributes in
/// [`AssumptionSource::from_sentence`] — one conditional, two roles. `None`
/// only for definitions (no claim).
fn guarded_claim(sentence: &Sentence) -> Option<Formula> {
    let claim = claim_formula(sentence)?;
    let applicability = applicability(sentence);
    Some(if applicability == Formula::Top {
        claim
    } else {
        Formula::Or {
            items: vec![Formula::not(applicability), claim],
        }
    })
}

/// The sentence-internal contract formula. `None` for definitions AND
/// permissions: vocabulary has no contract reading, and a permission has no
/// lone contract (it enters contracts only by pairing, on the environment
/// side — settled in [`crate::semantics::ingest_contract`]; its claim
/// formula exists, as an [`AtomRef::Admissibility`] atom). Coordinated
/// subjects ARE contract-bearing since round 4: the guarantee's claim is
/// the coordination's `And`/`Or` over per-item atoms.
pub fn contract_formula(sentence: &Sentence) -> Option<ContractFormula> {
    if matches!(
        speech_act(sentence),
        SpeechAct::Definition | SpeechAct::Permission
    ) {
        return None;
    }
    let guarantee = guarded_claim(sentence)?;
    Some(ContractFormula {
        assumption: Formula::Top,
        guarantee,
        sources: Vec::new(),
    })
}
