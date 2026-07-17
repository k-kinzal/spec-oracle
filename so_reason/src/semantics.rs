//! Interpretations derived over the parsed sentence structure.
//!
//! The syntax in [`so_lang::ast`] says what a sentence *is*; this module says
//! what a sentence *does* — its speech act, its normative force, its assertion
//! content — and exposes the legacy lone-sentence ingest projection.
//!
//! The role theory behind that projection is retained here because it derives
//! directly from sentence denotation: *assumption* and *guarantee* are
//! not sentence categories but **roles an assertion plays relative to a
//! responsible subject**. A statement whose subject is the component under
//! specification is a guarantee of that component's contract; a statement
//! about the component's environment becomes an assumption only by being
//! *paired* with a guarantee it enables. A behavioral sentence taken alone
//! therefore ingests as a guarantee under the trivial assumption `⊤`;
//! non-trivial assumptions are relationships **between** sentences.
//! [`crate::contract`] owns the semantic A/G value and the formation of those
//! relationships; this module's [`IngestContract`] remains a compatibility
//! projection of the authored sentence. Definitions establish
//! vocabulary and have no contract reading at all. A permission *admits*
//! behavior rather than constraining it, so as a lone sentence it yields no
//! `(⊤, G)` reading either: it enters a contract only through pairing, on
//! the environment (assumption) side of the guarantee it enables.
//!
//! Everything here is a derived view over the words; the words remain the
//! source of truth.

use serde::{Deserialize, Serialize};
use so_lang::ast::*;

/// The specification act a sentence performs.
///
/// The act is read off the pivot alone, so it reflects only the modal-site
/// negation: `No request shall be logged.` classifies as [`Obligation`]
/// even though its denotation is a negative binding claim — the same claim
/// shape as the [`Prohibition`] `The request shall not be logged.` Consumers
/// comparing sentences for equivalence must compare claim polarity (or the
/// skeleton), not `act`.
///
/// [`Obligation`]: SpeechAct::Obligation
/// [`Prohibition`]: SpeechAct::Prohibition
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SpeechAct {
    Definition,
    Description,
    Obligation,
    Prohibition,
    Recommendation,
    Permission,
}

/// How strongly a deontic sentence binds: `shall`/`must` bind, `should`
/// recommends. Descriptions, definitions, and permissions carry no force.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Force {
    Binding,
    Recommended,
}

/// Whether a claim is asserted or denied. Negation sites are syntactically
/// fixed (`shall not`, `never`, a subject `no`), so polarity is read off the
/// tree, not scanned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Polarity {
    Affirmative,
    Negative,
}

/// The one polarity-composition rule: each negation site flips once, and XOR
/// composes the sites. `site_negative` is the claim-level site (a deontic
/// `not` or a description `never`); the subject contributes its own flip when
/// a top-level item is determined by `no`. The claim denotation and the
/// skeleton both go through here, so they cannot drift apart.
fn combined_polarity(site_negative: bool, subject: &NpGroup) -> Polarity {
    if site_negative != subject.has_no_item() {
        Polarity::Negative
    } else {
        Polarity::Affirmative
    }
}

/// Classify the speech act of a sentence. The classification is read off the
/// pivot alone: the grammar has already made it unambiguous.
pub fn speech_act(sentence: &Sentence) -> SpeechAct {
    match &sentence.core {
        Core::Definition { .. } => SpeechAct::Definition,
        Core::Description { .. } => SpeechAct::Description,
        Core::Deontic { modal, negated, .. } => match (modal, negated) {
            (Modal::Shall | Modal::Must, false) => SpeechAct::Obligation,
            (Modal::Shall | Modal::Must, true) => SpeechAct::Prohibition,
            // A negated recommendation stays a recommendation; its polarity
            // lives in the assertion.
            (Modal::Should, _) => SpeechAct::Recommendation,
            (Modal::May, _) => SpeechAct::Permission,
        },
    }
}

/// The normative force, when the sentence has one: `shall`/`must` bind,
/// `should` recommends. Definitions, descriptions, and permissions have none.
pub fn force(sentence: &Sentence) -> Option<Force> {
    match &sentence.core {
        Core::Deontic {
            modal: Modal::Shall | Modal::Must,
            ..
        } => Some(Force::Binding),
        Core::Deontic {
            modal: Modal::Should,
            ..
        } => Some(Force::Recommended),
        _ => None,
    }
}

/// The assertion content of a behavioral (non-definition) sentence: its
/// circumstances, subject, and claim, detached from surface word order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Assertion {
    pub scopes: Vec<Frame>,
    pub states: Vec<Frame>,
    pub trigger: Option<Trigger>,
    pub exception: Option<Clause>,
    pub subject: NpGroup,
    pub claim: Claim,
}

/// What an assertion claims of its subject.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Claim {
    /// A description: the subject is in a state. The polarity is the COMBINED
    /// truth-functional polarity: `never` XOR a subject `no` (`always`
    /// strengthens but does not change polarity). The surface negation sites
    /// stay in the AST — `adverb` here, `Det::No` on the subject; the claim
    /// carries what the sentence denies or asserts.
    State {
        polarity: Polarity,
        copula: Copula,
        adverb: Option<DescriptionAdverb>,
        predicate: Predicate,
        /// The passive agent (`is logged by the daemon`), when stated —
        /// round 5. Digested as a [`RoleKind::Agent`] role, so the
        /// description meets `shall be logged by the daemon` at one atom.
        agent: Option<NpGroup>,
        /// The thematic-role tail after the passive agent (round 8
        /// follow-up): digested in surface order after the Agent role, so
        /// `is logged by the daemon within 5 seconds` meets `shall be
        /// logged by the daemon within 5 seconds` at one atom. Empty when
        /// no agent is stated (the plain predicate reading keeps the tail
        /// as words).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
    /// An obligation, prohibition, or recommendation: the subject acts. The
    /// polarity is the COMBINED truth-functional polarity: the modal `not`
    /// XOR a subject `no` (two flips cancel). The surface sites stay in the
    /// AST (`negated`, `Det::No`). Round 6: the claim holds the whole
    /// [`VpGroup`], so `either <vp> or <vp>` alternatives stay one claim
    /// (their disjunction lives in the formula layer and in the skeleton's
    /// per-alternative atoms).
    Action {
        polarity: Polarity,
        force: Force,
        vp: VpGroup,
    },
    /// A permission: the action is admissible, not required. Round 6: holds
    /// the [`VpGroup`] like [`Claim::Action`] does.
    Admissible { vp: VpGroup },
    /// A capability: the subject is ABLE to act (`is [always|never] able to
    /// <vp>`) — a descriptive behavior property, not a deontic act. The
    /// polarity is the COMBINED truth-functional polarity (round 5): the
    /// description adverb `never` XOR a subject `no`, through the shared
    /// helper — `The client is never able to retry.` and `No client is
    /// able to retry.` both deny the capability, and `No client is never
    /// able to retry.` composes back to affirmative. `always` strengthens
    /// but does not flip, exactly as in state claims.
    Capability { polarity: Polarity, vp: Vp },
}

/// What a sentence denotes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Denotation {
    /// A definition: vocabulary, not behavior.
    Vocabulary {
        scopes: Vec<Frame>,
        term: Np,
        definiens: Definiens,
    },
    /// A binding or recommended behavior, or a described invariant.
    Behavior(Assertion),
    /// A permitted behavior: admissibility rather than requirement.
    Admissibility(Assertion),
}

/// The denotation of a sentence.
pub fn denote(sentence: &Sentence) -> Denotation {
    let frames = &sentence.frames;
    let circumstance = |subject: NpGroup, claim: Claim| Assertion {
        scopes: frames.scopes.clone(),
        states: frames.states.clone(),
        trigger: frames.trigger.clone(),
        exception: sentence.exception.clone(),
        subject,
        claim,
    };
    match &sentence.core {
        Core::Definition { term, definiens } => Denotation::Vocabulary {
            scopes: frames.scopes.clone(),
            term: term.clone(),
            definiens: definiens.clone(),
        },
        Core::Description {
            subject,
            copula,
            adverb,
            predicate,
            agent,
            roles,
        } => {
            // Capability descriptions denote behavior through their verb
            // phrase, not a state predicate. Round 5: the description
            // adverb composes into the capability's polarity (`is never
            // able to` denies it).
            if let Predicate::AbleTo { vp } = predicate {
                let polarity =
                    combined_polarity(matches!(adverb, Some(DescriptionAdverb::Never)), subject);
                return Denotation::Behavior(circumstance(
                    subject.clone(),
                    Claim::Capability {
                        polarity,
                        vp: (**vp).clone(),
                    },
                ));
            }
            let polarity =
                combined_polarity(matches!(adverb, Some(DescriptionAdverb::Never)), subject);
            Denotation::Behavior(circumstance(
                subject.clone(),
                Claim::State {
                    polarity,
                    copula: *copula,
                    adverb: *adverb,
                    predicate: predicate.clone(),
                    agent: agent.clone(),
                    roles: roles.clone(),
                },
            ))
        }
        Core::Deontic {
            subject,
            modal,
            negated,
            vp,
        } => {
            let polarity = combined_polarity(*negated, subject);
            match modal {
                Modal::May => Denotation::Admissibility(circumstance(
                    subject.clone(),
                    Claim::Admissible { vp: vp.clone() },
                )),
                Modal::Shall | Modal::Must => Denotation::Behavior(circumstance(
                    subject.clone(),
                    Claim::Action {
                        polarity,
                        force: Force::Binding,
                        vp: vp.clone(),
                    },
                )),
                Modal::Should => Denotation::Behavior(circumstance(
                    subject.clone(),
                    Claim::Action {
                        polarity,
                        force: Force::Recommended,
                        vp: vp.clone(),
                    },
                )),
            }
        }
    }
}

/// The assumption side of a single-sentence contract. A sentence taken alone
/// assumes nothing of its environment; only pairing between sentences can
/// supply a non-trivial assumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Assumption {
    Top,
}

impl Assumption {
    pub fn render(&self) -> &'static str {
        match self {
            Assumption::Top => "⊤",
        }
    }
}

/// The assume-guarantee ingest projection of one sentence: its assertion in
/// the guarantee role under the trivial assumption.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IngestContract {
    pub assumption: Assumption,
    pub guarantee: Assertion,
    pub act: SpeechAct,
    pub force: Option<Force>,
}

/// Project a sentence into its ingest contract. Definitions return `None`:
/// vocabulary has no contract reading. Permissions return `None` too: an
/// admissibility admits behavior rather than constraining it, so it is not a
/// guarantee under `⊤`; it can enter a contract only by pairing, on the
/// environment side (its [`Denotation`] stays [`Denotation::Admissibility`]).
pub fn ingest_contract(sentence: &Sentence) -> Option<IngestContract> {
    let guarantee = match denote(sentence) {
        Denotation::Vocabulary { .. } | Denotation::Admissibility(_) => return None,
        Denotation::Behavior(assertion) => assertion,
    };
    Some(IngestContract {
        assumption: Assumption::Top,
        guarantee,
        act: speech_act(sentence),
        force: force(sentence),
    })
}

// ---- logical skeleton ---------------------------------------------------------------

/// The quantificational force of a determiner, normalized so that surface
/// variants meet: `each`/`every`/`all`/`any` are one universal, `a`/`an` one
/// existential. `any` is LEGISLATED universal (round 3): requirements
/// English reads `any request …` as `every request …`, not as an
/// existential witness. `no` is [`Quantifier::Negative`] AND — on a subject —
/// contributes a polarity flip to the whole claim (both facts are recorded —
/// the quantifier here, the flip in the claim's combined polarity, which
/// [`Skeleton::polarity`] mirrors). On an object, `no` stays out of claim
/// polarity (settled) but is visible as the object's quantifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Quantifier {
    /// `each` / `every` / `all` / `any` (the last legislated universal).
    Universal,
    /// `a` / `an`.
    Existential,
    /// `the`.
    Definite,
    /// A bare noun phrase.
    None,
    /// `no`.
    Negative,
    /// `at least n` / `at most n` / `exactly n`.
    Count { op: CountOp, n: u64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CountOp {
    AtLeast,
    AtMost,
    Exactly,
}

/// The normalized subject of a behavioral claim: its quantifier, its
/// restrictor (the modifier words, as written), its head word, and — round 6
/// — its FULL-FIDELITY identity string.
///
/// `full` is the lossiness guard: the lowercased canonical render of the
/// whole noun phrase with its own top-level determiner excluded (nested
/// phrases — the `of`-chain and any relative clause — render as written,
/// their determiners included). Quantifier normalization never touches it,
/// so `each request that is authenticated` and `each request that is
/// unauthenticated` share quantifier/restrictor/head but differ in `full`,
/// and no relation judgment can mistake one for the other.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubjectSkeleton {
    pub quantifier: Quantifier,
    pub restrictor: Vec<String>,
    pub head: String,
    /// Full-fidelity identity (round 6): lowercased render of
    /// modifiers + head + `of`-chain + relative, determiner excluded.
    #[serde(default)]
    pub full: String,
}

/// The digest of one object (or role) noun phrase: its quantifier, its
/// lowercased head, and — round 6 — its full-fidelity identity string
/// (same construction as [`SubjectSkeleton::full`]). Skeleton v3: object
/// determiners are no longer dropped — `log no request` and `log the
/// request` differ exactly here; round 6: `of`-chains and relatives are no
/// longer dropped from identity — `the owner of the file` and `the owner
/// of the bucket` differ exactly in `full`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectSkeleton {
    pub quantifier: Quantifier,
    pub head: String,
    /// Full-fidelity identity (round 6): lowercased render of
    /// modifiers + head + `of`-chain + relative, determiner excluded.
    #[serde(default)]
    pub full: String,
}

/// The full-fidelity identity string of one noun phrase (round 6): the
/// lowercased canonical render with the phrase's own top-level determiner
/// excluded. LEGISLATED: nested noun phrases (`of`-chain links, relative
/// clause bodies) keep their determiners as written — the top-level
/// determiner is quantification (carried separately as the quantifier),
/// while nested determiners are part of what the phrase names.
pub(crate) fn np_full(np: &Np) -> String {
    let stripped = Np {
        det: None,
        ..np.clone()
    };
    stripped.render().to_lowercase()
}

/// The structured digest of a comparison predicate (round 6): the operator,
/// the measure as written, and — for `between` — the upper bound. State
/// claims and `be`-complement claims whose predicate is a comparison carry
/// this ALONGSIDE the rendered words (kept for index compatibility), so the
/// relation engine can reason over intervals instead of re-parsing rendered
/// words.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComparisonSkeleton {
    pub op: ComparisonOp,
    pub value: MeasureSkeleton,
    /// The upper bound of `between <value> and <upper>`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upper: Option<MeasureSkeleton>,
}

/// The digest of one comparison measure: a quantity with its number lexeme
/// and unit AS WRITTEN, or a noun-phrase value's full identity string
/// (lowercased render of the whole group, determiners included — a measure
/// noun phrase is a value name, not a quantified position; legislated).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MeasureSkeleton {
    Quantity {
        number: String,
        unit: Option<String>,
    },
    Np {
        full: String,
    },
}

/// The digest of one comparison predicate (round 6), shared by claim atoms
/// and clause digests.
fn comparison_skeleton(comparison: &Comparison) -> ComparisonSkeleton {
    let measure = |m: &Measure| match m {
        Measure::Quantity { number, unit } => MeasureSkeleton::Quantity {
            number: number.clone(),
            unit: unit.clone(),
        },
        Measure::Np { np } => MeasureSkeleton::Np {
            full: np.render().to_lowercase(),
        },
        // A bounded measure never reaches comparison position through the
        // grammar (`Bounded` is admitted under `for` only); a hand-built
        // tree digests it as an opaque identity string — conservative, no
        // interval grounding.
        Measure::Bounded { .. } => MeasureSkeleton::Np {
            full: m.render().to_lowercase(),
        },
    };
    ComparisonSkeleton {
        op: comparison.op,
        value: measure(&comparison.value),
        upper: comparison.upper.as_ref().map(measure),
    }
}

/// The comparison digest of a predicate, when it is one.
fn predicate_comparison(predicate: &Predicate) -> Option<ComparisonSkeleton> {
    match predicate {
        Predicate::Comparison(comparison) => Some(comparison_skeleton(comparison)),
        _ => None,
    }
}

/// The normalized behavior kernel of a claim: for action claims the verb
/// plus particle (or, for `be`, the complement predicate words) plus the
/// object digests and role digests; for state claims the predicate words.
/// Words are surface words, lowercased — there is deliberately NO
/// lemmatization: `logged` matches `logged`, never `log`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Atom {
    pub words: Vec<String>,
    /// The manner adverbs of the claim's verb phrase, lowercased, in surface
    /// order. `words` does NOT absorb manner: `stop` and `stop immediately`
    /// share their verb kernel and differ exactly here. Empty for state
    /// claims.
    pub manner: Vec<String>,
    /// ALL objects, coordination included (one entry per coordinated item),
    /// each with its quantifier and lowercased head. Empty for state claims
    /// (a predicate has no object).
    pub objects: Vec<ObjectSkeleton>,
    /// The conjunction of a coordinated object group (round 6 follow-up):
    /// `notify the admin and the owner` and `notify the admin or the owner`
    /// share their item list and differ exactly here. `None` for a single
    /// (or absent) object. Without this, the or-object atom EQUALLED its
    /// and-object twin — a false Yes the round-6 lossiness rule forbids.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub objects_conj: Option<Conj>,
    /// Digests of the thematic-role phrases, in surface order, so `store the
    /// report in the archive` and `store the report on the public bucket`
    /// stop colliding, and `within 5 seconds` differs from `within 10
    /// seconds` exactly in its Deadline role.
    pub roles: Vec<RoleSkeleton>,
    /// The structured comparison (round 6), when the claim's predicate (a
    /// state claim's predicate, or a `be`-complement) is one. The rendered
    /// words are kept too — `words` and `comparison` describe the same
    /// material at two fidelities.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ComparisonSkeleton>,
    /// The content complement (round 7): the digest of a `<verb> that
    /// <clause>` clause, when the verb phrase carries one. `None` for
    /// state claims and content-free verb phrases.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<ContentSkeleton>,
}

/// The digest of a content complement (round 7): the clause digest PLUS
/// its full-fidelity identity string — the lowercased canonical render of
/// the whole clause. The `full` string is the lossiness guard the round-6
/// rule requires: the digest is still coarser than the words (round 11
/// carries a verbal body's object digests, but modifiers inside role
/// phrases and the object group's conjunction stay out), so content
/// identity must not rest on the digest alone.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContentSkeleton {
    pub clause: ClauseSkeleton,
    /// Lowercased canonical render of the content clause.
    pub full: String,
}

/// The digest of one thematic-role phrase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleSkeleton {
    pub kind: RoleKind,
    pub value: RoleValue,
    /// The role's surface MARKER, lowercased, when the preposition itself
    /// disambiguates within one [`RoleKind`] (round 9): a Location role
    /// carries its preposition (`in` vs `on the archive` are different
    /// propositions — the round-2 "known residual collision" is retired).
    /// `None` for every role whose kind already fixes the marker
    /// (Recipient is always `to`, Deadline always `within`, …), so
    /// pre-round-9 serialized skeletons load unchanged and non-locative
    /// digests keep their shape.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub marker: Option<String>,
}

/// The role a [`RoleSkeleton`] digests — one per [`RolePp`] variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RoleKind {
    Recipient,
    Means,
    Topic,
    Deadline,
    Duration,
    Rate,
    Before,
    After,
    Until,
    Source,
    Goal,
    Location,
    /// The passive agent (`by <np>`) — round 5. Descriptions and copular
    /// clause bodies digest their agent under this kind too, so the
    /// deontic passive and the described passive meet.
    Agent,
}

/// The digested content of a role phrase. Struct variants (not newtypes):
/// an internally tagged enum cannot serialize a newtype variant holding a
/// sequence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
// The clause variant carries a whole nested [`ClauseSkeleton`] (round 8);
// boxing it would break destructuring sites for a size win that does not
// matter at these volumes — see the note on [`so_lang::ast::VpGroup`].
#[allow(clippy::large_enum_variant)]
pub enum RoleValue {
    /// Noun-phrase roles: one digest per item, coordination included, each
    /// with its quantifier and lowercased head (skeleton v3). `conj` is the
    /// group's conjunction (round 6 follow-up — `to the admin and the
    /// owner` vs `to the admin or the owner` differ exactly here), `None`
    /// for a single item.
    Heads {
        items: Vec<ObjectSkeleton>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        conj: Option<Conj>,
    },
    /// A measured role (Deadline/Duration over a quantity): number and unit
    /// kept AS WRITTEN — comparability (5 < 10, seconds vs ms) is downstream.
    Measure {
        number: String,
        unit: Option<String>,
    },
    /// A BOUNDED measured role (round 6): `for at least 30 days`, `for
    /// between 5 and 10 seconds`. Everything as written; `upper` is the
    /// second bound of `between`.
    BoundedMeasure {
        op: ComparisonOp,
        number: String,
        unit: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        upper: Option<String>,
    },
    /// A clausal role (`before`/`after`/`until`): the FULL nested clause
    /// digest plus its full-fidelity identity string (round 8, superseding
    /// the flat `{subject_head, words}` digest). The skeleton keeps the
    /// nested clause's polarity, manner, roles, and comparison — `after no
    /// backup completes` and `after the backup completes` must never digest
    /// alike — and `full` is the lossiness anchor: the lowercased canonical
    /// render of the nested clause, exactly as [`ContentSkeleton::full`]
    /// anchors content complements (the nested digest is coarser than the
    /// words even with the round-11 object digests, so identity must not
    /// rest on the digest alone).
    Clause {
        skeleton: ClauseSkeleton,
        /// Lowercased canonical render of the nested clause.
        full: String,
    },
}

/// The digest of one guard clause: its subject heads (lowercased, joined by
/// one space for a coordinated subject), the negation it carries, its verb
/// plus particle or predicate words (lowercased), and the digests of its
/// thematic-role phrases (verbal bodies carry roles since round 3; round 8
/// superseded the restriction — copular bodies carry their agent and role
/// tail too, and a capability body digests its verb phrase's roles). A
/// clause has exactly one negation site — a subject `no` — so `polarity` is
/// `Some(Negative)` when present and `None` when the clause carries no
/// negation site.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClauseSkeleton {
    pub subject_head: String,
    pub polarity: Option<Polarity>,
    pub words: Vec<String>,
    /// The object digests of a VERBAL body (round 11, change 2 —
    /// superseding the documented drop-the-object blind spot): one
    /// [`ObjectSkeleton`] per coordinated item, so `the queue holds no
    /// message` and `the queue holds the message` no longer share a
    /// skeleton — the INDEX now separates what the full anchors always
    /// did. Round 12 (change 6): CAPABILITY bodies carry their verb
    /// phrase's object digests too — `is able to hold the lock` and `is
    /// able to hold the token` differ in the index now, retiring the
    /// blind spot the round-8 pin documented (the guard anchor already
    /// separated them losslessly). Empty for plain copular bodies (a
    /// predicate has no object). LEGISLATED (round 11): the object
    /// GROUP's `and`/`or` conjunction is NOT carried here — an and-group
    /// and its or-group twin still share the digest and are separated by
    /// the lossless anchor only. Serde: pre-round-11 digests carry no
    /// field and load as empty — the documented legacy reading (the old
    /// digest dropped the object).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub objects: Vec<ObjectSkeleton>,
    /// The manner adverbs of a verbal body, lowercased, in surface order.
    /// `words` does NOT absorb manner (`completes` vs `completes
    /// successfully` differ exactly here); empty for non-capability copular
    /// bodies (a capability body's manner comes from its verb phrase —
    /// round 8, change 5).
    pub manner: Vec<String>,
    pub roles: Vec<RoleSkeleton>,
    /// The structured comparison (round 6), when a copular body's predicate
    /// is one; `None` for verbal bodies and non-comparison predicates.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ComparisonSkeleton>,
    /// The content complement of a VERBAL body (round 9): the nested
    /// clause's digest plus its full render — the same lossiness-anchor
    /// discipline as [`ContentSkeleton`] everywhere else. Boxed: the
    /// content skeleton nests a clause skeleton, and the recursion needs
    /// the indirection. `None` for copular bodies and content-free verbal
    /// bodies, and serde-skipped, so pre-round-9 digests load unchanged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<Box<ContentSkeleton>>,
}

/// The digest of the trigger frame: its kind, its conjunction (`None` for a
/// single clause), and its clause digests.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TriggerSkeleton {
    pub kind: TriggerKind,
    pub conj: Option<Conj>,
    pub clauses: Vec<ClauseSkeleton>,
}

/// Digests of a sentence's circumstance frames, flattened per frame family.
/// Only the trigger keeps its conjunction: `Where`/`While` clauses are an
/// unordered bag for indexing purposes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Guards {
    pub scopes: Vec<ClauseSkeleton>,
    pub states: Vec<ClauseSkeleton>,
    pub trigger: Option<TriggerSkeleton>,
}

/// The logical skeleton of a behavioral sentence: quantifier, combined
/// polarity, normalized atom, and frame/exception digests, so contradiction
/// detection can see through surface differences (`No request is logged.` vs
/// `Each request shall be logged.`). This is the INDEX for future edge
/// generation — a data-only derived view rich enough that candidate pairs can
/// be found and distinguished — not the decision procedure: edge generation
/// over skeletons is graph work, outside this crate.
///
/// Known blind spots (deliberate for now): coarse role and object digests
/// keep quantifier + head (the round-6 `full` strings carry modifiers and
/// nesting, and — round 9 — the Location digest carries its preposition
/// marker, so `in` vs `on the archive` separate now). Round 11 (change 2)
/// retires the drop-the-object blind spot for verbal guard digests:
/// [`ClauseSkeleton::objects`] carries the verbal body's object digests,
/// so `exceeds the limit` and `exceeds the threshold` no longer collide
/// in the INDEX (the object GROUP's `and`/`or` conjunction is the one
/// residual collision there — anchors separate it).
/// Round 8 (superseding the round-3 flat digest): `before`/`after`/`until`
/// role digests carry the WHOLE nested clause skeleton plus its full
/// render, so `before no user logs out` and `before the user logs out` no
/// longer digest alike. Since skeleton v3, object determiners are NO LONGER
/// dropped: `log no request` and `log the request` differ in the object's
/// quantifier (object `no` still stays out of claim polarity — settled).
/// The words remain the source of truth for anything finer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Skeleton {
    pub subject: SubjectSkeleton,
    /// The COMBINED polarity of the claim, as carried by the claim itself.
    /// Every negation site flips it once: a deontic `not` XOR a description
    /// `never` XOR a subject `no`. Two flips cancel (`No request shall not
    /// be logged.` is affirmative).
    pub polarity: Polarity,
    /// The normalized behavior kernels: EXACTLY ONE for every claim except
    /// an `either … or …` deontic (round 6), which carries one atom per
    /// alternative, in surface order. Round 6 RESHAPE (supersedes the lone
    /// `atom` field): the index must see every alternative, and a lone
    /// field would either hide them or duplicate the first — so the field
    /// is the vector, with no legacy alias.
    pub atoms: Vec<Atom>,
    pub force: Option<Force>,
    pub act: SpeechAct,
    /// Digests of the circumstance frames the claim sits under.
    pub guards: Guards,
    /// Digest of the `unless` carve-out, when present.
    pub exception: Option<ClauseSkeleton>,
}

/// Derive the logical skeleton of a sentence. `None` for definitions
/// (vocabulary has no behavioral claim) and for coordinated subjects, which
/// have no single quantifier-restrictor-head normal form in v0.2 — the
/// skeleton is the surface INDEX and stays single-subject; the formula
/// layer ([`crate::formula::claim_formula`]) digests a coordinated subject
/// one item at a time, so coordinated sentences are formula-bearing even
/// though they have no skeleton.
pub fn skeleton(sentence: &Sentence) -> Option<Skeleton> {
    let assertion = match denote(sentence) {
        Denotation::Vocabulary { .. } => return None,
        Denotation::Behavior(assertion) | Denotation::Admissibility(assertion) => assertion,
    };
    let np = match &assertion.subject {
        NpGroup::Single(np) => np,
        NpGroup::Coordinated { .. } => return None,
    };
    let subject = subject_skeleton_of(np);
    // The claim's polarity is already the combined one — every negation site
    // (deontic `not` / description `never` / subject `no`) is XOR-composed by
    // [`combined_polarity`] in [`denote`]. An admissible claim carries no
    // claim-level site; its subject still composes (unreachable through
    // [`so_lang::parse::parse`], which rejects `no` under `may`, but a
    // hand-built tree gets the same rule).
    let polarity = claim_polarity(&assertion.claim, &assertion.subject);
    let atoms = claim_atoms(&assertion.claim);
    let guards = Guards {
        scopes: frames_clause_skeletons(&assertion.scopes),
        states: frames_clause_skeletons(&assertion.states),
        trigger: assertion.trigger.as_ref().map(|trigger| TriggerSkeleton {
            kind: trigger.kind,
            conj: trigger.clause.conj,
            clauses: trigger.clause.items.iter().map(clause_skeleton).collect(),
        }),
    };
    Some(Skeleton {
        subject,
        polarity,
        atoms,
        force: force(sentence),
        act: speech_act(sentence),
        guards,
        exception: assertion.exception.as_ref().map(clause_skeleton),
    })
}

/// The normalized quantificational force of a determiner slot. `any` is
/// legislated universal (requirements-English convention, round 3).
fn quantifier_of(det: &Option<Det>) -> Quantifier {
    match det {
        Option::None => Quantifier::None,
        Some(Det::The) => Quantifier::Definite,
        Some(Det::A) | Some(Det::An) => Quantifier::Existential,
        Some(Det::Each) | Some(Det::Every) | Some(Det::All) | Some(Det::Any) => {
            Quantifier::Universal
        }
        Some(Det::No) => Quantifier::Negative,
        Some(Det::AtLeast { n }) => Quantifier::Count {
            op: CountOp::AtLeast,
            n: *n,
        },
        Some(Det::AtMost { n }) => Quantifier::Count {
            op: CountOp::AtMost,
            n: *n,
        },
        Some(Det::Exactly { n }) => Quantifier::Count {
            op: CountOp::Exactly,
            n: *n,
        },
    }
}

/// The skeleton of one subject noun phrase: its quantifier, restrictor, and
/// head. Crate-internal: the formula layer digests coordinated subjects one
/// item at a time through this.
///
/// GENERIC SUBJECTS ARE UNIVERSAL (round 5, legislated): in a BEHAVIORAL
/// sentence — deontic (capability included) or description; definitions have
/// no skeleton at all — a subject determined by `a`/`an` or bare (no
/// determiner, bare plurals included) is the requirements-English GENERIC
/// reading: `A request shall be logged.` and `Requests are logged.` oblige
/// every request, exactly as `Each request shall be logged.` does, so all
/// three meet at [`Quantifier::Universal`]. The normalization applies to the
/// SUBJECT position only: object and role noun phrases keep `a`/`an`
/// existential (`shall create a session` is one session per occasion, via
/// [`quantifier_of`]) and bare [`Quantifier::None`]. This function is the
/// subject position — every caller digests a GRAMMATICAL subject (for a
/// passive that is the patient; the round-10 RESPONSIBLE view is a
/// separate key derivation, [`responsible_subject_keys`], not a digest).
pub(crate) fn subject_skeleton_of(np: &Np) -> SubjectSkeleton {
    let quantifier = match quantifier_of(&np.det) {
        Quantifier::Existential | Quantifier::None => Quantifier::Universal,
        other => other,
    };
    SubjectSkeleton {
        quantifier,
        restrictor: np.modifiers.clone(),
        head: np.head.clone(),
        full: np_full(np),
    }
}

/// The COMBINED polarity of a claim under its subject. State, action, and —
/// round 5 — capability claims already carry it (XOR-composed by
/// [`combined_polarity`] in [`denote`]); an admissible claim has no
/// claim-level site, but its subject still composes (unreachable through
/// [`so_lang::parse::parse`], which rejects `no` under `may`, but a
/// hand-built tree gets the same rule).
pub(crate) fn claim_polarity(claim: &Claim, subject: &NpGroup) -> Polarity {
    match claim {
        Claim::State { polarity, .. }
        | Claim::Action { polarity, .. }
        | Claim::Capability { polarity, .. } => *polarity,
        Claim::Admissible { .. } => combined_polarity(false, subject),
    }
}

/// The behavior kernels of a claim, shared by [`skeleton`] and the formula
/// layer's behavior atoms: exactly one for every claim except an
/// [`Claim::Action`]/[`Claim::Admissible`] over `either … or …`
/// alternatives (round 6), which yields one atom PER ALTERNATIVE.
pub(crate) fn claim_atoms(claim: &Claim) -> Vec<Atom> {
    match claim {
        Claim::State {
            predicate,
            agent,
            roles,
            ..
        } => vec![Atom {
            words: lowercased_words(&predicate.render()),
            manner: Vec::new(),
            objects: Vec::new(),
            objects_conj: None,
            // The passive agent digests as an Agent role (round 5), so
            // `is logged by the daemon` and `shall be logged by the
            // daemon` share one atom; the round-8 role tail follows it
            // in surface order, exactly as in a copular clause body.
            roles: agent
                .as_ref()
                .map(agent_skeleton)
                .into_iter()
                .chain(roles.iter().map(role_skeleton))
                .collect(),
            // Round 6: a comparison predicate is digested structurally too.
            comparison: predicate_comparison(predicate),
            // A state claim has no verb phrase, so no content complement.
            content: None,
        }],
        Claim::Action { vp, .. } | Claim::Admissible { vp } => {
            vp.items().iter().map(vp_atom).collect()
        }
        Claim::Capability { vp, .. } => vec![vp_atom(vp)],
    }
}

/// The behavior kernel of one verb phrase.
fn vp_atom(vp: &Vp) -> Atom {
    let words = match &vp.complement {
        // `be` disappears into its complement: `shall be logged` and
        // `is logged` share the atom ["logged"].
        Some(complement) if vp.verb.eq_ignore_ascii_case("be") => {
            lowercased_words(&complement.render())
        }
        // A particle verb's atom is verb + particle (two words):
        // `time out` and `time` are different behaviors.
        _ => match &vp.particle {
            Some(particle) => vec![vp.verb.to_lowercase(), particle.to_lowercase()],
            None => vec![vp.verb.to_lowercase()],
        },
    };
    // Round 6: a `be`-complement comparison (`shall be at most 3`)
    // digests structurally, exactly as the described form does —
    // the two claims must keep meeting at one atom.
    let comparison = match &vp.complement {
        Some(complement) if vp.verb.eq_ignore_ascii_case("be") => predicate_comparison(complement),
        _ => None,
    };
    let manner = vp.manner.iter().map(|w| w.to_lowercase()).collect();
    let objects = vp.object.as_ref().map(object_skeletons).unwrap_or_default();
    let objects_conj = vp.object.as_ref().and_then(group_conj);
    let roles = vp.roles.iter().map(role_skeleton).collect();
    // Round 7: the content complement digests as its clause skeleton plus
    // the full-fidelity render (the lossiness guard — see
    // [`ContentSkeleton`]).
    let content = vp.content.as_ref().map(|clause| ContentSkeleton {
        clause: clause_skeleton(clause),
        full: clause.render().to_lowercase(),
    });
    Atom {
        words,
        manner,
        objects,
        objects_conj,
        roles,
        comparison,
        content,
    }
}

/// All heads of a noun-phrase group, lowercased.
fn heads_lowercased(group: &NpGroup) -> Vec<String> {
    group.heads().iter().map(|h| h.to_lowercase()).collect()
}

/// One [`ObjectSkeleton`] per item of a noun-phrase group: quantifier plus
/// lowercased head.
fn object_skeletons(group: &NpGroup) -> Vec<ObjectSkeleton> {
    let digest = |np: &Np| ObjectSkeleton {
        quantifier: quantifier_of(&np.det),
        head: np.head.to_lowercase(),
        full: np_full(np),
    };
    match group {
        NpGroup::Single(np) => vec![digest(np)],
        NpGroup::Coordinated { items, .. } => items.iter().map(digest).collect(),
    }
}

/// The conjunction of a coordinated noun-phrase group, `None` for a single
/// noun phrase. Digested alongside the item skeletons (round 6 follow-up):
/// dropping it made `and`-groups and `or`-groups carry equal propositions.
fn group_conj(group: &NpGroup) -> Option<Conj> {
    match group {
        NpGroup::Single(_) => None,
        NpGroup::Coordinated { conj, .. } => Some(*conj),
    }
}

/// The digest of a passive agent as an Agent role (round 5) — shared by
/// state claims and copular clause bodies.
fn agent_skeleton(agent: &NpGroup) -> RoleSkeleton {
    RoleSkeleton {
        kind: RoleKind::Agent,
        value: RoleValue::Heads {
            items: object_skeletons(agent),
            conj: group_conj(agent),
        },
        marker: None,
    }
}

/// The digest of one thematic-role phrase.
fn role_skeleton(role: &RolePp) -> RoleSkeleton {
    let heads = |kind: RoleKind, np: &NpGroup| RoleSkeleton {
        kind,
        value: RoleValue::Heads {
            items: object_skeletons(np),
            conj: group_conj(np),
        },
        marker: None,
    };
    let measured = |kind: RoleKind, measure: &Measure| RoleSkeleton {
        kind,
        value: match measure {
            // Number and unit AS WRITTEN: comparability is downstream.
            Measure::Quantity { number, unit } => RoleValue::Measure {
                number: number.clone(),
                unit: unit.clone(),
            },
            // Round 6: bounded quantities keep their bound structurally.
            Measure::Bounded {
                op,
                number,
                unit,
                upper,
            } => RoleValue::BoundedMeasure {
                op: *op,
                number: number.clone(),
                unit: unit.clone(),
                upper: upper.clone(),
            },
            Measure::Np { np } => RoleValue::Heads {
                items: object_skeletons(np),
                conj: group_conj(np),
            },
        },
        marker: None,
    };
    // Round 8: the nested digest is the WHOLE clause skeleton (polarity,
    // manner, roles, comparison kept), anchored by the full render.
    let clausal = |kind: RoleKind, clause: &Clause| RoleSkeleton {
        kind,
        value: RoleValue::Clause {
            skeleton: clause_skeleton(clause),
            full: clause.render().to_lowercase(),
        },
        marker: None,
    };
    match role {
        RolePp::Recipient(np) => heads(RoleKind::Recipient, np),
        RolePp::Means { np, .. } => heads(RoleKind::Means, np),
        RolePp::Topic(np) => heads(RoleKind::Topic, np),
        RolePp::Deadline(measure) => measured(RoleKind::Deadline, measure),
        RolePp::Duration(measure) => measured(RoleKind::Duration, measure),
        RolePp::Rate { unit } => RoleSkeleton {
            kind: RoleKind::Rate,
            value: RoleValue::Heads {
                items: vec![ObjectSkeleton {
                    quantifier: Quantifier::None,
                    head: unit.to_lowercase(),
                    full: unit.to_lowercase(),
                }],
                conj: None,
            },
            marker: None,
        },
        RolePp::Before(clause) => clausal(RoleKind::Before, clause),
        RolePp::After(clause) => clausal(RoleKind::After, clause),
        RolePp::Until(clause) => clausal(RoleKind::Until, clause),
        RolePp::Source(np) => heads(RoleKind::Source, np),
        RolePp::Goal(np) => heads(RoleKind::Goal, np),
        // Round 9: the Location digest CARRIES ITS PREPOSITION — `in the
        // archive` and `on the archive` are different propositions, so the
        // marker enters role identity (supersedes the round-2 legislated
        // heads-only collision).
        RolePp::Location { preposition, np } => RoleSkeleton {
            marker: Some(preposition.to_lowercase()),
            ..heads(RoleKind::Location, np)
        },
        RolePp::Agent(np) => heads(RoleKind::Agent, np),
    }
}

/// The digest of one clause: lowercased subject heads (joined by one space
/// when coordinated), the subject's `no` as the clause's negation site, the
/// verb plus particle (verbal body) or lowercased predicate words (copular
/// body), and the digests of the clause's own thematic-role phrases.
fn clause_skeleton(clause: &Clause) -> ClauseSkeleton {
    let subject_head = heads_lowercased(&clause.subject).join(" ");
    let polarity = clause.subject.has_no_item().then_some(Polarity::Negative);
    // Round 9: a verbal body's content complement digests with the shared
    // lossiness-anchor discipline (digest + full render).
    let content = match &clause.body {
        ClauseBody::Verbal {
            content: Some(content),
            ..
        } => Some(Box::new(ContentSkeleton {
            clause: clause_skeleton(content),
            full: content.render().to_lowercase(),
        })),
        _ => None,
    };
    let (words, manner, roles, comparison) = match &clause.body {
        // Capability in clause position (round 8, change 5): the digest is
        // STRUCTURAL — `able to` + the verb kernel, with the verb phrase's
        // manner and roles in their own slots — so `is able to stop within
        // 5 seconds` and `is able to stop within 10 seconds` differ in a
        // structured Deadline role, exactly as description capabilities
        // do. Round 12 (change 6): the verb phrase's OBJECT digests enter
        // the skeleton too (the `objects` match below), so `is able to
        // hold the lock` and `is able to hold the token` differ in the
        // index; the clause render in the guard anchor keeps full
        // fidelity, as always.
        ClauseBody::Copular {
            predicate: Predicate::AbleTo { vp },
            agent,
            roles,
            ..
        } => {
            let mut words = vec!["able".to_string(), "to".to_string(), vp.verb.to_lowercase()];
            if let Some(particle) = &vp.particle {
                words.push(particle.to_lowercase());
            }
            let digest_roles = agent
                .as_ref()
                .map(agent_skeleton)
                .into_iter()
                .chain(vp.roles.iter().map(role_skeleton))
                .chain(roles.iter().map(role_skeleton))
                .collect();
            (
                words,
                vp.manner.iter().map(|w| w.to_lowercase()).collect(),
                digest_roles,
                None,
            )
        }
        ClauseBody::Copular {
            predicate,
            agent,
            roles,
            ..
        } => (
            lowercased_words(&predicate.render()),
            Vec::new(),
            // The passive agent digests as an Agent role (round 5); the
            // round-8 role tail follows it in surface order.
            agent
                .as_ref()
                .map(agent_skeleton)
                .into_iter()
                .chain(roles.iter().map(role_skeleton))
                .collect(),
            // Round 6: a comparison predicate digests structurally too.
            predicate_comparison(predicate),
        ),
        ClauseBody::Verbal {
            verb,
            particle,
            manner,
            roles,
            ..
        } => {
            let words = match particle {
                Some(particle) => vec![verb.to_lowercase(), particle.to_lowercase()],
                None => vec![verb.to_lowercase()],
            };
            let manner = manner.iter().map(|w| w.to_lowercase()).collect();
            (
                words,
                manner,
                roles.iter().map(role_skeleton).collect(),
                None,
            )
        }
    };
    // Round 11 (change 2): a verbal body's object digests enter the
    // skeleton — `holds no message` vs `holds the message` differ in the
    // INDEX now, not only in the anchors. Round 12 (change 6): CAPABILITY
    // bodies carry their verb phrase's object digests too — `is able to
    // hold the lock` and `is able to hold the token` no longer share a
    // skeleton (the blind spot the round-8 pin documented is retired).
    // Plain copular bodies stay object-free (a predicate has no object;
    // see the field doc).
    let objects = match &clause.body {
        ClauseBody::Verbal {
            object: Some(object),
            ..
        } => object_skeletons(object),
        ClauseBody::Copular {
            predicate: Predicate::AbleTo { vp },
            ..
        } => vp.object.as_ref().map(object_skeletons).unwrap_or_default(),
        _ => Vec::new(),
    };
    ClauseSkeleton {
        subject_head,
        polarity,
        words,
        manner,
        objects,
        roles,
        comparison,
        content,
    }
}

/// The digests of one clause group's items, in order. Crate-internal: the
/// formula layer builds its guard atoms from these.
pub(crate) fn clause_group_skeletons(group: &ClauseGroup) -> Vec<ClauseSkeleton> {
    group.items.iter().map(clause_skeleton).collect()
}

/// The clause digests of a frame family, flattened across frames.
fn frames_clause_skeletons(frames: &[Frame]) -> Vec<ClauseSkeleton> {
    frames
        .iter()
        .flat_map(|frame| frame.clause.items.iter().map(clause_skeleton))
        .collect()
}

fn lowercased_words(rendered: &str) -> Vec<String> {
    rendered.split_whitespace().map(str::to_lowercase).collect()
}

// ---- subject identity keys ----------------------------------------------------------

/// Normalized textual identity keys for the GRAMMATICAL subject(s) of a
/// sentence — the surface subject position. In a PASSIVE claim this is the
/// PATIENT view (`Each request shall be logged by the daemon.` keys on
/// `request`); the responsible-component view is
/// [`responsible_subject_keys`] (round 10 — both views are deliberate and
/// documented there). Keys are joined by `.` (the join character is legislated `.`, chosen
/// because the chain reads as a path), one key per coordinated item, in
/// surface order. Empty for definitions — a definition establishes
/// vocabulary and has no responsible subject.
///
/// Round 5: keys CARRY MODIFIERS — `The backup daemon` must not collide
/// with `The daemon`. Each link of the `of`-chain (the subject itself, then
/// each `of` noun phrase in order) contributes its lowercased modifiers in
/// surface order, then its lowercased head: `the backup daemon` →
/// `backup.daemon`, `the owner of the file` → `owner.file`, `the owner of
/// the backup file` → `owner.backup.file` (legislated: of-chain links keep
/// their modifiers too — the same collision argument applies inside the
/// chain).
///
/// This is still a TENTATIVE textual key: determiners and relative clauses
/// are deliberately dropped, and nothing here resolves aliases or component
/// identity (the same component under two names — `specd` vs `the daemon` —
/// or two components sharing a head word). That identity work is
/// daemon-side future work; hard pairing decisions between sentences must
/// wait for it rather than trust key equality.
pub fn subject_keys(sentence: &Sentence) -> Vec<String> {
    let subject = match &sentence.core {
        Core::Definition { .. } => return Vec::new(),
        Core::Description { subject, .. } | Core::Deontic { subject, .. } => subject,
    };
    group_keys(subject)
}

/// The identity key of one noun phrase — the [`subject_keys`] construction
/// (modifiers + head per `of`-chain link, lowercased, `.`-joined).
fn np_key(np: &Np) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut link = Some(np);
    while let Some(np) = link {
        parts.extend(np.modifiers.iter().map(|m| m.to_lowercase()));
        parts.push(np.head.to_lowercase());
        link = np.of.as_deref();
    }
    parts.join(".")
}

/// The identity keys of a noun-phrase group, one per coordinated item.
fn group_keys(group: &NpGroup) -> Vec<String> {
    match group {
        NpGroup::Single(np) => vec![np_key(np)],
        NpGroup::Coordinated { items, .. } => items.iter().map(np_key).collect(),
    }
}

/// Normalized textual identity keys for the RESPONSIBLE subject(s) of a
/// sentence (round 10). [`subject_keys`] is the GRAMMATICAL view — the
/// surface subject position, which in a passive names the PATIENT
/// (`Each request shall be logged by the daemon.` keys on `request`). The
/// responsible component of a passive claim is its AGENT: the daemon does
/// the logging, so environment-vs-self questions (the pairing
/// subject-relation check, [`crate::contract::SubjectRelation`]) must be
/// asked of the daemon, not the request. Both views are kept — the
/// grammatical view stays the index of what the sentence is ABOUT; this
/// view is who ANSWERS for it.
///
/// The rule: when the claim is PASSIVE — a deontic `be`-complement verb
/// phrase or a copular description — AND an agent is stated (the dedicated
/// `agent` slot, or a [`RolePp::Agent`] role on the same claim site), the
/// responsible keys are the AGENT group's keys (one per coordinated item);
/// otherwise the grammatical subject's keys, unchanged. An agentless
/// passive (`Each request shall be logged.`) therefore falls back to the
/// grammatical view: no better identity is written. For an `either … or …`
/// deontic the FIRST alternative's agent decides (legislated: alternatives
/// share one responsible subject or the sentence should be split).
/// Definitions have no responsible subject — empty, as in
/// [`subject_keys`].
pub fn responsible_subject_keys(sentence: &Sentence) -> Vec<String> {
    match &sentence.core {
        Core::Definition { .. } => Vec::new(),
        Core::Description {
            subject,
            predicate,
            agent,
            roles,
            ..
        } => {
            // A capability (`is able to …`) is active — its subject acts —
            // so a hand-built agent never overrides it.
            if matches!(predicate, Predicate::AbleTo { .. }) {
                return group_keys(subject);
            }
            if let Some(agent) = agent {
                return group_keys(agent);
            }
            if let Some(agent) = roles.iter().find_map(|role| match role {
                RolePp::Agent(np) => Some(np),
                _ => None,
            }) {
                return group_keys(agent);
            }
            group_keys(subject)
        }
        Core::Deontic { subject, vp, .. } => {
            let first = match vp {
                VpGroup::Single(vp) => vp,
                VpGroup::Alternatives { items } => match items.first() {
                    Some(vp) => vp,
                    None => return group_keys(subject),
                },
            };
            let passive = first.verb.eq_ignore_ascii_case("be") && first.complement.is_some();
            if passive {
                if let Some(agent) = first.roles.iter().find_map(|role| match role {
                    RolePp::Agent(np) => Some(np),
                    _ => None,
                }) {
                    return group_keys(agent);
                }
            }
            group_keys(subject)
        }
    }
}

// ---- normalization candidates (round 11) --------------------------------------------

/// What a [`NormalizationCandidate`] proposes. One kind in round 11:
/// active/passive alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalizationKind {
    /// The active-voice reading of a passive claim with a stated agent.
    ActivePassive,
}

/// A PROPOSED normalization of a claim — provenance-marked, PROPOSAL-ONLY
/// (round 11, change 6). Candidates PROPOSE edges; they never prove:
/// consumers must verify a candidate against the sentence's anchors and
/// raw text before acting on it, and the relation engine deliberately
/// does NOT consume candidates (no [`crate::relate`] integration — a
/// crude morphological guess must never ground a `Yes`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizationCandidate {
    pub kind: NormalizationKind,
    /// The proposed atom: the candidate verb (a crude stem — see
    /// [`normalization_candidates`]) with the original claim's patient as
    /// object and the non-Agent role tail preserved.
    pub atom: Atom,
    /// The proposed subject: the stated agent, digested as a subject.
    pub subject: SubjectSkeleton,
    /// The fixed provenance note — why this candidate exists and what it
    /// must not be trusted for.
    pub note: &'static str,
}

/// A small IRREGULAR participle → stem map (round 12, change 5): the
/// closed list below, nothing more. Candidates only — a map hit leads the
/// candidate list but is never claimed correct.
const IRREGULAR_PARTICIPLES: &[(&str, &str)] = &[
    ("sent", "send"),
    ("kept", "keep"),
    ("made", "make"),
    ("held", "hold"),
    ("built", "build"),
    ("left", "leave"),
    ("lost", "lose"),
    ("found", "find"),
    ("brought", "bring"),
    ("bought", "buy"),
    ("caught", "catch"),
    ("taught", "teach"),
    ("sold", "sell"),
    ("told", "tell"),
    ("paid", "pay"),
    ("laid", "lay"),
    ("said", "say"),
    ("read", "read"),
    ("run", "run"),
    ("done", "do"),
    ("given", "give"),
    ("taken", "take"),
    ("written", "write"),
    ("chosen", "choose"),
    ("seen", "see"),
    ("known", "know"),
];

/// The crude participle-stem CANDIDATE list (round 11; REORDERED AND
/// EXTENDED round 12, change 5 — superseding the round-11 "participle
/// itself always leads" pin: the better guesses now lead so consumers
/// trying candidates in order try the likeliest first, and the participle
/// itself closes the list as the always-present fallback). Order:
///
/// 1. the irregular-map hit ([`IRREGULAR_PARTICIPLES`]), when the
///    participle is in the closed list (`sent` → `send`);
/// 2. the DOUBLE-CONSONANT UNDOUBLED strip: the two-character `ed`/`en`
///    strip whose result ends in a doubled consonant, with one dropped
///    (`logged` → `log`, `stopped` → `stop`);
/// 3. the round-11 strips — a participle longer than three characters
///    ending in `ed` or `en` gives the two-character and one-character
///    strips (`logged` → `logg`, `logge`); otherwise a bare `d` ending
///    longer than two characters gives the `d`-strip;
/// 4. the participle itself.
///
/// Duplicates drop, order kept. ALL plausible stems are emitted; none is
/// claimed correct — still PROPOSAL-ONLY (no [`crate::relate`]
/// integration).
fn participle_stems(participle: &str) -> Vec<String> {
    let word = participle.to_lowercase();
    let mut stems: Vec<String> = Vec::new();
    let mut push = |s: &str| {
        if !s.is_empty() && !stems.iter().any(|x| x == s) {
            stems.push(s.to_string());
        }
    };
    if let Some((_, stem)) = IRREGULAR_PARTICIPLES.iter().find(|(p, _)| *p == word) {
        push(stem);
    }
    if word.len() > 3 && (word.ends_with("ed") || word.ends_with("en")) {
        let stripped = &word[..word.len() - 2];
        // Double-consonant undoubling (round 12): `logg` → `log`.
        let bytes = stripped.as_bytes();
        if bytes.len() >= 2 {
            let last = bytes[bytes.len() - 1];
            if last == bytes[bytes.len() - 2]
                && last.is_ascii_alphabetic()
                && !matches!(last, b'a' | b'e' | b'i' | b'o' | b'u')
            {
                push(&stripped[..stripped.len() - 1]);
            }
        }
        push(stripped);
        push(&word[..word.len() - 1]);
    } else if word.len() > 2 && word.ends_with('d') {
        push(&word[..word.len() - 1]);
    }
    push(&word);
    stems
}

/// The extracted passive site of [`normalization_candidates`]: participle,
/// agent group, patient (grammatical subject) group, manner, non-Agent
/// role tail.
type PassiveSite<'a> = (
    &'a str,
    &'a NpGroup,
    &'a NpGroup,
    &'a [String],
    Vec<&'a RolePp>,
);

/// Active/passive candidate alignment (round 11, change 6): for a PASSIVE
/// behavioral claim with a stated Agent — a description's agent slot (or a
/// hand-built [`RolePp::Agent`] in its role tail), or a deontic
/// `be`-complement's Agent role — emit the ACTIVE-VOICE candidate atoms:
/// subject := the agent (one candidate per coordinated agent item, surface
/// order), verb := each crude participle stem ([`participle_stems`] — all
/// plausible stems, never claimed correct), object := the grammatical
/// subject (the patient, one digest per item), roles := the non-Agent role
/// tail as written. The reverse direction (active → passive candidates) is
/// OUT OF SCOPE (legislated). Scope is deliberately narrow (legislated,
/// round 11): only single-word `Predicate::Words` participles qualify (a
/// multi-word predicate, a comparison, a `Pp`, or a capability is not a
/// passive participle site), and only a SINGLE deontic verb phrase (an
/// `either … or …` deontic emits nothing — alternatives do not share one
/// agent-voice normalization). Active sentences, definitions, and
/// agentless passives emit nothing.
///
/// AFFIRMATIVE BEHAVIORAL claims only (round 11 fix): a NEGATED site —
/// `is never submitted by …`, `shall not be sent by …` — emits NOTHING,
/// because the candidate atom carries no polarity slot, so the proposal
/// would be indistinguishable from the affirmative twin's and a consumer
/// pairing on it would align a never-claim with an affirmative active
/// claim. A PERMISSION (`may be sent by …`) emits nothing either: a
/// permission denotes admissibility, not behavior, and the feature is
/// scoped to behavioral claims.
///
/// DOCTRINE: candidates PROPOSE edges; they never prove. Consumers must
/// verify against the anchors/raw text; the relation engine does not read
/// them (deliberate — no [`crate::relate`] integration).
pub fn normalization_candidates(sentence: &Sentence) -> Vec<NormalizationCandidate> {
    const NOTE: &str = "active-voice candidate from a passive claim's stated agent; the verb \
                        stems are crude morphological guesses — verify against the anchors/raw \
                        text before proposing an edge";
    // The passive site: (participle, agent group, subject group, manner,
    // non-Agent roles).
    let site: Option<PassiveSite<'_>> = match &sentence.core {
        Core::Description {
            subject,
            predicate: Predicate::Words { words },
            agent,
            roles,
            adverb,
            ..
        } if words.len() == 1 && *adverb != Some(DescriptionAdverb::Never) => {
            let stated = agent.as_ref().or_else(|| {
                roles.iter().find_map(|role| match role {
                    RolePp::Agent(np) => Some(np),
                    _ => None,
                })
            });
            stated.map(|agent_np| {
                let tail: Vec<&RolePp> = roles
                    .iter()
                    .filter(|r| !matches!(r, RolePp::Agent(_)))
                    .collect();
                (words[0].as_str(), agent_np, subject, &[][..], tail)
            })
        }
        Core::Deontic {
            subject,
            vp: VpGroup::Single(vp),
            modal,
            negated,
        } if vp.verb.eq_ignore_ascii_case("be") && !*negated && *modal != Modal::May => {
            match &vp.complement {
                Some(Predicate::Words { words }) if words.len() == 1 => {
                    let agent_np = vp.roles.iter().find_map(|role| match role {
                        RolePp::Agent(np) => Some(np),
                        _ => None,
                    });
                    agent_np.map(|agent_np| {
                        let tail: Vec<&RolePp> = vp
                            .roles
                            .iter()
                            .filter(|r| !matches!(r, RolePp::Agent(_)))
                            .collect();
                        (
                            words[0].as_str(),
                            agent_np,
                            subject,
                            vp.manner.as_slice(),
                            tail,
                        )
                    })
                }
                _ => None,
            }
        }
        _ => None,
    };
    let Some((participle, agent, patient, manner, tail)) = site else {
        return Vec::new();
    };
    let agent_items: Vec<&Np> = match agent {
        NpGroup::Single(np) => vec![np],
        NpGroup::Coordinated { items, .. } => items.iter().collect(),
    };
    let mut candidates = Vec::new();
    for agent_np in agent_items {
        for stem in participle_stems(participle) {
            candidates.push(NormalizationCandidate {
                kind: NormalizationKind::ActivePassive,
                atom: Atom {
                    words: vec![stem],
                    manner: manner.iter().map(|w| w.to_lowercase()).collect(),
                    objects: object_skeletons(patient),
                    objects_conj: group_conj(patient),
                    roles: tail.iter().map(|role| role_skeleton(role)).collect(),
                    comparison: None,
                    content: None,
                },
                subject: subject_skeleton_of(agent_np),
                note: NOTE,
            });
        }
    }
    candidates
}

/// A resolved (or unresolved) definite reference within a specification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reference {
    /// Index of the sentence containing the definite noun phrase.
    pub sentence: usize,
    /// The head word of the definite noun phrase.
    pub head: String,
    pub resolution: Resolution,
}

/// How a definite noun phrase resolves (round 12, change 3 — the
/// `Ambiguous` variant is RESTORED, superseding the round-6 note that
/// declared it unreachable: that note was true only while resolution
/// matched heads alone; antecedents are now tracked by FULL noun-phrase
/// identity — the round-6 `full` string: modifiers + head + `of`-chain +
/// relative, lowercased — so differing introductions of one head are
/// visible again).
///
/// The rules, for a definite `the <np>` whose candidates are the prior
/// indefinite antecedents sharing its HEAD:
///
/// * no candidate → [`Resolution::Unresolved`] (deixis, not an error);
/// * all candidates share ONE full identity → [`Resolution::Unique`] to
///   the most recent;
/// * candidates with DIFFERING fulls: the reference's own modifiers
///   select — a reference with modifiers matches only candidates whose
///   full CONTAINS those modifiers (exact-token containment, lowercased).
///   When the selection lands on exactly one full identity, the
///   resolution is [`Resolution::Unique`] to its most recent
///   introduction; otherwise [`Resolution::Ambiguous`], carrying the
///   surviving candidates. LEGISLATED (round 12): a bare reference (no
///   modifiers) over differing fulls is Ambiguous over ALL candidates; a
///   modifier set matching NO candidate is Ambiguous over all candidates
///   too (antecedents of the head exist, none is selected — the honest
///   answer is the unresolved choice, not deixis); the candidate list is
///   deduplicated by full identity, keeping each full's MOST RECENT
///   introduction, in reading order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Resolution {
    /// The sentence index of the most recent indefinite antecedent.
    Unique { antecedent_sentence: usize },
    /// Multiple antecedents with differing full identities match, and the
    /// reference does not select one (round 12, change 3): the candidates,
    /// deduplicated by full identity (most recent introduction each), in
    /// reading order.
    Ambiguous {
        candidates: Vec<AntecedentCandidate>,
    },
    /// No antecedent: deixis to the system under specification, not an error.
    Unresolved,
}

/// One candidate antecedent of an [`Resolution::Ambiguous`] definite
/// reference (round 12, change 3): where it was introduced and its full
/// noun-phrase identity (the round-6 `full` string).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AntecedentCandidate {
    /// The sentence index of the introduction.
    pub sentence: usize,
    /// The introduction's full identity: lowercased render of
    /// modifiers + head + `of`-chain + relative, determiner excluded.
    pub full: String,
}

/// Controlled coreference over a specification: each definite NP (`the X`)
/// matched against indefinite introductions (`a X` / `an X`) earlier in the
/// text — candidates by exact head word, identity by the FULL noun-phrase
/// string (round 12, change 3; see [`Resolution`]). Analysis data, never a
/// parse error. A definite with no antecedent is deixis to the system under
/// specification.
pub fn references(specification: &Specification) -> Vec<Reference> {
    let mut references = Vec::new();
    // Every indefinite introduction, in reading order: head as written,
    // full identity, sentence index.
    let mut introduced: Vec<(String, String, usize)> = Vec::new();
    for (index, sentence) in specification.sentences.iter().enumerate() {
        for np in sentence_nps(sentence) {
            match np.det {
                Some(Det::A) | Some(Det::An) => {
                    introduced.push((np.head.clone(), np_full(np), index));
                }
                Some(Det::The) => {
                    let resolution = resolve_definite(np, &introduced);
                    references.push(Reference {
                        sentence: index,
                        head: np.head.clone(),
                        resolution,
                    });
                }
                _ => {}
            }
        }
    }
    references
}

/// Resolve one definite noun phrase against the introductions so far
/// (the rules on [`Resolution`]).
fn resolve_definite(np: &Np, introduced: &[(String, String, usize)]) -> Resolution {
    let candidates: Vec<&(String, String, usize)> = introduced
        .iter()
        .filter(|(head, _, _)| *head == np.head)
        .collect();
    if candidates.is_empty() {
        return Resolution::Unresolved;
    }
    let most_recent = |set: &[&(String, String, usize)]| -> Resolution {
        Resolution::Unique {
            antecedent_sentence: set.last().expect("non-empty").2,
        }
    };
    let one_full = |set: &[&(String, String, usize)]| -> bool {
        set.iter().all(|(_, full, _)| *full == set[0].1)
    };
    if one_full(&candidates) {
        return most_recent(&candidates);
    }
    // Differing fulls: the reference's own modifiers select by exact-token
    // containment over the candidate fulls.
    let modifiers: Vec<String> = np.modifiers.iter().map(|m| m.to_lowercase()).collect();
    if !modifiers.is_empty() {
        let selected: Vec<&(String, String, usize)> = candidates
            .iter()
            .filter(|(_, full, _)| {
                let tokens: Vec<&str> = full.split_whitespace().collect();
                modifiers.iter().all(|m| tokens.contains(&m.as_str()))
            })
            .copied()
            .collect();
        if !selected.is_empty() && one_full(&selected) {
            return most_recent(&selected);
        }
        if !selected.is_empty() {
            return Resolution::Ambiguous {
                candidates: dedup_by_full(&selected),
            };
        }
        // No candidate carries the modifiers: ambiguous over all
        // (legislated — see [`Resolution`]).
    }
    Resolution::Ambiguous {
        candidates: dedup_by_full(&candidates),
    }
}

/// Deduplicate candidates by full identity, keeping each full's MOST
/// RECENT introduction, in reading order (legislated, round 12).
fn dedup_by_full(set: &[&(String, String, usize)]) -> Vec<AntecedentCandidate> {
    let mut out: Vec<AntecedentCandidate> = Vec::new();
    for (_, full, sentence) in set {
        if let Some(existing) = out.iter_mut().find(|c| c.full == *full) {
            existing.sentence = *sentence;
        } else {
            out.push(AntecedentCandidate {
                sentence: *sentence,
                full: full.clone(),
            });
        }
    }
    out
}

// ---- noun-phrase traversal ----------------------------------------------------------

/// All noun phrases of a sentence, in reading order: frames first, then the
/// core, then the exception and purpose adjuncts.
fn sentence_nps(sentence: &Sentence) -> Vec<&Np> {
    let mut out = Vec::new();
    for frame in sentence.frames.scopes.iter().chain(&sentence.frames.states) {
        clause_group_nps(&frame.clause, &mut out);
    }
    if let Some(trigger) = &sentence.frames.trigger {
        clause_group_nps(&trigger.clause, &mut out);
    }
    match &sentence.core {
        Core::Definition { term, definiens } => {
            np_nps(term, &mut out);
            match definiens {
                Definiens::Np { np, roles } => {
                    group_nps(np, &mut out);
                    for role in roles {
                        role_nps(role, &mut out);
                    }
                }
                Definiens::Clause(clause) => clause_nps(clause, &mut out),
            }
        }
        Core::Description {
            subject,
            predicate,
            agent,
            roles,
            ..
        } => {
            group_nps(subject, &mut out);
            predicate_nps(predicate, &mut out);
            if let Some(agent) = agent {
                group_nps(agent, &mut out);
            }
            for role in roles {
                role_nps(role, &mut out);
            }
        }
        Core::Deontic { subject, vp, .. } => {
            group_nps(subject, &mut out);
            for item in vp.items() {
                vp_nps(item, &mut out);
            }
        }
    }
    if let Some(exception) = &sentence.exception {
        clause_nps(exception, &mut out);
    }
    match &sentence.purpose {
        Some(Purpose::SoThat(clause)) => clause_nps(clause, &mut out),
        Some(Purpose::InOrderTo(vp)) => vp_nps(vp, &mut out),
        None => {}
    }
    out
}

fn clause_group_nps<'a>(group: &'a ClauseGroup, out: &mut Vec<&'a Np>) {
    for clause in &group.items {
        clause_nps(clause, out);
    }
}

fn clause_nps<'a>(clause: &'a Clause, out: &mut Vec<&'a Np>) {
    group_nps(&clause.subject, out);
    match &clause.body {
        ClauseBody::Copular {
            predicate,
            agent,
            roles,
            ..
        } => {
            predicate_nps(predicate, out);
            if let Some(agent) = agent {
                group_nps(agent, out);
            }
            for role in roles {
                role_nps(role, out);
            }
        }
        ClauseBody::Verbal {
            object,
            roles,
            content,
            ..
        } => {
            if let Some(object) = object {
                group_nps(object, out);
            }
            for role in roles {
                role_nps(role, out);
            }
            if let Some(content) = content {
                clause_nps(content, out);
            }
        }
    }
}

fn group_nps<'a>(group: &'a NpGroup, out: &mut Vec<&'a Np>) {
    match group {
        NpGroup::Single(np) => np_nps(np, out),
        NpGroup::Coordinated { items, .. } => {
            for np in items {
                np_nps(np, out);
            }
        }
    }
}

fn np_nps<'a>(np: &'a Np, out: &mut Vec<&'a Np>) {
    out.push(np);
    if let Some(of) = &np.of {
        np_nps(of, out);
    }
    if let Some(relative) = &np.relative {
        match &relative.body {
            RelativeBody::Copular {
                predicate,
                agent,
                roles,
                ..
            } => {
                predicate_nps(predicate, out);
                if let Some(agent) = agent {
                    group_nps(agent, out);
                }
                for role in roles {
                    role_nps(role, out);
                }
            }
            RelativeBody::Verbal { object, roles, .. } => {
                if let Some(object) = object {
                    group_nps(object, out);
                }
                for role in roles {
                    role_nps(role, out);
                }
            }
            RelativeBody::ObjectGap { subject, roles, .. } => {
                group_nps(subject, out);
                for role in roles {
                    role_nps(role, out);
                }
            }
        }
    }
}

fn vp_nps<'a>(vp: &'a Vp, out: &mut Vec<&'a Np>) {
    if let Some(object) = &vp.object {
        group_nps(object, out);
    }
    if let Some(complement) = &vp.complement {
        predicate_nps(complement, out);
    }
    for role in &vp.roles {
        role_nps(role, out);
    }
    if let Some(content) = &vp.content {
        clause_nps(content, out);
    }
}

fn role_nps<'a>(role: &'a RolePp, out: &mut Vec<&'a Np>) {
    match role {
        RolePp::Recipient(np)
        | RolePp::Topic(np)
        | RolePp::Source(np)
        | RolePp::Goal(np)
        | RolePp::Location { np, .. }
        | RolePp::Agent(np)
        | RolePp::Means { np, .. } => group_nps(np, out),
        RolePp::Deadline(measure) | RolePp::Duration(measure) => measure_nps(measure, out),
        RolePp::Rate { .. } => {}
        RolePp::Before(clause) | RolePp::After(clause) | RolePp::Until(clause) => {
            clause_nps(clause, out)
        }
    }
}

fn predicate_nps<'a>(predicate: &'a Predicate, out: &mut Vec<&'a Np>) {
    match predicate {
        Predicate::Comparison(comparison) => {
            measure_nps(&comparison.value, out);
            if let Some(upper) = &comparison.upper {
                measure_nps(upper, out);
            }
        }
        Predicate::Pp { np, .. } => group_nps(np, out),
        Predicate::AbleTo { vp } => vp_nps(vp, out),
        Predicate::Words { .. } => {}
    }
}

fn measure_nps<'a>(measure: &'a Measure, out: &mut Vec<&'a Np>) {
    if let Measure::Np { np } = measure {
        group_nps(np, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use so_lang::parse::parse;

    fn sentence(input: &str) -> Sentence {
        parse(input).unwrap().sentences.remove(0)
    }

    #[test]
    fn speech_acts_by_pivot() {
        assert_eq!(
            speech_act(&sentence("The pump shall stop.")),
            SpeechAct::Obligation
        );
        assert_eq!(
            speech_act(&sentence("The daemon shall not store derived views.")),
            SpeechAct::Prohibition
        );
        assert_eq!(
            speech_act(&sentence("The retry count is at most 3.")),
            SpeechAct::Description
        );
        assert_eq!(
            speech_act(&sentence("A session means a sequence of requests.")),
            SpeechAct::Definition
        );
        assert_eq!(
            speech_act(&sentence("The client may retry.")),
            SpeechAct::Permission
        );
        assert_eq!(
            speech_act(&sentence("The library should install propagators.")),
            SpeechAct::Recommendation
        );
    }

    #[test]
    fn force_by_modal() {
        assert_eq!(
            force(&sentence("The pump shall stop.")),
            Some(Force::Binding)
        );
        assert_eq!(
            force(&sentence("The pump must stop.")),
            Some(Force::Binding)
        );
        assert_eq!(
            force(&sentence("The pump should stop.")),
            Some(Force::Recommended)
        );
        assert_eq!(force(&sentence("The pump may stop.")), None);
        assert_eq!(force(&sentence("The pump is stopped.")), None);
    }

    #[test]
    fn denotations() {
        match denote(&sentence("The client may retry.")) {
            Denotation::Admissibility(assertion) => {
                assert!(matches!(assertion.claim, Claim::Admissible { .. }));
            }
            other => panic!("expected admissibility, got {other:?}"),
        }
        match denote(&sentence("The daemon shall not store derived views.")) {
            Denotation::Behavior(assertion) => match assertion.claim {
                Claim::Action {
                    polarity: Polarity::Negative,
                    force: Force::Binding,
                    ..
                } => {}
                other => panic!("expected negative binding action, got {other:?}"),
            },
            other => panic!("expected behavior, got {other:?}"),
        }
        match denote(&sentence("The temperature is never above the limit.")) {
            Denotation::Behavior(assertion) => match assertion.claim {
                Claim::State {
                    polarity: Polarity::Negative,
                    ..
                } => {}
                other => panic!("expected negative state, got {other:?}"),
            },
            other => panic!("expected behavior, got {other:?}"),
        }
    }

    #[test]
    fn ingest_contract_projection() {
        assert!(ingest_contract(&sentence("A session means a sequence of requests.")).is_none());
        // A permission admits rather than constrains: no lone-sentence
        // contract; it pairs into contracts on the environment side.
        assert!(ingest_contract(&sentence("The client may retry.")).is_none());
        let contract = ingest_contract(&sentence("The pump shall stop.")).unwrap();
        assert_eq!(contract.assumption.render(), "⊤");
        assert_eq!(contract.act, SpeechAct::Obligation);
        assert_eq!(contract.force, Some(Force::Binding));
        assert_eq!(contract.guarantee.subject.heads(), vec!["pump"]);
    }

    #[test]
    fn skeleton_sees_through_surface_differences() {
        // `No request is logged.` vs `Each request shall be logged.`:
        // identical atoms, opposite polarity, Negative vs Universal.
        let no = skeleton(&sentence("No request is logged.")).unwrap();
        let each = skeleton(&sentence("Each request shall be logged.")).unwrap();
        assert_eq!(no.atoms[0].words, vec!["logged"]);
        assert_eq!(each.atoms[0].words, vec!["logged"]);
        assert_eq!(no.atoms[0], each.atoms[0]);
        assert_eq!(no.subject.quantifier, Quantifier::Negative);
        assert_eq!(each.subject.quantifier, Quantifier::Universal);
        assert_eq!(no.subject.head, "request");
        assert_eq!(each.subject.head, "request");
        assert_eq!(no.polarity, Polarity::Negative);
        assert_eq!(each.polarity, Polarity::Affirmative);
        assert_eq!(each.force, Some(Force::Binding));
        assert_eq!(no.act, SpeechAct::Description);
        assert_eq!(each.act, SpeechAct::Obligation);
    }

    #[test]
    fn skeleton_prohibition_matches_never_description() {
        let prohibition = skeleton(&sentence("The request shall not be logged.")).unwrap();
        let never = skeleton(&sentence("The request is never logged.")).unwrap();
        assert_eq!(prohibition.atoms[0].words, vec!["logged"]);
        assert_eq!(prohibition.atoms[0], never.atoms[0]);
        assert_eq!(prohibition.polarity, Polarity::Negative);
        assert_eq!(never.polarity, Polarity::Negative);
    }

    #[test]
    fn skeleton_double_negation_composes_to_affirmative() {
        // Modal `not` XOR subject `no`: two flips cancel.
        let s = skeleton(&sentence("No request shall not be logged.")).unwrap();
        assert_eq!(s.subject.quantifier, Quantifier::Negative);
        assert_eq!(s.polarity, Polarity::Affirmative);
        assert_eq!(s.atoms[0].words, vec!["logged"]);
    }

    #[test]
    fn skeleton_scope_and_shape() {
        // Definitions have no skeleton.
        assert!(skeleton(&sentence("A session means a sequence of requests.")).is_none());
        // Coordinated subjects have no single normal form in v0.2.
        assert!(skeleton(&sentence("The pump and the valve shall stop.")).is_none());
        // Action atoms carry the verb and the object digests (quantifier +
        // lowercased head).
        let s = skeleton(&sentence("The daemon shall persist the Node.")).unwrap();
        assert_eq!(s.atoms[0].words, vec!["persist"]);
        assert_eq!(
            s.atoms[0].objects,
            vec![ObjectSkeleton {
                quantifier: Quantifier::Definite,
                head: "node".into(),
                full: "node".into(),
            }]
        );
        assert_eq!(s.subject.quantifier, Quantifier::Definite);
        // No lemmatization: surface words only. Round 5: a bare-plural
        // behavioral subject is the generic reading — Universal.
        let s = skeleton(&sentence("Requests are logged.")).unwrap();
        assert_eq!(s.subject.quantifier, Quantifier::Universal);
        assert_eq!(s.atoms[0].words, vec!["logged"]);
        // A permission still has a skeleton (its denotation is admissible
        // behavior), with no force.
        let s = skeleton(&sentence("The client may retry.")).unwrap();
        assert_eq!(s.act, SpeechAct::Permission);
        assert_eq!(s.force, None);
        assert_eq!(s.atoms[0].words, vec!["retry"]);
    }

    #[test]
    fn definite_references_resolve_to_most_recent_introduction() {
        let spec = parse(
            "A session means a sequence of requests. \
             When a session expires, the system shall close the session.",
        )
        .unwrap();
        let refs = references(&spec);
        // `the system` (unresolved deixis) and `the session` (resolved).
        assert_eq!(refs.len(), 2);
        assert_eq!(refs[0].head, "system");
        assert_eq!(refs[0].resolution, Resolution::Unresolved);
        assert_eq!(refs[1].head, "session");
        assert_eq!(
            refs[1].resolution,
            Resolution::Unique {
                antecedent_sentence: 1
            },
            "the frame's own `a session` is the most recent introduction"
        );
    }
}
