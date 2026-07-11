//! The abstract syntax of the constrained specification language.
//!
//! This module is the surface layer: it names the categories a specification
//! sentence is made of — speech-act cores, circumstance frames, noun and verb
//! phrases, thematic roles — and nothing else. It deliberately contains no
//! assume-guarantee vocabulary: contracts are one *interpretation* of these
//! structures, defined in [`crate::semantics`], and the syntax must remain
//! definable without them.
//!
//! The unit of the language is the [`Specification`]: a sequence of sentences,
//! each performing one specification act — defining a term, describing the
//! system, or obliging / forbidding / recommending / permitting behavior —
//! under zero or more circumstance frames, with an optional exception and an
//! optional statement of purpose.
//!
//! Losslessness: every meaning-bearing word of the input is present in the
//! tree — determiners, quantifiers, modality, polarity, thematic roles — and
//! [`Sentence::render`] reproduces the sentence in canonical form (closed-class
//! words in canonical casing, single spaces, a trailing period). The exact
//! input slice is retained in [`Sentence::source`]; raw text remains the source
//! of truth wherever a sentence is persisted.

use serde::{Deserialize, Serialize};

/// A specification: one or more sentences. Parsing yields this top category —
/// not a contract, not a single statement form.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Specification {
    pub sentences: Vec<Sentence>,
}

/// One sentence: circumstance frames, a speech-act core, an optional exception
/// carve-out, and an optional purpose.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sentence {
    /// The exact input slice this sentence was parsed from (surrounding
    /// whitespace trimmed, terminator included when present). The raw words are
    /// the source of truth; the tree is their structure.
    pub source: String,
    pub frames: Frames,
    pub core: Core,
    /// `…, unless <clause>` — a carve-out from the frames' applicability. An
    /// exception is defeasibility structure, not a contradiction.
    pub exception: Option<Clause>,
    /// `…, so that <clause>` / `…, in order to <vp>` — intent. A purpose does
    /// not constrain behavior; it is evidence of what the sentence serves.
    pub purpose: Option<Purpose>,
}

/// The circumstance frames, in canonical order: configuration scopes (`Where`),
/// state scopes (`While`), and at most one trigger (`When` / `If`). Frame
/// keywords retain their surface casing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Frames {
    pub scopes: Vec<Frame>,
    pub states: Vec<Frame>,
    pub trigger: Option<Trigger>,
}

impl Frames {
    pub fn is_empty(&self) -> bool {
        self.scopes.is_empty() && self.states.is_empty() && self.trigger.is_none()
    }
}

/// One `Where`/`While` frame: the keyword as written and its clause group.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Frame {
    pub keyword: String,
    pub clause: ClauseGroup,
}

/// The trigger frame. `When` marks an ordinary event; `If` marks a contingency
/// (EARS' unwanted-behaviour form). A sentence has at most one trigger: the
/// conjunction of two occurrences has no single reading, so the grammar rejects
/// it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trigger {
    pub kind: TriggerKind,
    pub keyword: String,
    pub clause: ClauseGroup,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TriggerKind {
    Event,
    Contingency,
}

/// The speech-act core: what kind of specification act the sentence performs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Core {
    /// `<term> means <definiens>` — establishes vocabulary. Timeless: only
    /// `Where` frames may scope a definition.
    Definition { term: Np, definiens: Definiens },
    /// `<subject> is/are [always|never] <predicate> [by <np-group>]` —
    /// describes how the system is (an invariant), with no deontic force.
    /// The optional trailing `by` phrase is the PASSIVE AGENT (`The request
    /// is logged by the daemon.`) — round 5; outside a passive site `by`
    /// is rejected, never silently swallowed.
    Description {
        subject: NpGroup,
        copula: Copula,
        adverb: Option<DescriptionAdverb>,
        predicate: Predicate,
        /// `by <np-group>` after the predicate: the passive agent.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        agent: Option<NpGroup>,
        /// The thematic-role tail after the passive agent (round 8
        /// follow-up): `The request is logged by the daemon within 5
        /// seconds.` keeps its Deadline structured, so the described
        /// passive still meets the deontic passive at one atom. Present
        /// only behind an agent — an agentless description keeps the
        /// plain predicate reading (its tail stays predicate words).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
    /// `<subject> shall/must/should [not] <vp>` or `<subject> may <vp>` — the
    /// normative acts: obligation, prohibition, recommendation, permission.
    /// Round 6: the verb phrase slot is a [`VpGroup`], so a single sentence
    /// can state genuine ALTERNATIVES — `shall either accept the request or
    /// reject the request` — which splitting into two sentences cannot
    /// (two sentences oblige both).
    Deontic {
        subject: NpGroup,
        modal: Modal,
        negated: bool,
        vp: VpGroup,
    },
}

/// A verb phrase or an explicit alternation of verb phrases (round 6):
/// `either <vp> or <vp> [or <vp>]…`. The `either` marker is REQUIRED and
/// the conjunction is `or` only — `and`-coordination of verb phrases stays
/// unsupported, because two sentences already mean exactly that (both
/// required), so the coordination would add a second spelling, not a
/// meaning. Deontic cores only (v0.2): descriptions and capabilities keep
/// a single verb phrase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
// `Single(Vp)` dwarfs the vector variant, but boxing it would put an
// indirection on the overwhelmingly common case and break every
// destructuring site; syntax trees are per-sentence values, not bulk
// storage.
#[allow(clippy::large_enum_variant)]
pub enum VpGroup {
    Single(Vp),
    Alternatives { items: Vec<Vp> },
}

impl VpGroup {
    /// The lone verb phrase, when this is not an alternation.
    pub fn single(&self) -> Option<&Vp> {
        match self {
            VpGroup::Single(vp) => Some(vp),
            VpGroup::Alternatives { .. } => None,
        }
    }

    /// The verb phrases of the group: one for a single phrase, one per
    /// alternative otherwise.
    pub fn items(&self) -> &[Vp] {
        match self {
            VpGroup::Single(vp) => std::slice::from_ref(vp),
            VpGroup::Alternatives { items } => items,
        }
    }

    pub fn render(&self) -> String {
        match self {
            VpGroup::Single(vp) => vp.render(),
            VpGroup::Alternatives { items } => {
                let rendered: Vec<String> = items.iter().map(Vp::render).collect();
                format!("either {}", rendered.join(" or "))
            }
        }
    }
}

/// What a defined term means: a noun phrase (with optional trailing role
/// phrases) or a full clause.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
// The clause variant outgrew the lint threshold when measures gained
// bounds (round 6); boxing would break destructuring sites for no
// practical win — see the note on [`VpGroup`].
#[allow(clippy::large_enum_variant)]
pub enum Definiens {
    Np { np: NpGroup, roles: Vec<RolePp> },
    Clause(Clause),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Copula {
    Is,
    Are,
}

impl Copula {
    pub fn as_str(&self) -> &'static str {
        match self {
            Copula::Is => "is",
            Copula::Are => "are",
        }
    }
}

/// `always` / `never` in a description. Negation in a description is expressed
/// by `never` — a dedicated site, so its scope is syntactically fixed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DescriptionAdverb {
    Always,
    Never,
}

/// The deontic modals. `shall` and `must` are both binding (the word used is
/// preserved here); `should` is a recommendation; `may` is a permission.
/// `may not` and `can` are rejected by the grammar as ambiguous.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Modal {
    Shall,
    Must,
    Should,
    May,
}

impl Modal {
    pub fn as_str(&self) -> &'static str {
        match self {
            Modal::Shall => "shall",
            Modal::Must => "must",
            Modal::Should => "should",
            Modal::May => "may",
        }
    }
}

// ---- clauses ----------------------------------------------------------------

/// A clause or a coordination of clauses under one conjunction — the guard of
/// a circumstance frame. `conj` is `None` exactly when there is one item.
/// `and` reads as a joint guard (all items hold together; in a trigger, at
/// most one item is an event and the rest are states read at its instant —
/// the recognizer rejects more); `or` as an alternative guard (in a trigger,
/// alternation: either occurrence fires it) — either way the group is ONE
/// frame. Only frames and triggers coordinate clauses; exceptions, purposes,
/// `before`/`after`, and definiens keep a single clause (v0.2 scope).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClauseGroup {
    pub conj: Option<Conj>,
    pub items: Vec<Clause>,
}

impl ClauseGroup {
    /// A group of one clause, for construction in tests.
    pub fn single(clause: Clause) -> ClauseGroup {
        ClauseGroup {
            conj: None,
            items: vec![clause],
        }
    }

    pub fn render(&self) -> String {
        let conj = self.conj.unwrap_or(Conj::And);
        self.items
            .iter()
            .map(Clause::render)
            .collect::<Vec<_>>()
            .join(&format!(" {} ", conj.as_str()))
    }
}

/// A clause: the internal grammar of frames, exceptions, purposes, and
/// definiens — a subject and what is said of it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Clause {
    pub subject: NpGroup,
    pub body: ClauseBody,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ClauseBody {
    /// `<np> is|are|remains <predicate> [by <np-group>] [<role-pp>…]` — a
    /// state or (read under `When`) an event in passive form. The frame
    /// keyword, not a dictionary, fixes the temporal reading. The optional
    /// `by` phrase is the passive agent (round 5): `when the request is
    /// submitted by the user, …`. Round 8: the predicate carries a
    /// thematic-role TAIL (`while the pump is active at the depot`), so
    /// locatives, deadlines, and `until`/`before`/`after` are structured
    /// roles instead of flat predicate words. The dedicated `agent` slot
    /// keeps the round-5 shape — a `by` IMMEDIATELY after the predicate;
    /// a `by` later in the tail is the Agent role in `roles` (a copular
    /// body is a passive site, so role-position `by` is admitted). Both
    /// spellings digest to one Agent role.
    Copular {
        copula: ClauseCopula,
        predicate: Predicate,
        /// `by <np-group>` immediately after the predicate: the passive
        /// agent.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        agent: Option<NpGroup>,
        /// The predicate's thematic-role tail (round 8), after the agent.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
    /// `<np> <verb> [<particle>] [<np>] [<role-pp>…]` — an active-voice event
    /// or state. The particle is the controlled particle-verb slot (`logs
    /// out`, `shuts down`); the roles are the same thematic-role phrases a
    /// verb phrase carries, so a clause can state channel, source,
    /// destination, location, and timing. `before`/`after` roles nest a
    /// clause, so an event can be stated relative to another (`the payment
    /// clears after the order ships`).
    Verbal {
        verb: String,
        particle: Option<String>,
        /// Bare post-verbal manner adverbs (`completes successfully`), in
        /// surface order and casing — the controlled manner slot shared with
        /// [`Vp::manner`].
        manner: Vec<String>,
        object: Option<NpGroup>,
        roles: Vec<RolePp>,
        /// The CONTENT complement (round 9, revising the round-7 "clause
        /// bodies stay content-free" legislation on new grounds:
        /// assumptions depend on observed/asserted content, so dependency
        /// statements belong in guards): `when the monitor ensures that
        /// the token is valid, …` — the same shape as [`Vp::content`],
        /// FINAL in the clause (roles precede it; the nested clause
        /// consumes the rest of the clause slice), same depth accounting.
        /// Content-`that` opens only where a relative cannot attach —
        /// directly after the verb (or its particle/manner run) or after
        /// a role; after a noun, `that` stays that noun's restrictive
        /// relative. RelativeBody verbal arms carry NO content slot in
        /// v0.2 (legislated). Serde-defaulted, so pre-round-9 trees load.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        content: Option<Box<Clause>>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ClauseCopula {
    Is,
    Are,
    Remains,
}

impl ClauseCopula {
    pub fn as_str(&self) -> &'static str {
        match self {
            ClauseCopula::Is => "is",
            ClauseCopula::Are => "are",
            ClauseCopula::Remains => "remains",
        }
    }
}

/// The purpose adjunct: intent, not behavior.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Purpose {
    SoThat(Clause),
    InOrderTo(Vp),
}

// ---- noun phrases -------------------------------------------------------------

/// A noun phrase or a coordination of noun phrases. Coordination uses one
/// conjunction throughout; mixing `and` and `or` in one group is rejected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum NpGroup {
    Single(Np),
    Coordinated {
        conj: Conj,
        /// `both … and …` / `either … or …` when explicitly marked.
        marker: Option<GroupMarker>,
        items: Vec<Np>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Conj {
    And,
    Or,
}

impl Conj {
    pub fn as_str(&self) -> &'static str {
        match self {
            Conj::And => "and",
            Conj::Or => "or",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GroupMarker {
    Both,
    Either,
}

/// A noun phrase: determiner or quantifier, modifiers, head, `of`-chain, and an
/// optional restrictive relative clause. Determiners and quantifiers are kept —
/// `each request` and `requests` are different obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Np {
    pub det: Option<Det>,
    /// Open-class words before the head (adjectives, compound-noun parts), in
    /// surface order and casing.
    pub modifiers: Vec<String>,
    pub head: String,
    /// `of <np>` — the only noun-attached preposition; all other prepositions
    /// are thematic roles on the predicate.
    pub of: Option<Box<Np>>,
    /// Boxed to break the size recursion through the relative body's
    /// predicate, which may itself contain noun phrases.
    pub relative: Option<Box<Relative>>,
}

impl Np {
    /// A bare head, for construction in tests.
    pub fn bare(head: &str) -> Np {
        Np {
            det: None,
            modifiers: Vec::new(),
            head: head.to_string(),
            of: None,
            relative: None,
        }
    }
}

/// Determiners and quantifiers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Det {
    The,
    A,
    An,
    Each,
    Every,
    All,
    Any,
    /// `no` — a negation site: its scope is the noun phrase it determines.
    No,
    // Struct variants (not newtypes over the bare number): an internally
    // tagged enum cannot serialize a newtype variant holding a primitive.
    AtLeast {
        n: u64,
    },
    AtMost {
        n: u64,
    },
    Exactly {
        n: u64,
    },
}

impl Det {
    pub fn render(&self) -> String {
        match self {
            Det::The => "the".to_string(),
            Det::A => "a".to_string(),
            Det::An => "an".to_string(),
            Det::Each => "each".to_string(),
            Det::Every => "every".to_string(),
            Det::All => "all".to_string(),
            Det::Any => "any".to_string(),
            Det::No => "no".to_string(),
            Det::AtLeast { n } => format!("at least {n}"),
            Det::AtMost { n } => format!("at most {n}"),
            Det::Exactly { n } => format!("exactly {n}"),
        }
    }
}

/// A restrictive relative clause, attached to the immediately preceding head.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Relative {
    pub marker: RelMarker,
    pub body: RelativeBody,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RelMarker {
    That,
    Who,
}

impl RelMarker {
    pub fn as_str(&self) -> &'static str {
        match self {
            RelMarker::That => "that",
            RelMarker::Who => "who",
        }
    }
}

/// The body of a restrictive relative clause. Round 7: the verbal body is
/// the FULL verbal tail — verb, particle, manner, object, and thematic
/// roles — mirroring [`ClauseBody::Verbal`], so `each request that arrives
/// from the gateway` restricts by source. Roles inside a relative attach
/// to the RELATIVE's verb (innermost attachment, legislated): `the session
/// that holds the lock in the vault` locates the HOLDING; write the role
/// before the object's relative to attach it to the outer verb. The new
/// slots default empty under serde, so pre-round-7 trees still load.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RelativeBody {
    /// Round 8: the copular body mirrors [`ClauseBody::Copular`] — an
    /// optional passive agent (`that is signed by the user`) and a
    /// thematic-role tail (`that is valid within 5 seconds`), attached to
    /// the RELATIVE's predicate (innermost attachment, as for verbal
    /// relatives). The new slots default empty under serde, so pre-round-8
    /// trees still load.
    Copular {
        copula: ClauseCopula,
        predicate: Predicate,
        /// `by <np-group>` immediately after the predicate: the passive
        /// agent (round 8).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        agent: Option<NpGroup>,
        /// The predicate's thematic-role tail (round 8), after the agent.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
    Verbal {
        verb: String,
        /// The controlled particle-verb slot, as in [`ClauseBody::Verbal`].
        #[serde(default, skip_serializing_if = "Option::is_none")]
        particle: Option<String>,
        /// Bare post-verbal manner adverbs, in surface order and casing.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        manner: Vec<String>,
        object: Option<NpGroup>,
        /// The relative verb's own thematic-role phrases (round 7).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
    /// Round 9: an OBJECT-GAP relative — `each request that the gateway
    /// forwards`: the restricted head is the MISSING OBJECT of the
    /// relative's verb (exactly one gap, implicit), and the relative
    /// carries its own subject plus the verbal tail WITHOUT an object
    /// slot. The gap reading opens only when a determiner/quantifier-led
    /// noun phrase follows `that`/`who` (LEGISLATED: a bare noun phrase
    /// there keeps the round-7 subject-gap verbal reading — `that holds
    /// locks` is verb + object, and no lexicon could tell it from a gap's
    /// subject + verb). An explicit determiner-led object after the gap's
    /// verb means this is NOT a gap; the sentence keeps the round-6
    /// `DeterminerAsVerb` diagnosis. Renders `that <subject> <verb> …`.
    ObjectGap {
        subject: NpGroup,
        verb: String,
        /// The controlled particle-verb slot, as in [`ClauseBody::Verbal`].
        #[serde(default, skip_serializing_if = "Option::is_none")]
        particle: Option<String>,
        /// Bare post-verbal manner adverbs, in surface order and casing.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        manner: Vec<String>,
        /// The gap verb's own thematic-role phrases (innermost
        /// attachment, exactly as for round-7 verbal relatives).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        roles: Vec<RolePp>,
    },
}

// ---- verb phrases -------------------------------------------------------------

/// A verb phrase: the verb, an optional particle, an optional object,
/// thematic-role phrases, and — when the verb is `be` — a complement
/// predicate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Vp {
    pub verb: String,
    /// The controlled particle-verb slot: `out`, `down`, `up`, or `off`
    /// immediately after the verb (`logs out`, `shuts down the server`).
    /// `in`/`on` are NOT particles — they open Location roles; hyphenation
    /// (`logs-in`) stays the workaround for those.
    pub particle: Option<String>,
    /// The controlled manner slot: bare `-ly` adverbs in post-verbal
    /// position (`stop immediately`), in surface order and casing. Manner
    /// words are recognized only where an object or role would start —
    /// never inside a noun phrase (`the assembly`, `the nightly build` are
    /// untouched) — and render right after the verb/particle, before the
    /// object, so the canonical form re-parses to the same tree.
    pub manner: Vec<String>,
    pub object: Option<NpGroup>,
    pub roles: Vec<RolePp>,
    pub complement: Option<Predicate>,
    /// The CONTENT complement (round 7): `<verb> that <clause>` — `shall
    /// ensure that the token is valid`. Content is FINAL in the verb
    /// phrase: roles must precede it (`verify within 5 seconds that the
    /// token is valid`), and the clause consumes the rest of the phrase.
    /// Renders `that <clause>` after the roles. Content-`that` opens only
    /// where a relative cannot attach — directly after the verb (or its
    /// particle/manner run) or after a measure role; directly after a noun,
    /// `that` is that noun's restrictive relative (legislated, round 7).
    /// Verbal clause bodies (frames) carry the same final slot since
    /// round 9 ([`ClauseBody::Verbal`]); only relative verbal tails stay
    /// content-free in v0.2.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<Box<Clause>>,
}

/// A thematic-role phrase. The preposition fixes the role; the role is why the
/// phrase matters — recipients, deadlines, and means are load-bearing
/// specification content, not decoration on an opaque response string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "role", rename_all = "snake_case")]
pub enum RolePp {
    /// `to <np>`
    Recipient(NpGroup),
    /// `via <np>` / `using <np>`
    Means { marker: MeansMarker, np: NpGroup },
    /// `about <np>`
    Topic(NpGroup),
    /// `within <measure>` — deadlines carry a refinement order of their own.
    Deadline(Measure),
    /// `for <measure>`
    Duration(Measure),
    /// `per <unit>`
    Rate { unit: String },
    /// `before <clause>`. The clause is boxed (as in `After`/`Until`): a
    /// clausal role nests whole clauses inside roles inside clauses, and
    /// keeping the payload behind one pointer keeps the recursive parser's
    /// stack frames small at the shared depth bound.
    Before(Box<Clause>),
    /// `after <clause>` (boxed — see `Before`).
    After(Box<Clause>),
    /// `until <clause>` — the behavior holds up to the clause's occurrence.
    /// The companion of `before`/`after`: same clause parsing, same depth
    /// accounting (boxed — see `Before`).
    Until(Box<Clause>),
    /// `from <np>`
    Source(NpGroup),
    /// `into <np>`
    Goal(NpGroup),
    /// `in|on|at|under|over|above|below <np>` — where the behavior happens.
    /// The preposition is kept as written; `at` opens a location only when it
    /// is not the comparison opener `at least`/`at most`.
    Location { preposition: String, np: NpGroup },
    /// `by <np>` — the passive agent, admitted ONLY in a `be` verb phrase
    /// (`shall be logged by the daemon`); everywhere else a role-position
    /// `by` is rejected ([`crate::parse::ParseError::ByOutsidePassive`]).
    Agent(NpGroup),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MeansMarker {
    Via,
    Using,
}

impl MeansMarker {
    pub fn as_str(&self) -> &'static str {
        match self {
            MeansMarker::Via => "via",
            MeansMarker::Using => "using",
        }
    }
}

// ---- predicates and measures ---------------------------------------------------

/// What is predicated of a subject (in descriptions, copular clauses, relative
/// clauses, and `be`-complements).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Predicate {
    /// A comparison — an SMT-ready atom.
    Comparison(Comparison),
    /// A capability: `able to <vp>`, exactly after a description's copula
    /// with no adverb between (`The client is able to retry.`). Boxed to
    /// break the size recursion (a verb phrase's complement is itself a
    /// predicate).
    AbleTo { vp: Box<Vp> },
    /// A locative/relational prepositional predicate: `below the limit`,
    /// `in flight mode`.
    Pp { preposition: String, np: NpGroup },
    /// An open-class adjective/participle phrase: `running`, `frozen`,
    /// `greater accuracy` is *not* this — comparisons parse first. A struct
    /// variant (not a newtype over the list): an internally tagged enum
    /// cannot serialize a newtype variant holding a sequence.
    Words { words: Vec<String> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Comparison {
    pub op: ComparisonOp,
    pub value: Measure,
    /// The upper bound of `between <value> and <upper>`.
    pub upper: Option<Measure>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ComparisonOp {
    GreaterThan,
    LessThan,
    AtLeast,
    AtMost,
    EqualTo,
    Between,
}

impl ComparisonOp {
    pub fn render(&self) -> &'static str {
        match self {
            ComparisonOp::GreaterThan => "greater than",
            ComparisonOp::LessThan => "less than",
            ComparisonOp::AtLeast => "at least",
            ComparisonOp::AtMost => "at most",
            ComparisonOp::EqualTo => "equal to",
            ComparisonOp::Between => "between",
        }
    }
}

/// A quantity (`5 seconds`, `zero`) or a noun phrase standing for a value
/// (`the limit`). The number is kept as written; numeric evaluation is a
/// downstream concern.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Measure {
    Quantity {
        number: String,
        unit: Option<String>,
    },
    /// A bounded quantity (round 6): `at least 30 days`, `between 5 and 10
    /// seconds`. Admitted under `for` (Duration) ONLY — `within` already
    /// means an upper bound, so it keeps the plain quantity (legislated).
    /// Numbers and unit are kept as written; `upper` is the second number
    /// of `between <number> and <upper> [unit]` and the two bounds share
    /// the one unit.
    Bounded {
        op: ComparisonOp,
        number: String,
        unit: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        upper: Option<String>,
    },
    /// A noun phrase standing for a value (`the limit`). A STRUCT variant
    /// on the wire — `{ "kind": "np", "np": … }` — because [`NpGroup`] is
    /// itself internally tagged by `kind`: a newtype variant would flatten
    /// the payload into the same JSON object and emit a duplicate `kind`
    /// field, a document `serde_json` writes but refuses to read back.
    Np { np: Box<NpGroup> },
}

// ---- canonical rendering --------------------------------------------------------

impl Specification {
    pub fn render(&self) -> String {
        self.sentences
            .iter()
            .map(Sentence::render)
            .collect::<Vec<_>>()
            .join(" ")
    }
}

impl Sentence {
    /// Render the sentence in canonical form: frame keywords in title case,
    /// closed-class words lowercase, `If …, then …`, single spaces, trailing
    /// period. Open-class words keep their surface casing.
    pub fn render(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for scope in &self.frames.scopes {
            parts.push(format!("Where {},", scope.clause.render()));
        }
        for state in &self.frames.states {
            parts.push(format!("While {},", state.clause.render()));
        }
        if let Some(trigger) = &self.frames.trigger {
            match trigger.kind {
                TriggerKind::Event => parts.push(format!("When {},", trigger.clause.render())),
                TriggerKind::Contingency => {
                    parts.push(format!("If {}, then", trigger.clause.render()))
                }
            }
        }
        parts.push(self.core.render());
        if let Some(exception) = &self.exception {
            parts.push(format!(", unless {}", exception.render()));
        }
        if let Some(purpose) = &self.purpose {
            match purpose {
                Purpose::SoThat(clause) => parts.push(format!(", so that {}", clause.render())),
                Purpose::InOrderTo(vp) => parts.push(format!(", in order to {}", vp.render())),
            }
        }
        let mut joined = String::new();
        for part in parts {
            // Adjuncts begin with their comma and attach without a space.
            if !joined.is_empty() && !part.starts_with(',') {
                joined.push(' ');
            }
            joined.push_str(&part);
        }
        format!("{joined}.")
    }
}

impl Core {
    pub fn render(&self) -> String {
        match self {
            Core::Definition { term, definiens } => {
                format!("{} means {}", term.render(), definiens.render())
            }
            Core::Description {
                subject,
                copula,
                adverb,
                predicate,
                agent,
                roles,
            } => {
                let adverb = match adverb {
                    Some(DescriptionAdverb::Always) => " always",
                    Some(DescriptionAdverb::Never) => " never",
                    None => "",
                };
                let agent = match agent {
                    Some(agent) => format!(" by {}", agent.render()),
                    None => String::new(),
                };
                let mut out = format!(
                    "{} {}{adverb} {}{agent}",
                    subject.render(),
                    copula.as_str(),
                    predicate.render()
                );
                for role in roles {
                    out.push(' ');
                    out.push_str(&role.render());
                }
                out
            }
            Core::Deontic {
                subject,
                modal,
                negated,
                vp,
            } => {
                let not = if *negated { " not" } else { "" };
                format!(
                    "{} {}{not} {}",
                    subject.render(),
                    modal.as_str(),
                    vp.render()
                )
            }
        }
    }
}

impl Definiens {
    pub fn render(&self) -> String {
        match self {
            Definiens::Np { np, roles } => {
                let mut out = np.render();
                for role in roles {
                    out.push(' ');
                    out.push_str(&role.render());
                }
                out
            }
            // A clause definiens always renders with its `that` marker, so
            // the canonical form is unambiguous and re-parses to the same
            // tree even when the marker was omitted in the input.
            Definiens::Clause(clause) => format!("that {}", clause.render()),
        }
    }
}

impl Clause {
    pub fn render(&self) -> String {
        match &self.body {
            ClauseBody::Copular {
                copula,
                predicate,
                agent,
                roles,
            } => {
                let mut parts: Vec<String> = vec![
                    self.subject.render(),
                    copula.as_str().to_string(),
                    predicate.render(),
                ];
                if let Some(agent) = agent {
                    parts.push(format!("by {}", agent.render()));
                }
                for role in roles {
                    parts.push(role.render());
                }
                parts.join(" ")
            }
            ClauseBody::Verbal {
                verb,
                particle,
                manner,
                object,
                roles,
                content,
            } => {
                let mut parts: Vec<String> = vec![self.subject.render(), verb.clone()];
                if let Some(particle) = particle {
                    parts.push(particle.clone());
                }
                parts.extend(manner.iter().cloned());
                if let Some(object) = object {
                    parts.push(object.render());
                }
                for role in roles {
                    parts.push(role.render());
                }
                if let Some(content) = content {
                    parts.push(format!("that {}", content.render()));
                }
                parts.join(" ")
            }
        }
    }
}

impl NpGroup {
    pub fn render(&self) -> String {
        match self {
            NpGroup::Single(np) => np.render(),
            NpGroup::Coordinated {
                conj,
                marker,
                items,
            } => {
                let rendered: Vec<String> = items.iter().map(Np::render).collect();
                let joined = rendered.join(&format!(" {} ", conj.as_str()));
                match marker {
                    Some(GroupMarker::Both) => format!("both {joined}"),
                    Some(GroupMarker::Either) => format!("either {joined}"),
                    None => joined,
                }
            }
        }
    }

    /// Whether any top-level item is determined by `no`. Only the item's own
    /// determiner counts: a `no` inside an `of`-chain or a relative clause
    /// does not negate the phrase itself.
    pub fn has_no_item(&self) -> bool {
        let has_no = |np: &Np| np.det == Some(Det::No);
        match self {
            NpGroup::Single(np) => has_no(np),
            NpGroup::Coordinated { items, .. } => items.iter().any(has_no),
        }
    }

    /// The heads of the phrase — one for a single NP, one per coordinated item.
    pub fn heads(&self) -> Vec<&str> {
        match self {
            NpGroup::Single(np) => vec![np.head.as_str()],
            NpGroup::Coordinated { items, .. } => items.iter().map(|np| np.head.as_str()).collect(),
        }
    }
}

impl Np {
    pub fn render(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        if let Some(det) = &self.det {
            parts.push(det.render());
        }
        parts.extend(self.modifiers.iter().cloned());
        parts.push(self.head.clone());
        if let Some(of) = &self.of {
            parts.push(format!("of {}", of.render()));
        }
        if let Some(relative) = &self.relative {
            parts.push(relative.render());
        }
        parts.join(" ")
    }
}

impl Relative {
    pub fn render(&self) -> String {
        match &self.body {
            RelativeBody::Copular {
                copula,
                predicate,
                agent,
                roles,
            } => {
                let mut parts: Vec<String> = vec![
                    self.marker.as_str().to_string(),
                    copula.as_str().to_string(),
                    predicate.render(),
                ];
                if let Some(agent) = agent {
                    parts.push(format!("by {}", agent.render()));
                }
                for role in roles {
                    parts.push(role.render());
                }
                parts.join(" ")
            }
            RelativeBody::Verbal {
                verb,
                particle,
                manner,
                object,
                roles,
            } => {
                let mut parts: Vec<String> = vec![self.marker.as_str().to_string(), verb.clone()];
                if let Some(particle) = particle {
                    parts.push(particle.clone());
                }
                parts.extend(manner.iter().cloned());
                if let Some(object) = object {
                    parts.push(object.render());
                }
                for role in roles {
                    parts.push(role.render());
                }
                parts.join(" ")
            }
            RelativeBody::ObjectGap {
                subject,
                verb,
                particle,
                manner,
                roles,
            } => {
                let mut parts: Vec<String> = vec![
                    self.marker.as_str().to_string(),
                    subject.render(),
                    verb.clone(),
                ];
                if let Some(particle) = particle {
                    parts.push(particle.clone());
                }
                parts.extend(manner.iter().cloned());
                for role in roles {
                    parts.push(role.render());
                }
                parts.join(" ")
            }
        }
    }
}

impl Vp {
    pub fn render(&self) -> String {
        let mut parts: Vec<String> = vec![self.verb.clone()];
        if let Some(particle) = &self.particle {
            parts.push(particle.clone());
        }
        parts.extend(self.manner.iter().cloned());
        if let Some(object) = &self.object {
            parts.push(object.render());
        }
        if let Some(complement) = &self.complement {
            parts.push(complement.render());
        }
        for role in &self.roles {
            parts.push(role.render());
        }
        if let Some(content) = &self.content {
            parts.push(format!("that {}", content.render()));
        }
        parts.join(" ")
    }
}

impl RolePp {
    pub fn render(&self) -> String {
        match self {
            RolePp::Recipient(np) => format!("to {}", np.render()),
            RolePp::Means { marker, np } => format!("{} {}", marker.as_str(), np.render()),
            RolePp::Topic(np) => format!("about {}", np.render()),
            RolePp::Deadline(measure) => format!("within {}", measure.render()),
            RolePp::Duration(measure) => format!("for {}", measure.render()),
            RolePp::Rate { unit } => format!("per {unit}"),
            RolePp::Before(clause) => format!("before {}", clause.render()),
            RolePp::After(clause) => format!("after {}", clause.render()),
            RolePp::Until(clause) => format!("until {}", clause.render()),
            RolePp::Source(np) => format!("from {}", np.render()),
            RolePp::Goal(np) => format!("into {}", np.render()),
            RolePp::Location { preposition, np } => {
                format!("{preposition} {}", np.render())
            }
            RolePp::Agent(np) => format!("by {}", np.render()),
        }
    }
}

impl Predicate {
    pub fn render(&self) -> String {
        match self {
            Predicate::Comparison(comparison) => comparison.render(),
            Predicate::AbleTo { vp } => format!("able to {}", vp.render()),
            Predicate::Pp { preposition, np } => format!("{preposition} {}", np.render()),
            Predicate::Words { words } => words.join(" "),
        }
    }
}

impl Comparison {
    pub fn render(&self) -> String {
        match (&self.op, &self.upper) {
            (ComparisonOp::Between, Some(upper)) => {
                format!("between {} and {}", self.value.render(), upper.render())
            }
            (op, _) => format!("{} {}", op.render(), self.value.render()),
        }
    }
}

impl Measure {
    pub fn render(&self) -> String {
        let with_unit = |body: String, unit: &Option<String>| match unit {
            Some(unit) => format!("{body} {unit}"),
            None => body,
        };
        match self {
            Measure::Quantity { number, unit } => with_unit(number.clone(), unit),
            Measure::Bounded {
                op,
                number,
                unit,
                upper,
            } => match (op, upper) {
                (ComparisonOp::Between, Some(upper)) => {
                    with_unit(format!("between {number} and {upper}"), unit)
                }
                _ => with_unit(format!("{} {number}", op.render()), unit),
            },
            Measure::Np { np } => np.render(),
        }
    }
}
