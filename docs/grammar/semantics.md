# Semantics: the derived interpretations

> Part of the [grammar reference](./README.md).

The syntax layer — the [sentence layer](./sentences.md), the
[phrase grammar](./phrases.md), the [lexical rules](./lexical.md) — says what a
sentence *is*. This page documents
[`so_reason/src/semantics.rs`](../../so_reason/src/semantics.rs) and
[`so_reason/src/contract.rs`](../../so_reason/src/contract.rs): the first says
what a sentence *does* and the second forms semantic assume-guarantee contracts
over the formula interpretation. Apart from one pointer in the
[index](./README.md), this is the only page in the grammar reference where
assume-guarantee vocabulary appears; the syntax layer is definable without it,
and the other pages demonstrate that.

Everything here is a **derived view** over the parsed tree. The words remain
the source of truth. Every function on this page is total over parsed
sentences: the grammar has already rejected everything ambiguous, so
interpretation never fails and never guesses.

---

## Speech acts

```rust
pub fn speech_act(&Sentence) -> SpeechAct
```

The specification act a sentence performs, read off the pivot alone — the
grammar has already made it unambiguous:

| Speech-act core | `SpeechAct` |
| --- | --- |
| `<term> means <definiens>` | `Definition` |
| `<subject> is/are [always\|never] <predicate>` | `Description` |
| `<subject> shall/must <vp>` | `Obligation` |
| `<subject> shall/must not <vp>` | `Prohibition` |
| `<subject> should [not] <vp>` | `Recommendation` |
| `<subject> may <vp>` | `Permission` |

Two edges worth noting:

- A negated recommendation (`should not`) **stays a recommendation**; its
  negation lives in the assertion's polarity, not in the act.
- `may not` never reaches this function: the grammar rejects it as ambiguous
  (see [errors.md](./errors.md)); the canonical rewrite is `shall not`.

## Force

```rust
pub fn force(&Sentence) -> Option<Force>
```

How strongly a deontic sentence binds:

| Pivot | `force` |
| --- | --- |
| `shall`, `must` | `Some(Binding)` |
| `should` | `Some(Recommended)` |
| `may` | `None` |
| `is` / `are`, `means` | `None` |

Definitions, descriptions, and permissions carry no force. A permission is
deliberately forceless: it admits behavior rather than requiring it.

## Polarity

Whether a claim is asserted or denied. Negation sites are syntactically fixed —
`shall not` / `must not` / `should not` in a deontic core, `never` in a
description — so polarity is **read off the tree**, never scanned for in open
text. (`no` as a determiner is a third negation site; its scope is the noun
phrase it determines, and it stays inside the noun phrase.)

---

## The assertion

```rust
pub struct Assertion {
    pub scopes: Vec<Frame>,
    pub states: Vec<Frame>,
    pub trigger: Option<Trigger>,
    pub exception: Option<Clause>,
    pub subject: NpGroup,
    pub claim: Claim,
}
```

The assertion is the content of a behavioral (non-definition) sentence,
detached from surface word order: **the sentence's single property** — one
claim, about one subject, situated in its circumstances. The circumstance
frames are not separate propositions bolted onto the claim; they are the
**internal temporal structure** of that one property:

| Field | Source | Reading |
| --- | --- | --- |
| `scopes` | `Where …,` frames | configuration scope — in which build/plan/mode the claim applies |
| `states` | `While …,` frames | state scope — during which condition the claim applies |
| `trigger` | `When …,` / `If …, then` frame | the event (`When`) or contingency (`If`) that activates the claim |

Each frame (and the trigger) holds a **clause group** — one clause or several
coordinated under a single conjunction — carried into the assertion as-is:
`and` is a **joint guard** (all items hold together), `or` an **alternative
guard** (any one suffices). In a trigger, `and` reads as ONE event plus
states holding at its occurrence (the grammar rejects a second event
conjunct — conjunction of occurrences is simultaneity, which has no single
reading), while `or` reads as **alternative triggers** — either occurrence
fires the claim (disjunction of events is alternation, which is
well-defined). Either way it is still ONE frame; the group is the internal
structure of that frame's condition, not several frames.

| Field | Source | Reading |
| --- | --- | --- |
| `exception` | `, unless <clause>` | a carve-out from applicability — defeasibility structure, not a contradiction |
| `subject` | the core's subject noun phrase | who the claim is about |
| `claim` | the core after the pivot | what is claimed of the subject |

The purpose adjunct (`so that` / `in order to`) is **deliberately absent** from
the assertion: a purpose states intent, not behavior, so it does not constrain
what the assertion claims. It stays on the sentence (and is still scanned by
[`references`](#definite-references)).

### Claims

```rust
pub enum Claim {
    State      { polarity, copula, adverb, predicate, agent }, // description (agent: round 5)
    Action     { polarity, force, vp: VpGroup },               // obligation / prohibition / recommendation
    Admissible { vp: VpGroup },                                // permission
    Capability { polarity, vp: Vp },                           // `is [always|never] able to <vp>` (polarity: round 5)
}
```

Round 6: `Action` and `Admissible` hold the whole `VpGroup`, so an
`either <vp> or <vp>` deontic stays ONE claim; its disjunction surfaces in
the formula layer (an `Or` over per-alternative atoms) and in the
skeleton's per-alternative `atoms`. `Capability` keeps a single `Vp` —
alternatives are deontic-only in v0.2.

| Variant | From | Polarity | Force |
| --- | --- | --- | --- |
| `State` | `is/are [always\|never] <predicate> [by <agent>]` | `never` XOR subject `no`; `always` does not flip | none |
| `Action` | `shall/must/should [not] <vp>` | `not` XOR subject `no` | `Binding` for `shall`/`must`, `Recommended` for `should` |
| `Admissible` | `may <vp>` | none — `may not` and a `no` subject under `may` are both rejected by the grammar, so an admissibility cannot be negated | none |
| `Capability` | `is/are [always\|never] able to <vp>` | `never` XOR subject `no` (round 5 — the adverb is admitted before `able to` and composes; `No client is able to retry.` denies the capability) | none |

The claim's polarity is the **combined truth-functional polarity**: each
negation site flips it once, XOR-composed — the deontic `not` or description
`never` with a subject-level `no` (`No request shall be logged.` is a
`Negative` `Action`; `No request shall not be logged.` composes back to
`Affirmative`). The surface negation sites stay in the AST (`negated`, the
adverb, `Det::No`); the claim carries what the sentence asserts or denies.
Only the subject's own determiner participates — `no` in object position
scopes over that noun phrase, not over the claim. `always` strengthens a
description but does not change its polarity; the adverb is kept in the
claim as written (losslessness), alongside the derived polarity.

---

## Denotations

```rust
pub fn denote(&Sentence) -> Denotation
```

What a sentence denotes, by kind:

| `SpeechAct` | `Denotation` |
| --- | --- |
| `Definition` | `Vocabulary { scopes, term, definiens }` |
| `Description` | `Behavior(Assertion)` — a described invariant |
| `Obligation`, `Prohibition`, `Recommendation` | `Behavior(Assertion)` — required, forbidden, or recommended behavior |
| `Permission` | `Admissibility(Assertion)` |

**Vocabulary.** A definition establishes vocabulary, not behavior. Its
denotation carries only its `Where` scopes (the only frames the grammar admits
on a definition), the defined term (a single noun phrase — the grammar rejects
coordination in a term), and the definiens. Sentence-level exception and
purpose adjuncts do not enter a `Vocabulary` denotation.

**Behavior.** Descriptions, obligations, prohibitions, and recommendations all
denote a behavior assertion: something that is claimed to hold, or is required
/ forbidden / recommended to hold, of the subject in the stated circumstances.

**Admissibility.** A permission denotes admissibility, kept as a distinct
denotation rather than a weak behavior: `may` asserts that an action is
*admissible*, not that it happens. What a subject is permitted to do is
precisely what everything interacting with that subject must be prepared for —
which is why permissions feed the **environment side** of the assume-guarantee
reading below: when sentences are later paired at the graph level, an
admissibility is natural material for the *environment side* of some other
statement's contract — as **compatibility data** (an admissibility envelope:
the environment MAY do this, and the pairing must stay compatible with it),
never as an assumption conjunct that saturation would negate (round 6; see
[Typed pairing](#typed-pairing-paired-edgekind)) — and the denotation keeps it
separate so that stage can treat it that way.

---

## The assume-guarantee reading

Every behavioral statement — one that obliges, forbids, recommends, permits,
or describes — denotes one assertion: a single property of system behavior; a
definitional statement contributes vocabulary rather than behavior and stands
outside the contract reading. A statement's leading conditions — scope, state,
trigger — are the internal temporal structure of its assertion, not a contract
split. A contract is a *pairing*: a guarantee read under its assumptions, and
a statement taken alone is a guarantee under the trivial assumption. This is
the contract lens through which behavioral statements are related. It gives
refinement a precise meaning; composition is a foundation for later work, not
an operator the current assertion domain claims to implement.

### The role theory

*Assumption* and *guarantee* are not sentence categories. They are **roles an
assertion plays relative to a responsible subject**:

- A statement whose subject is the component under specification is a
  **guarantee** of that component's contract.
- A statement about the component's environment becomes an **assumption** only
  by being *paired* with a guarantee it enables.

A sentence's own circumstance frames are its assumption-side content in exactly
the sense above: they state what must hold of the environment for the claim to
bind. The ingest projection does not tear the sentence in two, though — the
frames travel *inside* the guaranteed assertion (the guarantee is the whole
conditioned claim, "in circumstance C, the subject does X"), and the contract's
separate assumption slot carries only what a sentence alone cannot supply: a
claim made by some *other* statement about the environment.

A sentence taken alone therefore forms a provisional guarantee under the
trivial assumption `⊤`. Non-trivial assumptions are pairings **between**
sentences. `so-reason::contract` defines their pure formation and semantic
value; `specd` selects, validates, and persists the graph relationships that
justify a formation.

### The ingest projection

```rust
pub enum Assumption { Top }                    // renders as "⊤"

pub struct IngestContract {
    pub assumption: Assumption,
    pub guarantee: Assertion,
    pub act: SpeechAct,
    pub force: Option<Force>,
}

pub fn ingest_contract(&Sentence) -> Option<IngestContract>
```

| Sentence kind | `ingest_contract` |
| --- | --- |
| Definition | `None` — vocabulary has no contract reading |
| Description, obligation, prohibition, recommendation | `Some`, guarantee = the behavior assertion |
| Permission | `None` — an admissibility admits rather than constrains |

Note that descriptions *do* project: a described invariant is a guarantee the
system makes about itself. Definitions and permissions stand outside the
lone-sentence contract reading — a definition because it is vocabulary, a
permission because its assertion **admits** behavior rather than constraining
it: as a lone sentence it has no `(⊤, G)` reading. Its denotation stays
`Admissibility`, and it enters a contract only through **pairing**, on the
environment (assumption) side of a guarantee it enables.

### Pairing semantics (the graph layer's contract)

A pairing compiles to a contract `(A, G)`: the assumption `A` is conjoined
from the paired **contract-forming** environment statements —
**EXPLICITLY RELIED, non-envelope, PROVEN, not merely RECOMMENDED, with
DISJOINT responsible subject keys** (a reliance on an occurrence or state,
or another component's dischargeable guarantee; round 9 — an UNPROVEN
source is a candidate edge that rides along without entering `A`; round
10 — a RECOMMENDED source and a SHARED-KEY source ride as candidates too:
recommendations never discharge AND never form `A`, and a textual subject
collision must be resolved with real component identity before the edge
forms; round 11 — a DEFAULT-RELIED source is a PERMANENT candidate:
contract forming requires the reliance to have been selected explicitly
through `for_guarantee_with_relied`), the guarantee `G` the enabled assertion. A paired *admissibility* is NOT part of
`A`: it rides along as compatibility data (round 6 — see
[Typed pairing](#typed-pairing-paired-edgekind)), because saturation must
never negate a permission. Contract equivalence and refinement are **not**
judged on the raw pair but on the *saturated* form `G ∪ ¬A` ("either the
guarantee holds or the assumption was violated"), per assume-guarantee
contract theory. The graph
layer must therefore implement that formula machinery — negation and
disjunction over assertions — **before** it introduces assumption edges; this
is a precondition, not an optimization. Well-formedness of a pairing: the
assumption-side statement may be ANY non-definition behavioral assertion
about the guarantee-side subject's *environment* — a statement whose
responsible subject is another component — never the guarantee-side
subject's own statement. That includes obligations and prohibitions whose
responsible subject is another component: relying on another component's
guarantee is exactly composition's assumption discharge. Polarity and force
govern whether a source can discharge an assumption: a permission
contributes admissibility — an envelope of tolerated environment behavior
that never asserts occurrence and never becomes an assumption conjunct
(round 6: it is compatibility data outside `A`, not material saturation
may negate); a
binding obligation or prohibition of the environment can discharge an
assumption outright; a description asserts how the environment stands; a
recommendation (`should`) NEVER hardens into an assumption — pairing one is
well-formed like any behavioral assertion, but it can never discharge the
assumption AND (API-encoded since round 10, `contract_forming`) it never
enters `A` either: recommended behavior cannot be relied on, only
expected, and conjoining a proven `should` into `A` would let saturation
`G ∨ ¬A` relieve the guarantee on a promise the environment never made.

**Graph edges select their reliance EXPLICITLY (round 10 doctrine,
API-ENCODED in round 11).** The default-relied constructors
(`for_guarantee`, `from_sentence`) set `relied` to the WHOLE source
conditional, which imports the source's own conditional shape into `A` —
the target ends up assuming "whenever the source's guard holds, its claim
holds" rather than the occurrence or state it actually awaits. That
default exists for migration and evidence collection ONLY: since round 11
it is marked `explicit_relied: false` and `contract_forming()` requires
the flag, so a default-relied source is a permanent candidate — visible
evidence that never enters `A`. A graph edge MUST be built with
`for_guarantee_with_relied`, passing the target's awaited assumption as
the explicit relied formula, so `A` trusts exactly what the guarantee
needs and the pairing validates that the source supports it.

**The well-formed proven pairing (round 11 — THE definition).** This
paragraph and the rustdoc on `FormedContract::well_formed` are the ONE
normative statement of pairing well-formedness; everything else
cross-links here. A paired contract is a **well-formed proven pairing**
when every assumption-side (non-envelope) source has:

1. an **explicit, non-`⊥` relied** formula (selected through
   `for_guarantee_with_relied`; `⊥` is rejected at construction as
   `vacuous_relied`);
2. a **proven** reliance — `relate::implies(source formula, relied)` at
   `Yes`;
3. an **environment-side** subject — RESPONSIBLE keys disjoint from the
   target's (`SubjectRelation::DisjointKeys`);
4. an **admissible act/force** — the act × kind matrix holds and the
   source is not merely recommended;

and, over the pairing as a whole, **assumption satisfiability is not
refuted** (`relate::assumption_satisfiable` is not `No`; `Unknown` is the
good case — satisfiability is never provable syntactically).
`FormedContract::well_formed()` summarizes the definition as DATA —
`{ all_contract_forming_explicit, all_proven,
all_sources_contract_forming, source_issues, assumption_satisfiability,
envelope_compatibility }`, the booleans quantified over the non-envelope
sources (vacuously true with none). **The aggregate is the one-call
verdict (round 12, change 2 — completing the round-11 summary, which
carried only conditions 1, 2, and 5):** `all_sources_contract_forming`
is `AssumptionSource::contract_forming()` — all four per-source
conditions at once — quantified over the assumption side, so a pairing
whose sources are explicit and proven but shared-key or merely
recommended now shows `false` there; the round-11 hazard in which the
two narrow booleans displayed `true` while nothing formed is retired.
`source_issues` itemizes why, per source index, with reasons
`not_explicit_relied` / `not_proven` / `shared_subject_keys` /
`recommended_force` — plus `envelope_kind` on envelope sources, recorded
for totality but BY-DESIGN (an envelope is compatibility data, never an
assumption conjunct, and never counts against the aggregate). The
individual booleans stay as diagnostics. The graph layer decides;
nothing in `so-reason` rejects or repairs a formed contract.

**Daemon realization.** The internal `EstablishOccurrenceReliance`,
`EstablishGuaranteeDischarge`, and `EstablishAdmissibilityEnvelope` Command
Handlers are the graph-side decision points; they are not exposed as RPCs
without concrete producer use cases. Their Edges store `source` (evidence),
`target` (the conditioned guarantee owner), and `relied_spec_id` (the authored
awaited assertion) as distinct fields. `specd` re-parses all three, uses
`for_guarantee_with_relied`, requires a `Yes` entailment rather than accepting
the language layer's candidate `Unknown`, requires every non-envelope source
to be contract-forming, assembles it with every current pairing into the same
target, and rejects `No` from either aggregate judgment. Only then does it
append the typed pairing Edge and a content-addressed paired Assumption
projection. The current view selects this `(A,G)` projection instead of the
ingest `(⊤,G)` projection; both remain immutable Ledger facts. Explicit command
input supplies the component/direction decision, while the responsible-subject
comparison remains a conservative guard: shared keys are rejected rather than
silently treated as distinct components.

**Verification doctrine (round 11, change 4).** `refines`/`assess` over a
paired contract whose formed assumption is REFUTED
(`assumption_satisfiable` = `No`) is VACUOUS — the saturated form
`G ∨ ¬A` is a tautology — and must not be reported as a proven relation:
`relate::refines` returns `Unknown` whenever either side's formed
assumption is refuted. `Unknown` satisfiability means downstream results
carry that caveat (not disproven, never certified).

**The ⊤-contract is PROVISIONAL.** When a pairing is selected for a
guarantee, the paired `(A, G)` **supersedes** the lone `(⊤, G)` — the two
are never conjoined. Conjoining them would keep `G` unconditional (the
`(⊤, G)` conjunct demands `G` in every environment) and defeat the point of
the assumption: a component is relieved exactly where its assumptions are
violated.

**Pairing edges are TYPED.** Three edge types, by what the assumption side
contributes:

- **occurrence/state reliance** — the guarantee relies on the assumed
  behavior actually happening (or the assumed state actually holding);
- **guarantee discharge** — another component's own guarantee (a binding
  obligation or prohibition of the environment) fulfills the assumption
  outright: composition's assumption discharge;
- **admissibility envelope** — a permission widens the tolerated
  environment behavior; it never asserts occurrence, so it can bound what
  the environment may do but cannot promise that it does.

The admissible assumption-side source kinds map onto these three types as
follows (since round 5 the mapping is validated per pairing, and it is not
a partition): an environment **obligation or prohibition** — a binding act
— may open a guarantee-discharge edge (binding acts are the only source
kinds that can discharge) or, when only the occurrence is relied on, an
occurrence/state-reliance edge; a **description** or **capability** opens
an occurrence/state-reliance edge — it asserts how the environment stands,
which is reliance on that state, not another component's binding promise;
a **recommendation** likewise opens an occurrence/state-reliance edge
that, per the rule above, can never discharge; a **permission** opens an
admissibility envelope and nothing else. The full act × kind matrix is
tabulated under [Typed pairing](#typed-pairing-paired-edgekind).

Since round 4 this doctrine is **API-encoded**, not prose-only: the three
edge types are `so_reason::contract::EdgeKind`, and
`FormedContract::paired(sources)` performs the supersession — it REPLACES
the provisional `⊤` assumption with the conjunction of the
**contract-forming** — non-envelope, proven (round 9), not merely
recommended, and `DisjointKeys` (round 10) —
source RELIED formulas (round 7: an edge is **evidence + reliance** — the
source sentence's formula is the evidence the edge rests on, and
`AssumptionSource::relied` is what the guarantee actually relies on; `A`
is built from the reliances. The default reliance is the whole source
formula, which reproduces the round-6 pairing exactly. Round 6: envelope
sources stay out of `A` and out of saturation), never conjoining the two
contracts (see [the formula layer](#typed-pairing-paired-edgekind)).
Selecting sources and validating them remains daemon/graph work.

**Two subject views (round 10).** `semantics::subject_keys` is the
GRAMMATICAL view — the surface subject position, which in a passive names
the PATIENT (`Each request shall be logged by the daemon.` keys on
`request`). `semantics::responsible_subject_keys` is the RESPONSIBLE view:
when the claim is passive — a deontic `be`-complement verb phrase or a
copular description — and an agent is stated (the dedicated slot or an
Agent role), the AGENT group's keys answer for the claim (`daemon` above);
otherwise the grammatical keys, unchanged (an agentless passive has no
better identity written). Both views are deliberate: the grammatical view
indexes what the sentence is ABOUT, the responsible view WHO ANSWERS for
it — and environment-vs-self questions (the pairing subject relation
below) are asked of the responsible view on both sides.

**Subject keys are CANDIDATE GENERATION ONLY.** `semantics::subject_keys(&Sentence)
-> Vec<String>` gives the grammatical subject(s) a normalized textual
identity key, joined by `.`, one key per coordinated item, empty for
definitions. Since round 5 keys CARRY MODIFIERS — `the backup daemon` →
`backup.daemon` must not collide with `the daemon` → `daemon`. Each
`of`-chain link contributes its lowercased modifiers (surface order), then
its lowercased head: `the owner of the file` → `owner.file`, `the owner of
the backup file` → `owner.backup.file`. Determiners and relative clauses
are still dropped. These keys exist to FIND candidate pairs, and for
nothing harder: a CONTRACT-FORMING pairing decision requires daemon-side
RESOLVED COMPONENT IDENTITY (aliases — `the daemon` / `specd`; two
components sharing a head word) and INTERFACE DIRECTION, neither of which
a textual key carries (unchanged roadmap, stated harder since round 7).
Round 10 aligns the API with this doctrine: the key comparison no longer
REJECTS anything — `for_guarantee` records it as
`AssumptionSource::subject_relation` (`SubjectRelation::DisjointKeys` /
`SharedKeys`, computed from the RESPONSIBLE keys on both sides), `so-reason`
reports and never decides. `SharedKeys` is a RED FLAG the graph must
resolve with component identity before forming the edge (conservatively,
only `DisjointKeys` sources are contract-forming — a shared-key source
rides as a candidate); `DisjointKeys` is NOT a proof of distinctness:
`the file` vs `the owner of the file` is a TEXTUAL disjointness, not a
semantic one — nothing about the key strings proves the two subjects are
different components, or the same one. Key equality must never be trusted
as identity, and key inequality never as difference.

**Capability.** `is [always|never] able to <vp>` denotes behavior the
subject can exhibit, free of deontic force: a description on the surface
(`SpeechAct::Description`, force `None`), a `Claim::Capability { polarity,
vp }` underneath. Since round 5 the description adverb is admitted before
`able to` and COMPOSES into the polarity through the shared XOR helper:
`is never able to` is a NEGATIVE capability, `No client is able to retry.`
denies it via the subject `no`, and `No client is never able to retry.`
composes back to affirmative (`always` strengthens without flipping,
exactly as in state claims). The skeleton digests the capability's verb
phrase (words, objects, roles, manner), the formula layer emits an
ordinary Behavior atom — a capability claim is a descriptive behavior
property, not an admissibility — and, like every description, it ingests
as `(⊤, G)`.

Worked example — `The pump shall stop.`:

| Field | Value |
| --- | --- |
| `assumption` | `Top`, rendered `⊤` |
| `guarantee` | assertion: subject `the pump`, claim `Action { Affirmative, Binding, stop }`, no frames |
| `act` | `Obligation` |
| `force` | `Some(Binding)` |

---

## The logical skeleton

```rust
pub fn skeleton(&Sentence) -> Option<Skeleton>

pub struct Skeleton {
    pub subject: SubjectSkeleton,   // quantifier + restrictor + head + full
    pub polarity: Polarity,         // the COMBINED polarity of the claim
    pub atoms: Vec<Atom>,           // behavior kernels: 1, or 1 per `either…or…` alternative (round 6)
    pub force: Option<Force>,
    pub act: SpeechAct,
    pub guards: Guards,             // digests of the circumstance frames
    pub exception: Option<ClauseSkeleton>, // digest of the `unless` carve-out
}
```

Round 6 RESHAPE: the lone `atom` field became `atoms: Vec<Atom>` — exactly
one for every claim except an `either … or …` deontic, which carries one
atom per alternative in surface order. The index must see every
alternative, and a lone field would either hide them or duplicate the
first, so there is no legacy alias.

A derived normalization of a behavioral sentence, so contradiction detection
can see through surface differences: `No request is logged.` and `Each
request shall be logged.` yield the same atom (`["logged"]`, over head
`request`) with opposite polarity and `Negative` vs `Universal` quantifiers.
`None` for definitions, and for coordinated subjects (no single
quantifier-restrictor-head normal form in v0.2 — the skeleton stays
single-subject; the [formula layer](#the-formula-layer) digests a
coordinated subject one item at a time, so coordinated sentences are
formula-bearing even though they have no skeleton). **Data only**: `so-reason`
provides the skeleton; it is the INDEX for future edge generation — rich
enough that candidate pairs can be found and told apart — not the decision
procedure. Generating conflict edges over it is graph work.

- **Quantifier** — from a determiner, and — since round 5 — from POSITION:
  a behavioral SUBJECT reads generically, an object or role phrase does
  not. The full mapping:

  | Determiner | Subject position (behavioral) | Object / role position |
  | --- | --- | --- |
  | `each` / `every` / `all` / `any` | `Universal` | `Universal` |
  | `a` / `an` | `Universal` (**generic reading, legislated round 5**) | `Existential` |
  | *bare* (incl. bare plural) | `Universal` (**generic reading, legislated round 5**) | `None` |
  | `the` | `Definite` | `Definite` |
  | `no` | `Negative` | `Negative` |
  | `at least` / `at most` / `exactly n` | `Count { op, n }` | `Count { op, n }` |

  `any` is legislated universal since round 3 (requirements English reads
  `any request …` as `every request …`, not as an existential witness);
  round 5 extends the same requirements-English convention to generic
  subjects: `A request shall be logged.`, `Requests are logged.`, and
  `Each request shall be logged.` all quantify universally over requests
  and now MEET at `Universal` instead of under-detecting conflicts. Object
  and role positions are untouched: `shall create a session` is one
  session per occasion. Definition terms are unaffected (definitions have
  no skeleton). A subject `Det::No` contributes BOTH the `Negative`
  quantifier and a polarity flip; an object `no` contributes only the
  quantifier (claim polarity is subject-ruled — settled in round 2).
- **Polarity** — the combined polarity of the claim: each negation site flips
  it once, composed by XOR — deontic `not` XOR description `never` XOR
  subject `no`. Two flips cancel: `No request shall not be logged.` is
  `Affirmative`.
- **Atom** — surface words, lowercased, with **no lemmatization** (`logged`
  matches `logged`, never `log`). For action claims: the verb plus its
  particle when present (`time out` and `time` are different behaviors) —
  or, when the verb is `be`, the complement predicate words, so `shall be
  logged` and `is logged` meet — plus `manner`, `objects`, and `roles`.
  Since round 4 the atom carries a **`manner`** field (the verb phrase's
  manner adverbs, lowercased, in surface order): `words` does **not**
  absorb manner, so `stop` and `stop immediately` share their verb kernel
  and differ exactly in `manner` (empty for state claims). Skeleton v3:
  `objects` is `Vec<ObjectSkeleton { quantifier, head, full }>`, one entry
  per coordinated item, so `log no request` and `log the request` differ
  exactly in the object's quantifier. Round 6: every subject and
  object/role digest carries **`full`** — the lowercased render of
  modifiers + head + `of`-chain + relative, with the phrase's own
  top-level determiner excluded (nested determiners kept as written,
  legislated) — the full-fidelity identity that keeps `the owner of the
  file` and `the owner of the bucket`, or `request that is authenticated`
  and `request that is unauthenticated`, from colliding. Role digests are
  `RoleSkeleton { kind, value, marker }` — `marker` (round 9) is the
  role's lowercased surface preposition when the preposition itself
  disambiguates within one kind: a Location role carries it (`in` vs
  `on the archive` are different propositions now, retiring the round-2
  heads-only collision), every other kind keeps `None` (their kind
  already fixes the marker), and serde skips an absent marker so
  pre-round-9 digests load unchanged. Role values are
  `Heads { items: Vec<ObjectSkeleton> }` (quantifier + lowercased head +
  full per item), a `Measure` with number and unit kept as written — so
  `within 5 seconds` and `within 10 seconds` differ exactly in their
  Deadline role, with comparability downstream — a `BoundedMeasure`
  (round 6: `for at least 30 days` keeps its operator, numbers, and unit
  structurally) — or, for `before`/`after`/`until`, a `Clause` value that
  since round 8 carries the WHOLE nested `ClauseSkeleton` (polarity,
  manner, roles, comparison) plus `full`, the lowercased render of the
  nested clause — superseding the round-3 flat `{subject_head, words}`
  digest under which `before no user logs out` and `before the user logs
  out` digested alike. The `full` string is the nested clause's lossiness
  anchor, exactly as `ContentSkeleton.full` anchors content complements
  (round 11: a nested verbal body's object digests enter the skeleton
  too, but the digest stays coarser than the words, so the anchor keeps
  its job). A
  comparison predicate additionally digests STRUCTURALLY
  (round 6): the atom (and a copular `ClauseSkeleton`) carries
  `comparison: Option<ComparisonSkeleton>` — operator, number lexeme,
  unit, and `between`'s upper bound (or an Np-measure's full string) —
  alongside the rendered words, which stay for index compatibility. Roles
  keep `store … in the archive` and `store … on the public bucket` from
  colliding — and, since round 9, `store … in the archive` and `store …
  on the archive` too (the marker is identity). For state claims: the predicate words, with no objects and —
  since round 5 — the passive agent (when stated) as the first role, under
  `RoleKind::Agent`, followed (round 8 follow-up) by the structured role
  tail written after the agent, so `is logged by the daemon` and `shall be
  logged by the daemon` digest to the same atom — and `is logged by the
  daemon within 5 seconds` meets `shall be logged by the daemon within 5
  seconds` too, the Deadline structured in both. Without an agent a
  description keeps the plain predicate reading (its tail stays predicate
  words). Copular guard clauses digest their
  agent the same way. Round 7: a content complement (`ensure that the
  token is valid`) digests as `content: Option<ContentSkeleton>` — the
  clause's `ClauseSkeleton` PLUS `full`, the lowercased render of the
  whole clause. The `full` string is the content's own full-identity
  under the lossiness rule: since round 11 `ClauseSkeleton` carries a
  verbal body's object digests, so `ensure that the reading exceeds the
  limit` and `… the threshold` separate in the digest too, but the digest
  stays coarser than the words (role-phrase modifiers, the object group's
  conjunction) and `full` remains the anchor — the relation engine treats
  content as identity and answers `Unknown`
  across differing contents, never `Yes`. Round 7 also widens relative
  bodies to the full verbal tail, and the tail participates in every
  `full` identity string (a relative's roles restrict the phrase they
  are written in).
- **Guards and exception** — digests of the frames and the `unless`
  carve-out. Each clause digests to
  `ClauseSkeleton { subject_head, polarity, words, manner, objects, roles,
  comparison, content }`
  (lowercased
  heads; `Some(Negative)` when the clause subject carries `no`; the verb
  plus particle or the predicate words; since round 4 the clause's own
  `manner` adverbs, lowercased and NOT absorbed into `words` — empty for
  non-capability copular bodies (a capability guard's manner comes from
  its verb phrase, below); and — since round 3 — the digests
  of the clause's own thematic-role phrases, so a sequence trigger's
  `after` clause shows up in the guard digest). Round 8 (superseding the
  round-3 restriction of roles to verbal bodies): COPULAR clause bodies
  carry a thematic-role tail too, so `While the pump is active at the
  depot,` digests predicate words `["active"]` plus a structured Location
  role — the agent (when stated) digests first, under `RoleKind::Agent`,
  then the tail's roles in surface order. Round 11 (change 2, retiring
  the drop-the-object blind spot): a VERBAL body's `objects` slot carries
  one `ObjectSkeleton` per coordinated item, so `When the queue holds no
  message,` and `… holds the message,` no longer share a guard skeleton —
  the INDEX now separates what the guard-atom anchors always did (the
  object GROUP's `and`/`or` conjunction is the legislated residual: it
  stays out of the digest, anchored only). Plain copular bodies keep
  `objects` empty (a predicate has no object). A copular capability guard
  (`while the client is able to retry within 5 seconds` — round 8,
  change 5) digests STRUCTURALLY: words `["able", "to", <verb>
  (<particle>)]`, with the capability verb phrase's manner and roles in
  their own slots, so capability descriptions and capability guards
  carry the same structured pieces. Round 12 (change 6, retiring the
  capability object drop — the blind spot the round-8 pin documented):
  a capability body's `objects` slot carries its verb phrase's object
  digests too, so `while the client is able to hold the lock` and
  `while the client is able to hold the token` no longer share a guard
  skeleton — the index agrees with what the guard ATOM's source render
  always anchored, and `guards_witness_overlap` keeps refusing across
  differing capability objects exactly as before (the anchor difference
  was already load-bearing; now the digest difference is too). Round 9: a VERBAL clause
  body's content complement digests as `content:
  Option<Box<ContentSkeleton>>` — the nested clause's digest plus its
  full render, the same lossiness-anchor discipline as everywhere else —
  so `when the monitor ensures that the token is valid,` and `… that the
  token is expired,` never share a guard digest, and the relation
  engine's guard identity extends through content. `Where`/`While` clauses are
  flattened per family; the trigger keeps its kind and conjunction
  (`TriggerSkeleton { kind, conj, clauses }`).

---

## The formula layer

```rust
// so_reason::formula
pub fn applicability(&Sentence) -> Formula
pub fn claim_formula(&Sentence) -> Option<Formula>

pub enum Formula {
    Atom { atom: AtomRef },      // one opaque atom
    And { items: Vec<Formula> }, // n-ary, mirroring the surface structure
    Or { items: Vec<Formula> },
    Not { inner: Box<Formula> },
    Top,                         // the empty conjunction
    Bottom,
}
pub enum AtomRef {
    Guard { clause: ClauseSkeleton, source: String, role: GuardRole }, // an applicability atom
    Behavior { behavior: BehaviorAtom },              // the claim atom
    Admissibility { behavior: BehaviorAtom },         // a permission's claim atom
}
pub enum GuardRole { Scope, State, Trigger { kind: TriggerKind }, Exception } // round 10
pub struct BehaviorAtom { subject, atom, force, act, source } // skeleton-level digests + lossless anchor
impl BehaviorAtom {
    pub fn proposition(&self) -> Proposition // the LOGICAL key (round 5)
}
pub struct Proposition { subject: SubjectSkeleton, atom: Atom } // no act/force/anchor
```

The formula layer supplies the assertion domain. It does not own contracts:
`contract_formula` remains re-exported here only as a compatibility path for
older callers.

## The contract layer

```rust
// so_reason::contract
pub enum Assertion {
    Atom { atom: ContractAtom },
    And { items: Vec<Assertion> },
    Or { items: Vec<Assertion> },
    Not { inner: Box<Assertion> }, // classical Boolean complement
    Top,
    Bottom,
}
pub struct Contract {
    assumption: Assertion,
    guarantee: Assertion,
}
impl Contract {
    pub fn saturated_guarantee(&self) -> Assertion // G ∨ ¬A
    pub fn saturate(&self) -> Contract           // (A, G ∨ ¬A)
    pub fn satisfied_by(&self, implementation: &Assertion) -> bool
    pub fn refines(&self, abstract_: &Contract) -> bool
    pub fn compose(&self, other: &Contract) -> Contract
    pub fn quotient(&self, divisor: &Contract) -> Contract
    pub fn merge(&self, other: &Contract) -> Contract
    pub fn interface(&self) -> ContractInterface
}

pub struct FormedContract {
    assumption: Formula,             // conjunction of the CONTRACT-FORMING sources' RELIED formulas (rounds 7/9/10)
    guarantee: Formula,
    sources: Vec<AssumptionSource>,  // formation provenance; not Contract identity
}
impl FormedContract {
    pub fn semantic(&self) -> Contract
    pub fn saturated(&self) -> Formula // source-formula spelling, not algebraic complement
    pub fn paired(&self, sources: &[AssumptionSource]) -> FormedContract  // {A₁…Aₗ} ⇒ G
}
pub type ContractFormula = FormedContract // compatibility name
pub fn formed_contract(&Sentence) -> Option<FormedContract>

pub enum EdgeKind { OccurrenceReliance, GuaranteeDischarge, AdmissibilityEnvelope }
pub struct AssumptionSource {
    pub kind: EdgeKind,
    pub formula: Formula,     // the EVIDENCE: what the source sentence claims
    pub relied: Formula,      // the RELIANCE: what the guarantee actually trusts (round 7)
    pub act: SpeechAct,       // validated provenance (round 5)
    pub force: Option<Force>,
    pub proven: bool,         // implies(formula, relied) == Yes at construction (round 8)
    pub subject_relation: SubjectRelation, // responsible-key comparison vs the target (round 10)
}
pub enum SubjectRelation { DisjointKeys, SharedKeys } // reported, never decided (round 10)
impl AssumptionSource {
    pub fn contract_forming(&self) -> bool // non-envelope, proven (round 9), not recommended, DisjointKeys (round 10)
}
impl AssumptionSource {
    // The preferred target-aware entry point (round 6; observational
    // since round 10): act × kind matrix PLUS the responsible-subject
    // relation, RECORDED as `subject_relation` (the round-6 SameSubject
    // rejection is removed); `relied` defaults to the source formula —
    // migration/tests only: graph edges use `for_guarantee_with_relied`.
    pub fn for_guarantee(EdgeKind, source: &Sentence, target: &Sentence)
        -> Result<AssumptionSource, PairingError>
    // Explicit reliance (round 7): additionally rejects a `relied` the
    // source formula PROVABLY fails to entail (`implies` = No); Unknown is
    // accepted (documented conservatism).
    pub fn for_guarantee_with_relied(EdgeKind, source: &Sentence, target: &Sentence, relied: Formula)
        -> Result<AssumptionSource, PairingError>
    // Advisory: does this source's formula entail what an assumption awaits?
    pub fn advisory_reliance_check(&self, relied: &Formula) -> Ternary
    // #[doc(hidden)], superseded as the entry point (round 6): act × kind
    // matrix only, for callers with no target sentence in hand.
    pub fn from_sentence(EdgeKind, &Sentence) -> Result<AssumptionSource, PairingError>
}
```

`Contract` is the semantic A/G pair. `FormedContract` separately records how
its assumption was selected from authored assertions. An implementation
assertion `M` satisfies `Contract(A,G)` exactly when `M ∧ A ⇒ G`, equivalently
when `M ⇒ G ∨ ¬A`. `Formula` itself is not used as this Boolean algebra:
`Formula::Not` immediately around a behavior atom is predicate denial inside
the subject quantifier (`∀x.¬P(x)`), not generally the classical complement
`¬∀x.P(x)`. Projection therefore turns positive and denied behavior predicates
into distinct signed `ContractAtom`s and reserves `Assertion::Not` for the
classical complement required by saturation and contract operations.

`ContractInterface` is the deterministic behavior alphabet (the generators
mentioned by `A` or `G`). Composition uses the union alphabet; it does not
invent input/output directions or component ownership that the constrained
language has not stated. Contract operations and graph materialization remain
outside the constrained-language grammar.

The **structural precondition for graph edges** (round 3): before edges can
be sound, every behavioral sentence needs a propositional shape — which
guard atoms scope it, how they conjoin and disjoin, where the exception
negates, what the claim atom is. This module provides exactly that shape
and deliberately nothing more at the formula level. Since round 5 a
**minimal relation engine** ([below](#the-relation-engine)) computes
conservative `implies`/`contradicts`/`refines` judgments over these
formulas; SMT grounding of the atoms and NL entailment remain future
strengthenings. Raw text stays authoritative; formulas are derived views.

- `applicability` — scopes ∧ states ∧ trigger ∧ ¬exception, each frame's
  clause group keeping its own `and`/`or` structure (an `or` trigger group
  stays an `Or` inside the conjunction). An ubiquitous sentence is `Top`.
  Round 10: each guard atom carries the FRAME ROLE it guards under
  (`GuardRole` — `Scope` for `Where`, `State` for `While`,
  `Trigger { kind }` for `When`/`If`, `Exception` for `unless`), so the
  flattening no longer erases which circumstance family a clause was
  written in; the role is part of guard-atom identity (equality,
  canonical sort key, overlap witnessing).
- `claim_formula` — the behavior (or admissibility) atom, wrapped in `Not`
  when its polarity is negative (polarity is formula structure, not atom
  content). A permission's claim is an `AtomRef::Admissibility` atom — a
  distinct arm, not a `Behavior` atom distinguished only by `act`. **A
  coordinated subject is formula-bearing since round 4**: it yields one
  atom per item (same behavior kernel, per-item subject digest and anchor),
  combined by the subject's own conjunction (`and`/`both` → `And`,
  `or`/`either` → `Or`; the group marker does not change the logic), and
  negation composes **per item** — the claim-level site (`not`/`never`)
  XORs with each item's *own* `no` determiner, so
  `The pump and the valve shall not run.` is `¬run(pump) ∧ ¬run(valve)`
  and `No pump and the valve shall run.` is `¬run(pump) ∧ run(valve)` — a
  sibling item's `no` never leaks onto a plain item. `None` only for
  definitions: vocabulary has no claim.
- `formed_contract` — the provisional contract formed from one sentence:
  `assumption = Top` at ingest (non-trivial assumptions arrive only by
  pairing, and the paired `(A, G)` then supersedes this lone form), and
  `guarantee = applicability → claim`, i.e.
  `Or(Not(applicability), claim)`, with `Top` applicability simplified
  away. `None` for definitions AND permissions — a permission has no lone
  contract (settled above). Coordinated subjects ARE contract-bearing
  since round 4: the guarantee's claim is the coordination's `And`/`Or`
  over per-item atoms. `saturated()` gives the theory's `G ∪ ¬A`
  symbolically; with the ingest assumption `Top` it is the guarantee
  itself.

### Index vs logic: the `no`-subject normalization

The skeleton is the surface INDEX: it records what was written, so a `no`
subject keeps the `Negative` quantifier there. The formula layer is
normalized LOGIC: a subject `no` quantifies universally over a denied
predicate (`no X: P` ≡ `¬∃X P` ≡ `∀X ¬P`), so a behavior atom built from a
`no` subject carries `Quantifier::Universal`, and the negation is carried
**exactly once**, by the formula's `Not` wrapper. The two views
intentionally differ on `no`. `No daemon shall sleep.` →
`Not(atom{daemon, Universal})`; `No request shall not be logged.` → the
two flips cancel and the atom is un-negated (`atom{request, Universal}`),
first-order equal to `Each request shall be logged.` on the normalized
subject digest, kernel, and force. What intentionally still differs
between two such logically equal atoms is the surface residue: the speech
act (read off the pivot: `Prohibition` vs `Obligation`) and the lossless
`source` anchor — so full `BehaviorAtom` equality is *stricter* than
logical equivalence, and downstream equality/entailment must project out
`act` and `source` (or normalize further) when it wants the logical
reading.

**Quantifier scope convention.** A behavior atom is not a closed
proposition: its subject quantifier always **out-scopes** the atom's own
`Not` wrapper. The `Not` is claim-level (predicate) negation — per-individual
denial — so `Not(atom{subject: ∀X, P})` reads `∀X ¬P(X)`, never `¬∀X P(X)`.
This is uniform, not special to `no`: `Each daemon shall not sleep.` also
yields `Not(atom{daemon, Universal})` meaning every daemon refrains. A
solver grounding these atoms in first-order form must apply the negation
inside the subject quantifier.

### Anchors

Every atom carries a lossless `source` anchor: the canonical render of the
material it was derived from — the clause render for guard atoms; the core
render with this item as sole subject (no frames, no exception, no
purpose) for behavior and admissibility atoms. The anchor keeps the
**surface negation sites** (`not`, subject `no`), so it carries strictly
more than the digest fields: the negation the formula expresses through
the `Not` wrapper and the `Universal` normalization is still visible in
the anchor text. The safe consumption rule is **re-derivation, not
substitution**: re-parse the anchor and take *its* `claim_formula` — that
reproduces exactly the atom's enclosing sub-formula (the atom with its own
`Not` wrapper), never the bare atom. Anchors are not atom-identity keys:
logically equivalent sentences keep distinct anchors. The digests stay for
indexing but are lossy; equality/entailment must compare formulas
re-derived from anchors (or the ASTs), never digests or anchor strings
alone.

### Typed pairing (`paired`, `EdgeKind`)

The supersession doctrine of [Pairing semantics](#pairing-semantics-the-graph-layers-contract)
is **API-encoded** since round 4. `FormedContract::paired(sources)`
returns a NEW contract whose assumption is the conjunction of the
**contract-forming** source RELIED formulas — non-envelope AND proven
(round 9) AND not merely recommended AND `DisjointKeys` (round 10) AND
explicitly relied (round 11; `AssumptionSource::contract_forming`, defined
once under [the well-formed proven pairing](#pairing-semantics-the-graph-layers-contract)) — a single one stands
alone; none — envelope-only or candidate-only pairing included — and
empty sources keep `Top`, **replacing** the provisional ingest assumption — the paired `(A, G)`
supersedes the lone `(⊤, G)`; the two are never conjoined. The guarantee
is untouched, and `saturated()` over the result gives `G ∨ ¬(∧ᵢAᵢ)`. Each
source is typed by `EdgeKind`: `OccurrenceReliance` (occurrence/state
reliance), `GuaranteeDischarge` — the **only** kind that can discharge an
assumption — and `AdmissibilityEnvelope`, which only *widens* the
tolerated environment behavior and never witnesses occurrence.

**Envelopes are not assumption conjuncts (round 6, correcting the round-5
shape).** A permission is compatibility data — *the environment MAY do
this, and the pairing must stay compatible with it* — not a behavior-set
whose complement means anything. Conjoining it into A and then saturating
(`G ∨ ¬A`) would NEGATE the permission, reading it as a behavior-set
complement it never was. Envelope sources are therefore retained in
`FormedContract::sources` (compatibility checking needs them) but never
enter the assumption formula and are never negated by saturation; their
formal denotation (widening A) is graph-layer future work. Since round 8
a retained envelope is no longer check-free: the graph layer must run
`relate::envelope_compatible` over every paired contract that retains
one — a guarantee that forbids exactly what its own envelope admits is a
proven incompatibility (`No`), and anything else is `Unknown`, never a
certified compatibility. (Round 10 closes the round-8 reachability gap:
with the same-subject rejection removed, a same-subject envelope can
arrive through the validated `for_guarantee` constructor — recorded as
`SharedKeys` — so the `No` arm is reachable through every construction
path and is now the formal guard the rejection used to approximate.)

**Validation is API-encoded since round 5, target-aware since round 6,
observational since round 10.**
`AssumptionSource::for_guarantee(kind, source, target)` is the entry
point: it builds a source WITH its provenance (`act`, `force`), enforces
the act × kind matrix below, and OBSERVES the source-vs-target subject
relation — the RESPONSIBLE subject keys
(`semantics::responsible_subject_keys`, round 10: a passive's stated
agent, not its patient, on both sides) are compared and the result
recorded as `subject_relation` (`DisjointKeys`/`SharedKeys`). The round-6
hard rejection (`PairingError::SameSubject`, `same_subject`) is REMOVED:
a shared key is a red flag, not a proof of self-reliance, so the source
constructs and rides as a candidate — `contract_forming` keeps `A` safe
by requiring `DisjointKeys`. A definition on either side is
`NotBehavioral`. The older `from_sentence(kind, sentence)` remains
(hidden from docs, not deprecated — documented choice) for callers with
no target in hand; it applies the matrix only and sets the LEGISLATED
`DisjointKeys` default (no target to compare against — the same reading
the serde default gives a stored pre-round-10 edge):

| Source act | `OccurrenceReliance` | `GuaranteeDischarge` | `AdmissibilityEnvelope` |
| --- | --- | --- | --- |
| Obligation / Prohibition (binding) | ✓ | ✓ | ✗ `BindingNoEnvelope` |
| Description (capability included) | ✓ (state reliance) | ✗ `DescriptionOnlyReliance` | ✗ `DescriptionOnlyReliance` |
| Recommendation | ✓ | ✗ `RecommendationOnlyReliance` | ✗ `RecommendationOnlyReliance` |
| Permission | ✗ `PermissionOnlyEnvelope` | ✗ `PermissionOnlyEnvelope` | ✓ |
| Definition | ✗ `NotBehavioral` | ✗ `NotBehavioral` | ✗ `NotBehavioral` |

**The edge carries its reliance (round 7).** `AssumptionSource.relied` is
the formula the target guarantee actually relies on — the edge is
evidence (`formula`, what the source sentence claims) + reliance
(`relied`, what the pairing trusts), and `paired` conjoins the RELIED
formulas into `A` (the contract-forming ones only: non-envelope, proven
— round 9 — not merely recommended and `DisjointKeys` — round 10). Both existing constructors default `relied` to the
source formula (documented default; since round 11 a defaulted reliance
is `explicit_relied: false` — migration/evidence only, permanently
candidate), and pre-round-7 serialized sources deserialize to that
default.
`AssumptionSource::for_guarantee_with_relied(kind, source, target,
relied)` sets it explicitly — round 11: it is also the ONLY constructor
that sets `explicit_relied: true`, without which a source never forms `A`
— and additionally validates that the evidence
supports the reliance: `relate::implies(source formula, relied)` must not
be `No` (`No` → `PairingError::SourceDoesNotSupportRelied`,
`source_does_not_support_relied`); `Unknown` is ACCEPTED by this pure
constructor — conservative,
documented: the structural rules often cannot prove an entailment that
holds, and full entailment validation of a pairing remains daemon/graph
work. The topology-producing daemon pairing path is stricter: it requires
the recorded `proven` flag (`Yes`), so `Unknown` never becomes a Ledger
Edge.

**Vacuous reliances are rejected (round 8, superseding the round-7
accept-Bottom pin).** A relied formula that is — or simplifies to — `⊥`
is `PairingError::VacuousRelied` (`vacuous_relied`): with `A = ⊥` the
saturated form `G ∨ ¬A` is a tautology, so the guarantee is erased
rather than conditioned. The erasure is provable from the shape alone,
so accepting it under the Unknown-is-accepted conservatism was never
conservative. (`relied: Top` — relying on nothing — remains expressible
and pairs to an unchanged `⊤` assumption.)

**The edge records whether its reliance is PROVEN (round 8).**
`AssumptionSource.proven` is `true` iff `relate::implies(formula,
relied)` answered `Yes` at construction (`Unknown` builds with `false`).
DOCTRINE — ENFORCED since round 9 (round 8 stated it, round 9 encodes
it): only proven reliances become contract-forming edges. `paired`
conjoins exactly the sources for which `contract_forming()` holds
(explicitly relied — round 11 — non-envelope, proven, not merely
recommended, `DisjointKeys`); an
unproven source is a CANDIDATE the graph
layer must confirm (re-derive at `Yes`) or discard — it is RETAINED in
`sources`, visibly unproven, but leaves the assumption unchanged, so a
candidate edge never relieves the guarantee of anything (`G ∨ ¬A` is
built only from confirmed trust). The default-relied
constructors set the flag `true` (relying on the whole source formula is
self-entailment); pre-round-8 serialized sources deserialize to `false`
(documented: an old edge loads as unproven until re-derived, never
silently promoted — and, since round 9, a loaded-unproven edge also
stays out of any newly derived assumption until re-derived).

**Two judgments guard the assembled pair (round 8; one-call summary
since round 11, COMPLETED round 12).** Individually valid
sources can still conjoin badly, so `relate` offers two checks the graph
layer must run on every paired contract — and `specd` does so before append —
`FormedContract::well_formed()` runs both and folds in the source-side
gates: the `all_sources_contract_forming` aggregate (round 12 — the
one-call verdict over all four per-source conditions), its per-source
`source_issues` itemization, and the two narrower
explicitness/provenness booleans as diagnostics, so one call carries the
whole verification status (data only; see [the well-formed proven
pairing](#pairing-semantics-the-graph-layers-contract)):
`relate::assumption_satisfiable(&FormedContract)` — can the conjoined
contract-forming reliances all hold at once (round 9: the judged set is
exactly the set `paired` conjoins, so the verdict is about the assumption
actually formed)? — and
`relate::envelope_compatible(&FormedContract)` — does the guarantee
forbid exactly what a retained envelope admits? Both follow the
never-`Yes` asymmetry doctrine described under
[the relation engine](#the-relation-engine).

The source formula is the sentence's own conditional (applicability →
claim — the same shape a guarantee takes), and `paired` now RETAINS its
sources on the contract (`FormedContract::sources`), keeping the derived
`assumption` conjunction and each conjunct's edge kind in sync — a
permission can no longer be quietly treated as occurrence evidence, nor a
recommendation as a discharge. `PairingError` carries actionable messages
and `kind()` names for telemetry. Selecting WHICH sentences pair remains
daemon/graph work: subject keys are still the TENTATIVE textual identity,
so the recorded `subject_relation` reports only the textually
self-evident; alias resolution and component identity remain daemon-side,
per the [subject-keys caveat](#pairing-semantics-the-graph-layers-contract).
Full interface-direction/entailment validation of a pairing is likewise
daemon/graph work, but the language layer OFFERS the conservative piece:
`AssumptionSource::advisory_reliance_check(&self, relied) -> Ternary` is
`relate::implies(source formula, relied)` — advisory only, `Yes` by
structural proof, `Unknown` never to be read as `No`, and no substitute
for the constructors' validity checks.

### The relation engine

```rust
// so_reason::relate
pub enum Ternary { Yes, No, Unknown }
pub fn implies(a: &Formula, b: &Formula) -> Ternary
pub fn contradicts(a: &Formula, b: &Formula) -> Ternary
pub fn refines(concrete: &FormedContract, abstract_: &FormedContract) -> Ternary
// round 6 — the force-AWARE end-to-end judgment (round 7 adds EnvelopeConflict):
pub enum RelationVerdict { HardContradiction, AdvisoryTension, DescriptiveConflict,
                   Refinement { concrete_is_a: bool }, Equivalent, Independent,
                   EnvelopeConflict, Unknown }
pub fn assess(a: &Sentence, b: &Sentence) -> RelationVerdict
// round 8 — contract-level checks for paired assumptions (never return Yes):
pub fn assumption_satisfiable(c: &FormedContract) -> Ternary
pub fn envelope_compatible(c: &FormedContract) -> Ternary
```

Round 5 makes the formulas non-decorative: *implies*, *contradicts*, and
*refines* are computed relations. Every judgment is **deliberately
syntactic and conservative** — `Yes` and `No` only by structural rule,
`Unknown` as the honest first-class answer for everything else. **`Unknown`
must never be treated as `No`.**

- **`implies`** — Boolean structure (constant folding, idempotence,
  syntactic absorption, contraposition, conjunction elimination,
  disjunction introduction); atoms compare by their `Proposition` — the
  logical key: subject digest plus behavior kernel, WITHOUT act, force, or
  anchor, so `The request is logged.` and `The request shall be logged.`
  meet, while behavior and admissibility atoms never compare (requirement
  vs tolerance). **Lossiness-aware since round 6**: the key includes the
  `full` identity strings of the subject and every object/role noun
  phrase, so a `Yes` requires the full renders to match wherever the
  coarse digests match; a coarse match with a full mismatch (`request
  that is authenticated` vs `request that is unauthenticated`, `the owner
  of the file` vs `the owner of the bucket`) is `Unknown` — never `Yes`,
  and never `No` (disjointness of the restrictions is not provable
  syntactically). The same rule covers the CONJUNCTION of a coordinated
  object or role group (round 6 follow-up): `notify the admin or the
  owner` and `notify the admin and the owner` share every item digest and
  differ exactly in the group's `and`/`or` (`Atom::objects_conj`,
  `RoleValue::Heads::conj`), so the pair is `Unknown` — never a mutual
  `Yes` (the true `and → or` entailment is a future strengthening).
  Round 8 extends the rule to CLAUSAL role values: `before`/`after`/
  `until` values carry the whole nested clause skeleton plus its full
  render, so `after no backup completes` and `after the backup
  completes` are `Unknown` in both directions — never the false `Yes`
  the flat round-3 digest produced. A polarity mismatch in the nested
  skeleton is enough for `Unknown`; there is deliberately NO
  nested-clause contradiction logic (a nested denial is a temporal
  boundary condition, not a claim in guarantee position — relating
  nested clauses across sentences is roadmap work).
  Being force-blind is deliberate and cuts both ways: `The
  pump should stop.` and `The pump shall stop.` carry the same
  proposition, so their claims imply each other at `Yes` — the round-5
  caveat that consumers must re-apply act/force context themselves is
  SUPERSEDED as advice by `assess` (below), which is that re-application;
  the force-blind core remains available and blind by design. **Interval
  reasoning (round 6)** replaces the same-operator numeric hook:
  comparisons ground to intervals over all six operators — `greater
  than`/`less than` OPEN, `at least`/`at most` CLOSED, `equal to` the
  point, `between` closed at both ends (its two bounds must share one
  unit) — and implication is CONTAINMENT, so cross-operator entailments
  hold where containment does (`equal to 3` implies `at most 3`; `less
  than 3` implies `at most 5`; `between 4 and 6` implies `at least 2`).
  Deadline/Duration role measures ground the same way — `within n` is
  `(-∞, n]`, `for n` is `[n, ∞)` (the round-5 legislated directions,
  generalized, so `for 10 seconds` still implies `for 5 seconds`), and
  bounded durations (`for at least 30 days`) denote their operator's
  interval and compose with the plain reading. SAME unit throughout (no
  normalization table — `seconds` vs `ms` is `Unknown`); numbers are
  numerals, decimals, or `zero`–`ten`. **Count-quantifier entailment
  (round 7)**: Det-derived Count quantifiers (`at least n` / `at most n`
  / `exactly n`) ground to the same intervals, in SUBJECT position when
  the subjects match on everything except the quantifier (`At least 5
  replicas shall run.` implies `At least 3 replicas shall run.`;
  `exactly 4` implies both `at least 3` and `at most 7`) and in OBJECT
  position when the subjects fully match and exactly one object pair
  differs only in its Count quantifier (`keep at least 5 replicas` ⇒
  `keep at least 3 replicas`). Mixed kinds — Universal, Existential,
  Definite, or Negative against Count — stay `Unknown`. NEGATION does not
  contrapose over subject counts (round 7 attack fix): a `Not` over a
  count-subject atom is a PER-INDIVIDUAL denial — the subject quantifier
  out-scopes it (§ Quantifier scope convention in `formula.rs`) — so `At
  least 5 replicas shall not run.` (≥5 refrain) implies `At least 3
  replicas shall not run.` in the SAME direction, never the reverse, and
  an obligation with a count prohibition (`at least 5 shall run` vs `at
  least 3 shall not run`) is jointly satisfiable: `Unknown`, not a
  contradiction. Object-position negation contraposes classically (the
  `Not` there is predicate-level over one subject). **Content
  identity (round 7)**: a `that`-content complement is part of the
  atom's identity (clause digest + full render), so differing contents
  are `Unknown`, never `Yes` — even where the lossy clause digests
  collide (`ensure that the reading exceeds the limit` vs `… the
  threshold`).
- **`contradicts`** — `Yes` when `implies(a, ¬b)` (or symmetrically) is
  `Yes` — so `The pump shall stop.` vs `The pump shall not stop.` is a
  computed `Yes`; round 6 adds DISJOINT INTERVALS over one measured
  subject: `at most 3` vs `at least 5` contradict (empty intersection),
  while `at most 3` vs `at least 3` stay compatible at 3 (touching CLOSED
  endpoints intersect; `less than 3` vs `at least 3` do contradict). The
  empty-intersection rule reads COMPARISON PREDICATES, same-kind
  Deadline/Duration ROLE measures (round 7 — retiring the round-6
  asymmetry with justification: role intervals already ground
  implication, and an empty intersection over one unit is a proof by the
  same trusted interval reading, so `for at least 30 days` vs `for less
  than 10 days` now contradicts at `Yes`; mixed kinds — a Deadline
  against a Duration — and unit mismatches still never ground), and
  Count quantifiers (round 7: `at least 5 replicas` vs `at most 3
  replicas` contradict, in subject or object position under the same
  full-match gates as the entailment). A descending `between` denotes the
  EMPTY interval — an unsatisfiable claim: it is disjoint from every
  interval INCLUDING ITSELF (so such a claim contradicts itself at
  `Yes` — the exclusion rule fires before the syntactic-equality `No`)
  and is vacuously contained in every interval (so it implies any
  same-subject comparison). Both answers are logically sound for an
  unsatisfiable claim. Round 9 moved the typo-shield to PARSE time: a
  written `between 6 and 4` is now `descending_between` (superseding the
  round-6 "documented, not policed" doctrine — nobody writes an empty
  interval on purpose), so only HAND-BUILT trees can hold one, and for
  those the interval rules above keep giving the sound answers. `No`
  when the formulas are syntactically equal; else `Unknown`. The equality `No` presumes the formula is satisfiable: a
  formula unsatisfiable on its own (e.g. a paired assumption conjoining
  `at least 5` and `at most 3` over one proposition) still returns `No`
  against itself — `No` means "the same claim", not "a consistent claim";
  satisfiability checking is SMT territory, a future strengthening.
- **`refines`** — per the theory, on saturated forms: `concrete` refines
  `abstract` iff the assumption weakens (`implies(abstract.assumption,
  concrete.assumption)`) and the saturated guarantee strengthens
  (`implies(concrete.saturated(), abstract.saturated())`); the two
  `Ternary`s combine conservatively (`Yes`+`Yes`=`Yes`, any `No`=`No`,
  else `Unknown`). `The retry count is at most 3.` refines `The retry
  count is at most 5.` end-to-end from parsed sentences. **Vacuity guard
  (round 11)**: when either side's FORMED assumption is refuted
  (`assumption_satisfiable` = `No`), that side's saturated form is a
  tautology and any implication over it is vacuous, so the judgment
  returns `Unknown` instead of reporting a vacuous proof — the
  [verification doctrine](#pairing-semantics-the-graph-layers-contract).
- **`assumption_satisfiable`** (round 8) — can the conjoined
  contract-forming (non-envelope, proven — round 9 — not recommended,
  `DisjointKeys` — round 10) RELIED formulas of
  a paired contract all hold at once — the exact set `paired` conjoins
  into `A`, so unproven candidate reliances cannot poison the judgment?
  Individually
  valid reliances can conjoin into an unsatisfiable `A` (`At least 5
  replicas shall run.` ∧ `At most 3 replicas shall run.`), and an
  unsatisfiable `A` relieves the guarantee EVERYWHERE — `G ∨ ¬A` is a
  tautology. The check is structural, over the fragments the engine
  already trusts: the simplified conjunction folding to `⊥`, an atom
  against its own negation over one proposition (full identities
  included; count subjects exempt — their `Not` is per-individual), and
  every pairwise exclusion `contradicts` can prove (disjoint count,
  comparison, and role-measure intervals). **ASYMMETRY DOCTRINE
  (legislated): `Yes` is NEVER returned.** `No` is a proof of
  unsatisfiability; `Unknown` means "not disproven" and is the GOOD case
  — satisfiability itself is not provable syntactically (that is model
  territory), so a caller awaiting `Yes` waits forever. Envelope sources
  are excluded (they never enter `A`); a source-less hand-built contract
  is judged over its `assumption` formula directly.
- **`envelope_compatible`** (round 8) — does a paired contract's own
  guarantee forbid exactly what a retained `AdmissibilityEnvelope` source
  admits? The `EnvelopeConflict` machinery one level down: the guarantee
  and each envelope formula decompose into their (guard, claim) parts;
  where the guards witness a shared region (the round-7 witness rule), the
  guarantee's claim FORBIDS behavior — a single negated behavior atom, or
  (round 11) EACH negated behavior conjunct of a conjunction (a conjunct
  is in force regardless of its siblings, so a hand-built mixed
  conjunction `¬a ∧ b` still forbids `a`; parsed prohibition and
  negative-description claims are uniformly negated, so the mixed shape
  only arises hand-built)
  — and the forbidden propositions (full identities included) cover the
  envelope's admitted atom(s), the envelope is violated — `No`. A
  may-retry envelope retained on a shall-not-retry guarantee is `No`; an
  unrelated envelope is `Unknown`. **The compatibility calculus (round
  11)**: prohibition conflicts refute; a NEGATIVE DESCRIPTION bounds
  exactly as a prohibition does (`is never logged` forbids `may be
  logged`); an OBLIGATION whose atom matches the admitted behavior never
  refutes — obligation implies admissibility, so the match is compatible
  EVIDENCE, and the judgment still answers `Unknown` (refutation-only,
  never certification); and the BRANCH RULE for `either … or …`
  envelopes: `No` only when EVERY branch's atom is prohibited (the
  permission is entirely revoked); when only some branch conflicts, an
  alternative can route around — `Unknown`.
  Count subjects and recommended prohibitions never ground (the round-7
  doctrines). Same asymmetry: **never `Yes`** — compatibility (the absence
  of any conflict) cannot be witnessed by these rules; `Unknown` is the
  good case. **Reachability (round 10, superseding the round-8 note)**:
  proposition equality includes the subject's full render, so the only
  provable `No` is a SAME-SUBJECT envelope — and since round 10 the
  validated constructor no longer rejects shared subject keys (they are
  recorded as `SubjectRelation::SharedKeys`, candidate data), so a
  same-subject envelope can arrive through every construction path and
  this check is the formal guard the removed rejection used to
  approximate. When `No` fires it is a sound proof, and the same-subject
  case between two statements is already caught by `assess`'s
  `EnvelopeConflict`.

### Force-aware verdicts (`assess`, round 6; guard-aware and envelope-aware since round 7)

`assess(a, b)` is the end-to-end judgment: it builds the two contract
formulas, runs the force-blind core, then classifies by act and force —
the re-application of context the round-5 caveat asked consumers to do.
First match wins:

| Condition | RelationVerdict |
| --- | --- |
| a permission on either side, crossed by a prohibition, a subject-`no` obligation, or a negative description of the SAME behavior (matching proposition, full identities included, guards witnessing a shared region; count subjects exempt — see below) | `EnvelopeConflict` (round 7) — the prohibition forbids exactly what the permission admits |
| a permission on either side, otherwise — permission × obligation over one atom included | `Unknown` — LEGISLATED (round 7): an obligation implies admissibility, so nothing conflicts, but certifying the pair COMPATIBLE is graph work, not a language fact; permissions otherwise participate via PAIRING, not head-to-head assessment |
| either side is a definition | `Unknown` — vocabulary has no contract to relate |
| guarantees contradict — structurally, OR by the round-7 GUARD-AWARE rule (below) — both sides `Binding` | `HardContradiction` — the set cannot be satisfied as written |
| guarantees contradict, a side `Recommended` | `AdvisoryTension` — following the recommendation would violate the other sentence |
| guarantees contradict, otherwise (a description side) | `DescriptiveConflict` — the system as described breaks (or is broken by) the norm |
| mutual implication, EQUAL force | `Equivalent` |
| mutual implication, unequal force | `Unknown` — LEGISLATED: neither "equivalent" nor a directed refinement is structurally true of a force-divergent pair (`should stop` vs `shall stop`); subsumption is graph policy |
| `refines` holds in the surviving direction AND the concrete side's force is at least as strong (round 12 — the FORCE PREORDER: Binding refines Binding/Recommended/description; Recommended refines only Recommended; descriptions — capability included — refine only descriptions) | `Refinement { concrete_is_a }` — the direction is reported |
| `refines` holds but the force preorder does not (`The service should respond within 5 seconds.` against `The service shall respond within 10 seconds.`) | `Unknown` — LEGISLATED (round 12): reporting it would promote advice into the discharge of a stronger binding promise. The low-level `refines` stays FORCE-BLIND by design; `assess` is the graph-facing verdict where force re-enters |
| both implication directions provably `No` | `Independent` (rarely provable) |
| otherwise | `Unknown` |

**Guard-aware relations (round 7).** A guarantee is assembled as
`¬guard ∨ claim`, and the structural `contradicts` cannot see a
claim-level conflict inside that `Or`: `When the order ships, the system
shall issue the receipt.` vs the same sentence with `shall not` compared
as `Unknown` before round 7. `assess` therefore decomposes each sentence
into its (applicability, claim) pair — the pieces `formula::applicability`
and `formula::claim_formula` expose before assembly — and applies the
CONDITIONAL-CONTRADICTION rule: if the two guards witness a shared
region and the claims provably contradict, the pair conflicts wherever
the shared guard holds. LEGISLATED overlap witness (round 7, extended
round 9): **equal guards up to COMMUTATIVE NORMALIZATION** — round 9
canonicalizes both sides before comparison, sorting `And`/`Or` operand
lists by a deterministic structural key (duplicates already collapsed by
the simplifier's idempotence), so `Where the mode is manual, While the
pump is running,` and `Where the pump is running, While the mode is
manual,` witness the one region they always denoted, and reordered
`and`/`or` conjuncts inside one frame do too (superseding the round-7
reordered-conjuncts-stay-Unknown pins) — a **`Top` guard on either
side** — `Top` is the everywhere-guard, so the other guard's own
region is exactly the overlap — and, round 9, the **INTERVAL OVERLAP
WITNESS**: two single copular comparison guards over the same subject
full identity (same rendered subject + copula read off the guard
anchors, no roles, no subject negation) whose intervals share one unit
and have a provably NON-EMPTY intersection. That witness is
CONSTRUCTIVE — a point of the intersection is a state satisfying both
written guards: an interior point in the generic case, or the single
shared value when two CLOSED bounds merely touch (`at most 3` vs `at
least 3` share exactly 3, so the witness fires; the OPEN touch `less
than 3` vs `at least 3` shares no point and refuses) — so `While the
depth is at most 5,` and `While
the depth is at most 3,` ground a contradiction between conflicting
claims, while an EMPTY intersection (`at most 3` vs `at least 5`)
refuses, and empty operands refuse too. A one-way guard implication of
any other shape (an extra `and` conjunct) still proves CONTAINMENT of
regions but NOT satisfiability of the overlap — syntactic guards cannot
prove that shared region nonempty — so it does not count, and other
differing guards stay `Unknown`, never `Yes`. Guard-equal implication needs no new rule
(`¬g ∨ c₁ → ¬g ∨ c₂` already follows structurally when `c₁ → c₂`), so
guard-equal refinement — deadline containment under one `When` — works
end to end.

Two caveats on the witness, documented rather than decided. First, the
witness is one shared WRITTEN condition, not a proof that the condition
is reachable: guard SATISFIABILITY is not checked (mirroring the
satisfiability caveat on `contradicts`' equality `No`), so a HAND-BUILT
guard whose clause can never hold — the descending empty interval, whose
written form is `descending_between` at parse since round 9 — still
witnesses through the equality case, and a `Yes` downstream presumes the
shared guard region is nonempty. (The round-9 interval overlap witness
is stricter: it checks its own intervals and refuses empty operands and
empty intersections.) The ONE emptiness the
engine can already see syntactically IS policed (round 7 attack fix): an
applicability that is provably empty by its own shape — `g ∧ ¬g`, a
trigger equal to its own `unless` clause — never witnesses, so `When the
order ships, …, unless the order ships.` no longer manufactures a
contradiction. Second — ROUND 10,
superseding the round-7 pinned observation that read the frame family
and trigger kind as *not* part of guard identity — the guard atom now
carries its `GuardRole`, and every atom-level guard match REQUIRES role
equality: `While X` never witnesses against `When X` (nor `When` against
`If`) even over identical clause words, and the round-9 interval overlap
witness gates on matching roles too. The conservative rationale: a
`While` region is a span the condition holds throughout, a `When` region
the instant it becomes true; the round-7 "the state holds at the trigger
instant" argument is a temporal-semantics claim the engine does not
model (edge-triggered and level-sensitive readings genuinely diverge),
so the cross-role witness is retired in the only safe direction — fewer
`Yes` proofs, more `Unknown`. Same-role pairs are unchanged. ONE
cross-role match is kept, role-BLIND by legislation because it only
BLOCKS proofs and its same-words argument holds for every role: the
`g ∧ ¬g` emptiness gate above still recognizes a trigger (or state, or
scope) conjoined with the negation of an `unless` carve-out over the
same written clause — wherever the sentence would apply, the clause
holds and the carve-out fails, so the region is empty regardless of
role, and the vacuous pair still witnesses nothing.

**The admissibility envelope (round 7).** A permission has no lone
contract, and behavior and admissibility atoms deliberately never compare
inside `implies`/`contradicts` (requirement vs tolerance are different
modalities). `EnvelopeConflict` is the ONE judgment that crosses the
species, and it crosses by proposition only: the permission's
admissibility atom against a single NEGATED behavior atom — a
prohibition, a subject-`no` obligation, or a negative description; a
recommendation does not bound — matching on proposition (full identities
included) under the round-7 guard witness. `The client may retry.` vs
`The client shall not retry.` is `EnvelopeConflict`; against `The client
shall retry.` or `The client should not retry.` it stays `Unknown`.
COUNT subjects never conflict here (round 7 attack fix): `At least 3
clients may retry.` and `At least 3 clients shall not retry.` can pick
DIFFERENT witness sets (six clients: three tolerated retriers, three
refrainers), so the prohibition does not forbid exactly what the
permission admits — only Definite/Universal subjects make the two atoms
co-referential.

Every non-`Unknown` verdict inherits the structural-proof trust of the
core; `The pump should stop.` vs `The pump shall not stop.` is
`AdvisoryTension`, `The request is logged.` vs `The request shall not be
logged.` is `DescriptiveConflict`, and `The retry count shall be at most
3.` vs `The retry count shall be at least 5.` is `HardContradiction` via
the interval rule.

What remains `Unknown` is everything the rules cannot see: different
words, unit mismatches, non-containing interval overlaps, quantifier
weakening, `before`/`after` clause reasoning, and all world knowledge. SMT
and NL-entailment strengthenings can only turn some `Unknown`s into
`Yes`/`No`; a `Yes` produced here never depends on them.

---

## Definite references

```rust
pub fn references(&Specification) -> Vec<Reference>
```

Controlled coreference over a whole specification: each **definite** noun
phrase (`the X`) is matched against **indefinite introductions** (`a X` /
`an X`) earlier in the text. This is analysis data, never a parse error.

| Determiner | Role in coreference |
| --- | --- |
| `a`, `an` | introduces its head word |
| `the` | refers — produces a `Reference` |
| anything else (`each`, `every`, `all`, `any`, `no`, quantifiers, bare) | neither introduces nor refers |

The rules, exactly as implemented (round 12, change 3 — antecedents are
tracked by FULL noun-phrase identity, and the `Ambiguous` variant is
RESTORED, retiring the round-6 note that declared it unreachable: that
note was true only while resolution matched heads alone):

- **Candidates by exact head.** The definite's head word must equal an
  antecedent's head word exactly — same string, same casing, no morphology
  (`sessions` does not match `session`). The candidate set is every prior
  indefinite introduction of that head.
- **Reading order.** Noun phrases are visited frames first, then the core, then
  the exception, then the purpose — recursing through `of`-chains, relative
  clause bodies, objects, role phrases, and noun-phrase measures. Only
  introductions strictly earlier in reading order count, so an indefinite in a
  sentence's own frame can be the antecedent of a definite in its core.
- **Identity by the full string.** Each introduction carries its round-6
  full identity (lowercased modifiers + head + `of`-chain + relative,
  determiner excluded). When ALL candidates share one full identity they
  are one term — `Unique`, to the **most recent** introduction.
- **Differing fulls: modifiers select, or the reference is `Ambiguous`.**
  A reference with modifiers matches only candidates whose full CONTAINS
  those modifiers (exact-token containment, lowercased). A selection
  landing on exactly one full identity is `Unique` to its most recent
  introduction; otherwise the resolution is `Ambiguous`, carrying the
  surviving candidates. LEGISLATED (round 12): a bare reference over
  differing fulls is `Ambiguous` over all candidates; modifiers matching
  NO candidate are `Ambiguous` over all candidates too (antecedents of
  the head exist and none is selected — the honest answer is the open
  choice, not deixis); the candidate list is deduplicated by full
  identity, keeping each full's most recent introduction, in reading
  order.
- **Unresolved is not an error.** A definite with no antecedent (`the system`
  as the first mention) is deixis to the system under specification.

```rust
pub struct Reference {
    pub sentence: usize,        // index of the sentence holding the definite NP
    pub head: String,           // its head word
    pub resolution: Resolution,
}

pub enum Resolution {
    Unique { antecedent_sentence: usize },
    Ambiguous { candidates: Vec<AntecedentCandidate> },
    Unresolved,
}

pub struct AntecedentCandidate {
    pub sentence: usize,        // where the introduction happened
    pub full: String,           // its full identity string
}
```

Worked example:

```text
A session means a sequence of requests.
When a session expires, the system shall close the session.
```

| Definite | `resolution` | Why |
| --- | --- | --- |
| `the system` (sentence 1) | `Unresolved` | no introduction of `system` — deixis, not an error |
| `the session` (sentence 1) | `Unique { antecedent_sentence: 1 }` | both `a session` introductions share one full identity; the most recent is the frame's own, in the same sentence |

The motivating trio (round 12):

```text
A user session shall expire.
An admin session shall expire.
The session shall expire.
```

| Definite | `resolution` | Why |
| --- | --- | --- |
| `the session` (sentence 2) | `Ambiguous { candidates: [user session @ 0, admin session @ 1] }` | two candidates with differing fulls, and the bare reference selects neither |

Written `The admin session shall expire.` instead, the reference's
modifier `admin` selects the sentence-1 introduction:
`Unique { antecedent_sentence: 1 }`.

---

## Normalization candidates (round 11)

`semantics::normalization_candidates(&Sentence) ->
Vec<NormalizationCandidate>` proposes ACTIVE/PASSIVE alignments:
for a passive behavioral claim with a stated Agent — a description's
agent slot (or a hand-built Agent role in its tail), or a deontic
`be`-complement's Agent role — it emits active-voice candidate atoms with
`NormalizationCandidate { kind: ActivePassive, atom, subject, note }`:

- **subject** — the stated agent, digested as a subject (one candidate
  set per coordinated agent item, surface order);
- **atom** — the candidate verb, the grammatical subject (the patient) as
  the object digest, and the non-Agent role tail as written;
- **verb candidates** — a CRUDE, legislated participle-stem list, all
  plausible stems emitted and none claimed correct. Round 12 (change 5)
  order — superseding the round-11 "participle itself always leads" pin
  (the better guesses lead so consumers trying candidates in order try
  the likeliest first): **(1)** the irregular-map hit, from a small
  closed map (`sent`→`send`, `kept`→`keep`, `made`→`make`,
  `held`→`hold`, `built`→`build`, `left`→`leave`, `lost`→`lose`,
  `found`→`find`, `brought`→`bring`, `bought`→`buy`, `caught`→`catch`,
  `taught`→`teach`, `sold`→`sell`, `told`→`tell`, `paid`→`pay`,
  `laid`→`lay`, `said`→`say`, `read`→`read`, `run`→`run`, `done`→`do`,
  `given`→`give`, `taken`→`take`, `written`→`write`, `chosen`→`choose`,
  `seen`→`see`, `known`→`know`); **(2)** the double-consonant UNDOUBLED
  strip (`logged` → `log`, `stopped` → `stop`); **(3)** the round-11
  strips — an `ed`/`en` ending longer than three characters gives the
  two-character and one-character strips (`logged` → `logg`, `logge`), a
  bare `d` ending longer than two characters gives the `d`-strip;
  **(4)** the participle itself, always present. Duplicates drop, order
  kept: `logged` → `log`, `logg`, `logge`, `logged`; `sent` → `send`,
  `sent`.

**Proposal-only doctrine (legislated).** Candidates PROPOSE edges; they
never prove. Consumers must verify a candidate against the sentence's
anchors and raw text before acting on it, and the relation engine
deliberately does NOT consume candidates — no `relate` integration, so a
crude morphological guess can never ground a `Yes`. Scope is deliberately
narrow: single-word `Predicate::Words` participles only, single deontic
verb phrases only (`either … or …` deontics emit nothing), and the
reverse direction (active → passive candidates) is out of scope. Active
sentences, agentless passives, definitions, capabilities, comparisons,
and multi-word predicates emit nothing. AFFIRMATIVE BEHAVIORAL claims
only (round 11 fix): a NEGATED site — `is never submitted by …`, `shall
not be sent by …` — emits nothing, because the candidate atom carries no
polarity slot and an affirmative-shaped proposal would align a
never-claim with its affirmative active twin; a PERMISSION (`may be sent
by …`) emits nothing either — a permission denotes admissibility, not
behavior. Recommendations (`should be sent by …`) stay in scope.

---

## Serialization

All types on this page derive `serde::{Serialize, Deserialize}` with the same
conventions as the syntax tree:

| Type | Convention | Example |
| --- | --- | --- |
| `SpeechAct`, `Force`, `Polarity`, `Assumption`, `CountOp`, `EdgeKind`, `SubjectRelation`, `SourceIssueReason` | unit variants, `snake_case` | `"obligation"`, `"top"`, `"at_least"`, `"guarantee_discharge"`, `"shared_keys"`, `"not_explicit_relied"` |
| `Claim`, `Denotation`, `Resolution`, `Quantifier`, `RoleValue`, `Formula`, `AtomRef`, `GuardRole` | internally tagged, `"kind"`, `snake_case` | `{ "kind": "admissible", … }`, `{ "kind": "count", "op": "at_least", "n": 3 }`, `{ "kind": "heads", "items": [{ "quantifier": { "kind": "definite" }, "head": "archive" }] }`, `{ "kind": "not", "inner": … }` |
| `Assertion`, `IngestContract`, `Reference`, `AntecedentCandidate`, `Skeleton`, `SubjectSkeleton`, `ObjectSkeleton`, `Atom`, `RoleSkeleton`, `ClauseSkeleton`, `TriggerSkeleton`, `Guards`, `BehaviorAtom`, `Contract`, `FormedContract`, `AssumptionSource`, `WellFormedness`, `SourceIssue` | plain structs | field names as written |

Internally tagged enums cannot serialize a newtype variant that holds a bare
sequence or primitive, so the two syntax-tree variants that carry one are
struct variants on the wire: an open-word predicate serializes as
`{ "kind": "words", "words": ["logged"] }` and a count determiner as
`{ "kind": "at_least", "n": 3 }` (`at_most`/`exactly` likewise). A
newtype variant over a payload that is ITSELF internally tagged by
`kind` collides the same way — the flattened inner tag duplicates the
outer one in a document `serde_json` writes but refuses to read — so a
noun-phrase measure is a struct variant on the wire too:
`{ "kind": "np", "np": … }` (round-9 attack fix; the old shape was
unreadable, so nothing valid persisted under it). The
`serialization.rs` test suite pins these shapes with JSON round trips over
the syntax tree and every derived view.

Round 12 wire changes: `WellFormedness` gains
`"all_sources_contract_forming": bool` — THE one-call aggregate (every
non-envelope source contract-forms) — and `"source_issues"`: a list of
plain-struct `SourceIssue { "index": usize, "reasons": [...] }` entries,
skipped when empty, whose reasons are the `snake_case` unit variants of
`SourceIssueReason` (`"not_explicit_relied"`, `"not_proven"`,
`"shared_subject_keys"`, `"recommended_force"`, `"envelope_kind"` — the
last recorded but by-design, never a defect). Pre-round-12 summaries
without the fields load as `false` and empty — the conservative
direction (a summary is a derived view; re-derive rather than trust).
`Resolution` regains the internally tagged `"ambiguous"` variant —
`{ "kind": "ambiguous", "candidates": [{ "sentence": 0, "full": "user
session" }] }` — carrying plain-struct `AntecedentCandidate` entries;
`ClauseSkeleton.objects` now also carries a CAPABILITY body's verb-phrase
object digests (change 6 — same field, same skip-when-empty shape;
skeletons are derived views and re-derivation refreshes them).

Round 11 wire changes: `ClauseSkeleton` gains `"objects"` — a verbal
body's object digests (one `ObjectSkeleton` per coordinated item),
skipped when empty; pre-round-11 digests without the field load as empty
— the documented legacy reading (the old digest dropped the object; a
re-derivation from raw text refreshes it). `AssumptionSource` gains
`"explicit_relied": bool`; pre-round-11 sources without it load as
`false` — the CONSERVATIVE direction: an old JSON edge becomes a
CANDIDATE (it no longer forms `A`) rather than silently keeping the
power to relieve a guarantee, and re-derivation through
`for_guarantee_with_relied` restores contract forming honestly.
`WellFormedness` is a new plain struct (two booleans, two `Ternary`s);
`NormalizationCandidate` is NOT serialized (a proposal-only in-memory
view carrying a `&'static` provenance note).

Round 10 wire changes: the guard atom (`AtomRef::Guard`) gains `"role"` —
the internally tagged `GuardRole` (`{ "kind": "scope" }`,
`{ "kind": "state" }`, `{ "kind": "trigger", "trigger": "event" }`,
`{ "kind": "exception" }`; the trigger kind's field is named `"trigger"`
on the wire because the enum's own tag already claims `"kind"`).
Pre-round-10 guard atoms without `"role"` load as `"state"` — DOCUMENTED
as the pre-round-10 reading, in which all guard families digested alike:
a legacy atom keeps exactly the identity it was recorded with rather than
being silently promoted into a finer one, and re-derivation from raw text
refreshes the role honestly. `AssumptionSource` gains
`"subject_relation"` (`"disjoint_keys"` / `"shared_keys"`); pre-round-10
sources without it load as `"disjoint_keys"` — the pre-round-10 reading
(a stored `for_guarantee` edge could only exist GRAMMATICALLY disjoint,
because the removed rejection compared grammatical `subject_keys`; a
passive-agent source that is `shared_keys` under the round-10 RESPONSIBLE
reading was constructible then and still loads as `disjoint_keys`, and a
stored `from_sentence` edge entered A
regardless, which the default preserves until re-derivation refreshes it).
The `same_subject` pairing-error kind is retired with the removed
`PairingError::SameSubject` variant.

Round 9 wire changes: `RoleSkeleton` gains `"marker"` (the Location
preposition, lowercased; absent for every other kind and skipped when
`None`), `ClauseSkeleton` gains `"content"` (a verbal body's content
digest — `{ "clause": …, "full": … }` — skipped when absent), the syntax
tree's verbal clause body gains `"content"` (a nested clause, skipped
when absent), and `RelativeBody` gains the internally tagged
`{ "kind": "object_gap", "subject": …, "verb": …, … }` variant.
Pre-round-9 JSON without any of these fields loads unchanged.

Round 8 wire changes: a clausal role value serializes as
`{ "kind": "clause", "skeleton": { …ClauseSkeleton… }, "full": "the order
ships" }` — the nested skeleton and full render REPLACE the flat
round-3 `{ "kind": "clause", "subject_head": …, "words": […] }` shape
(skeletons are derived views, re-derived from the raw text, so no
migration path is kept for the old shape). `AssumptionSource` gains
`"proven": bool`.

Backward compatibility of derived views: pre-round-7 JSON without
`AssumptionSource.relied` deserializes with `relied` defaulted to the
source `formula` (the round-6 meaning — a manual `Deserialize`, since the
default is a sibling field), and pre-round-7 atoms without `content` load
with `content: None`; pre-round-7 relative bodies without
`particle`/`manner`/`roles` load with the slots empty. Pre-round-8
sources without `proven` load as `proven: false` (unproven until
re-derived); pre-round-8 copular clause bodies without `roles`, and
copular relative bodies without `agent`/`roles`, load with the slots
empty; description cores (and `Claim::State`) without the round-8
follow-up `roles` — the role tail after the passive agent — load with the
slot empty too.

`Assumption::Top.render()` produces `⊤` for display; rendering is not the
persisted representation — the raw sentence text is.
