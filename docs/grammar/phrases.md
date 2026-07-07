# The phrase grammar

> Part of the [grammar reference](./README.md).

Below the sentence layer sits one shared phrase grammar. Every slot a sentence
offers — the subject of a speech-act core, the clause inside a circumstance
frame, the object of a verb, the bound of a comparison — is filled by the same
few phrase categories: noun phrases, verb phrases, predicates, and measures.
This page documents those categories as `so_lang/src/parse.rs` recognizes them
and `so_lang/src/ast.rs` represents them.

Two rules govern everything here:

- **Closed-class words are owned; open-class words are free.** Determiners,
  quantifiers, conjunctions, role prepositions, and comparison openers are
  recognized case-insensitively, and only in the positions where they are
  closed. Everything else — nouns, verbs, adjectives, identifiers, URLs,
  multibyte words — passes through as opaque tokens with surface casing kept.
- **Every meaning-bearing word lands in the tree.** Determiners, quantifiers,
  role markers, and negation are all represented, never normalized away. The
  canonical rendering re-emits closed-class words in lowercase and open-class
  words exactly as written.

---

## Noun phrases

A noun phrase is:

```text
[determiner] [modifiers ...] head [of <noun phrase>] [that|who <relative body>]
```

The modifiers are zero or more open-class words before the head, kept in
surface order and casing; the head is the last open-class word of the run.
Collection stops at any reserved word — a pivot, a frame keyword, `of`,
`that`, `who`, a conjunction or `both`/`either` marker, a clause copula,
`not`, `then`, and the excluded modals `can`/`will`/`would`/`could`/`might`/
`ought` (reserved everywhere so they can be diagnosed at pivot position) —
and, inside a verb phrase, at any role preposition. A phrase with no head is
an error whose name depends on the hole (`EmptySubject`, `EmptyPredicate`, …);
see
[errors.md](./errors.md).

Bare `with` is CLOSED in every noun-phrase collection context (round 6 —
plain subject positions included): `The file with the flag shall be
archived.` used to fold `with the flag` into the modifiers, pinning the
subject head to `flag` — accepted-but-wrong — and is now rejected as
`WithIsAmbiguous`, the same discipline as at role positions. The supported
restriction forms are the `of`-chain and the relative clause (`the file
that carries the flag`); a backticked `` `with` `` stays an ordinary noun.

To use a reserved word *as* an open-class word, wrap it in backticks: `` the
`will` `` is a noun phrase with head `` `will` ``, and `` the `while` loop ``
carries the modifier `` `while` ``. A backticked token is never
keyword-matched and the backticks are preserved in the stored word and in the
render; see
[lexical.md](./lexical.md#backtick-tokens-the-reserved-word-escape-hatch).

### Determiners and quantifiers

| Determiner | Example | Notes |
| --- | --- | --- |
| `the` | `the pump` | definite |
| `a` / `an` | `a workspace` | indefinite. In the derived skeleton, position matters (round 5): a BEHAVIORAL SUBJECT `a`/`an` (and a bare subject) is the requirements-English generic reading and normalizes to the universal quantifier (`A request shall be logged.` obliges every request), while object and role `a`/`an` stay existential (`shall create a session` is one session per occasion) — see [semantics.md](./semantics.md#the-logical-skeleton) |
| `each` / `every` / `all` / `any` | `each request` | the word used is preserved; the grammar does not collapse them. In the derived skeleton all four normalize to one universal quantifier — `any` is legislated universal (requirements English reads `any request …` as `every request …`) |
| `no` | `no OTLP endpoint` | a negation site — see [Negation sites](#negation-sites) |
| `at least N` | `at least 3 replicas` | stored as the count `3` |
| `at most N` | `at most two nodes` | number words work: stored as `2` |
| `exactly N` | `exactly 7 partitions` | stored as `7` |

Determiners are kept because dropping them collapses distinct sentences:
`each request shall be logged` and `requests are logged` are different
sentences making different claims, and `at least 3 replicas` differs from
`at most 3 replicas` in exactly the word a normalizer would be tempted to
strip. The counting quantifiers additionally store their number as a value
rather than a string, so two counts over the same head can be compared
directly — `at least 5 nodes` is a strictly stronger demand than
`at least 3 nodes`, and that ordering is readable off the tree.

The definite/indefinite distinction also feeds the coreference analysis in
[semantics.md](./semantics.md): `a session` introduces a term that a later
`the session` refers back to.

Rules for the counting quantifiers:

- `at least` / `at most` / `exactly` open a quantifier **only when a number
  follows** — a numeral (`3`) or a number word from the table (round 12:
  `zero` through `twenty`, the tens `thirty`–`ninety`, and `hundred`).
  Otherwise the words stay open-class: in `the sensor is at the door`, `at`
  is an ordinary preposition (and in predicate position opens a locative
  predicate, see below).
- A quantifier counts whole things. A decimal (`at least 5.5 nodes`) or an
  integer too large for 64 bits is rejected with `QuantifierNotWhole` rather
  than silently falling through as open-class words, which would erase the
  quantifier from the tree.
- An UNKNOWN number word after the opener is rejected fail-closed (round 12
  — superseding the round-1 silent fallthrough, in which `at least eleven`
  degraded to ordinary modifier words): `At least eleventy nodes shall
  run.` and the unsupported compound `At least twenty-one nodes shall run.`
  are `UnknownNumberWord` — write digits (`at least 21 nodes`). A
  determiner-led phrase after the opener is not a number position gone
  wrong and keeps its existing reading (`for at least the limit` stays
  `ForRequiresMeasure`).

### The `of`-chain

`of` is the **only preposition that attaches to a noun**:

```text
A session means a sequence of requests from one client.
```

Here `a sequence of requests` is one noun phrase — head `sequence`, with the
inner phrase `requests` hanging off `of` — while `from one client` is *not*
part of the noun phrase: `from` is a thematic role on the surrounding phrase
(see [Thematic roles](#thematic-roles)). Keeping all other prepositions off
the noun keeps attachment unambiguous: there is never a question of whether a
trailing prepositional phrase modifies the noun or the verb, because only
`of` can modify the noun. `of`-chains nest (`the head of the queue of
retries`), subject to the [depth bound](#the-phrase-depth-bound).

### Restrictive relative clauses

A noun phrase may end with a restrictive relative clause, marked by `that` or
`who` and attached to the immediately preceding head:

```text
Each request that carries a token shall be logged.
The user who is authenticated may open the session.
```

The relative body is either copular — `is` / `are` / `remains` followed by a
predicate — or verbal. **Round 7: the verbal body is the FULL verbal tail** —
verb, optional particle, manner adverbs, optional object, and thematic-role
phrases, exactly the shape a verbal clause body reads:

```text
Each request that arrives from the gateway shall be logged.
The daemon shall close each session that times out.
Each job that completes successfully shall be archived.
Each packet that arrives before the window closes shall be inspected.
```

Clausal roles (`before`/`after`/`until <clause>`) work inside the tail in
SUBJECT position as well as object position (round 7 attack fix): the
role's clause ends at the enclosing sentence's modal, which is a reserved
word that can never be clause material.

**Round 9: object-gap relatives.** A relative may also restrict its head
as the MISSING OBJECT of the relative's verb — the body carries its own
subject and the verbal tail without an object slot:

```text
Each request that the gateway forwards shall be logged.
Each user who the auditor flags shall be reviewed.
Each alert that the backup daemon raises shall be recorded.
Each request that at least 3 gateways forward shall be logged.
Each packet that the router sends out via the tunnel within 5 seconds shall be counted.
When each request that the gateway forwards arrives, the daemon shall wake.
```

The reading is deterministic, pinned both ways:

- The gap opens ONLY when a **determiner/quantifier-led** noun phrase
  follows `that`/`who` (the copular reading is tried first, so `that is
  signed` stays copular). The gap's subject is the SHORTEST prefix that
  spans at least the whole determiner or quantifier, parses exactly as a
  noun-phrase group followed by a verb-position word, AND leaves no
  object material after that verb (its particle and manner run
  included), so `each file that the owner of the workspace shares`
  restricts by the whole `of`-chain subject. The clean-tail condition
  (round-9 attack fix) makes trailing bare words EXTEND the subject
  instead of aborting: `that the backup daemon raises` is subject `the
  backup daemon` + verb `raises`, and `that at least 3 gateways forward`
  keeps its quantifier structured in the subject.
- LEGISLATED collision, the det-led mirror of the bare-NP rule below: a
  det-led body ending in two open words — `that the session holds
  locks` — reads as the longer subject (`the session holds`) with the
  last word as the gap's verb. The grammar has no verb lexicon to prefer
  the saturated `holds` + object `locks` reading, and that reading never
  parsed here anyway (a determiner cannot open a verbal tail), so the
  gap only turns a rejection into a parse.
- A **bare** noun phrase after the marker never opens a gap (legislated):
  `that holds locks` keeps its round-7 subject-gap reading (verb `holds`,
  object `locks`) — no syntactic rule could tell it from a gap's subject +
  verb (`that gateways forward`), so the established reading wins and
  bare-subject gaps stay unsupported.
- An **explicit object after any candidate verb** — determiner or
  quantifier-led, group-marked (`both`/`either`), or a bare number —
  means the relative is saturated and the head is not the missing
  object — not a gap at any split: `each request that the gateway
  forwards the packet` and `… forwards 5 packets` keep their
  `determiner_as_verb` rejection.
- Exactly ONE gap, implicit: the missing object slot is the restricted
  head; the gap's roles, particle, and manner attach to the gap's verb
  (innermost attachment, as for every relative). Renders as written —
  `that <subject> <verb> …` — and round-trips. RelativeBody verbal arms
  (gap included) carry NO content clause in v0.2.

**Round 8: the copular body mirrors the copular clause body** — after the
predicate it takes an optional passive agent (`by <np-group>`, the round-5
shape) and the same thematic-role tail, and `able to <vp>` exactly after
the copula is the capability predicate (see
[the capability predicate](#the-capability-predicate--able-to-vp)):

```text
Each request that is signed by the user shall be logged.
Each request that is valid within 5 seconds shall be logged.
Each daemon that is able to shut down gracefully shall register.
```

Roles inside a relative attach to the RELATIVE's verb or predicate —
**innermost attachment, legislated**: `the session that holds the lock in
the vault` locates the HOLDING, not the closing; there is no outer reading
of a role written after a relative's object (state the outer role before
the object instead). The relative's tail participates in the noun phrase's
full identity, so `request that arrives from the gateway` and `request
that arrives from the proxy` never meet in a relation judgment.

The two markers are interchangeable to the grammar; the one written is
preserved. The relative clause consumes its own copula or verb, so a keyword
inside it never ends the enclosing subject:

```text
The account that is frozen is never active.
```

parses with `that is frozen` inside the subject and the *second* `is` as the
sentence's pivot.

**Attachment after an `of`-chain (round 5, legislated).** The two markers
differ exactly here:

- A **`that`-relative attaches to the nearest preceding head** — in
  `a sequence of requests that carry a token`, the relative belongs to
  `requests`.
- A **`who`-relative attaches to the ROOT of the chain** — in
  `the user of the workspace who is active`, the relative restricts the
  USER, not the workspace. `who` is animate, and the chain root is the
  phrase's referent; the rule is deterministic, marker by marker, so both
  readings are writable: use `that` to restrict the inner head, `who` to
  restrict the outer one. Both attachments render after the full chain and
  round-trip (`the user of the workspace who is active` re-parses with the
  relative on `user`).

---

## Coordination

Wherever a noun phrase can appear (except a definition's term), a
**coordinated group** can appear instead:

```text
[both | either] <np> {and|or <np>} ...
```

- **One conjunction throughout.** A group is joined by `and` or by `or`,
  never both: `the total and the tax or the fee` is rejected with
  `MixedCoordination`. So are two conjunctions in a row (`and or`). The
  canonical rewrite is to pick one conjunction, or to split into separate
  sentences — one sentence per claim.
- **Unmarked groups may have any number of items.**
  `The pump and the valve and the fan shall stop.` is a legal three-item
  group.
- **`both` pairs with `and`, `either` with `or`, each over exactly two
  items.** `Both the pump and the valve shall stop.` and `Either the cache
  or the database shall answer.` parse, with the marker recorded.
  `Both the pump or the valve …`, a three-item `both …`, or a marker with no
  conjunction at all are each rejected with `MixedCoordination`.

The conjunction and marker are stored on the group, not inferred later, so
`and`-groups and `or`-groups remain distinguishable in the tree. Coordination
is iterative in the recognizer: groups thousands of items wide parse without
deepening any recursion.

---

## Verb phrases

A verb phrase — the material after a deontic modal, and the body of an
`in order to` purpose — is:

```text
<verb> [particle] {manner} [object] [complement] {role phrase} ... [that <clause>]
```

### Content complements — `<verb> that <clause>` (round 7)

A verb phrase may end with a **content complement**: `that` followed by a
full clause, stating what the verb's action is about:

```text
The server shall ensure that the token is valid.
The system shall verify within 5 seconds that the token is valid.
The monitor shall ensure that no request is dropped.
```

The rules, legislated and pinned both ways:

- **Content is FINAL: roles precede it**, and the clause consumes the rest
  of the verb phrase (`verify within 5 seconds that …` works; nothing may
  follow the clause). A measure written AFTER the clause therefore
  attaches INSIDE it — and since round 8 (copular role tails) the content
  clause structures it: `verify that the token is valid within 5 seconds`
  carries a structured `Deadline` role INSIDE the content skeleton.
  Attachment stays inner and content compares by IDENTITY (skeleton plus
  full render), so an inner deadline still never grounds an interval: the
  spelling relates to the roles-first form (and to the same content with a
  different inner deadline) only as `Unknown`. Write the deadline before
  the `that` when it must ground containment.
- **After a NOUN, `that` is that noun's restrictive relative** — the
  existing rule wins. `record the fact that the token is valid` keeps the
  relative reading, and since the tail has no verb-position word after
  any gap-subject split (round 9), the relative still rejects the
  determiner (`determiner_as_verb`), so the sentence is rejected rather
  than silently re-read; content-`that` triggers only where a relative
  cannot attach — directly after the verb (its particle and manner run
  included) or after a measure role.
- **Available in every verb-phrase position** (legislated, round 7):
  `be`-complement phrases and `either … or …` alternative items included —
  the slot sits after the shared role tail, so excluding them would cost a
  rule, not save one. `shall either ensure that the token is valid or
  reject the request` parses.
- **Available in VERBAL CLAUSE BODIES since round 9** (superseding the
  round-7 "frames stay content-free" legislation, on new grounds:
  assumptions depend on observed/asserted content, so dependency
  statements belong in guards). A frame, exception, purpose, definiens,
  or nested `before`/`after`/`until` clause whose body is verbal takes
  the same final `that <clause>`:

  ```text
  When the monitor ensures that the token is valid, the pump shall stop.
  The pump shall stop, unless the monitor reports that the link is down.
  While the pump runs until the monitor confirms that the tank is full, the daemon shall wait.
  ```

  Content is final in the clause exactly as in a verb phrase (roles
  precede it; the nested clause consumes the rest of the clause slice),
  nesting shares the one depth budget, and after a noun the `that` is
  still that noun's relative. RELATIVE bodies remain content-free in
  v0.2 (legislated): `each daemon that reports that the link is down` is
  rejected, never silently re-read.

The content clause digests into the claim atom (`Atom::content`) as its
clause skeleton PLUS a full-fidelity identity string, so `ensure that the
reading exceeds the limit` and `… the threshold` never meet in a relation
judgment ([semantics.md](semantics.md)).

### Alternatives — `either <vp> or <vp>` (round 6)

A DEONTIC core (and only a deontic core — descriptions and capabilities
keep a single verb phrase in v0.2) may state genuine alternatives:

```text
The server shall either accept the request or reject the request.
The daemon shall either be idle or run the job or stop.
The client may either retry or abort.
```

The `either` marker is REQUIRED and the conjunction is `or` only; two or
more full verb phrases are split at top-level `or` tokens, backtracking so
an `or` inside an item's own noun-phrase coordination stays inside the
item. This form exists because splitting has no faithful equivalent: two
`shall` sentences oblige BOTH behaviors, while `either … or …` obliges the
disjunction. `and`-coordination of verb phrases stays unsupported for the
dual reason — two sentences already mean exactly that.

Disambiguation with the noun-phrase `either` marker is deterministic
lookahead: directly after the modal, `either` followed by anything but a
determiner opens verb-phrase alternatives; followed by a determiner it
stays the noun-phrase marker (which the verb position then rejects, as
before round 6). In object position `either the admin or the owner` is the
unchanged noun-phrase coordination. `shall not either … or …` is rejected
(`NegatedAlternatives`, legislated): write two prohibitions instead of
trusting a De Morgan reading. `be <predicate>` is a valid alternative item.

- **The verb** is a single open-class word. A reserved word here is
  diagnosed, not guessed at: a frame keyword after the modal means the
  condition was written trailing (`MidSentenceFrame`), and an empty verb
  phrase (`The pump shall.`) is `EmptyVp`. A determiner (or counting
  quantifier) here is `DeterminerAsVerb` (round 6 follow-up): `The pump
  shall the valve.` — and the determiner-led TAIL of an `either … or …`
  alternative (`shall either notify the admin or the owner`) — used to
  accept the determiner as an open-class verb, an accepted-but-wrong
  tree.
- **The object** is a noun-phrase group, present when the next word is not a
  role preposition or another stop word: `record the total`,
  `install TraceContext and Baggage propagators`.
- **The `be`-complement.** When the verb is `be`, it takes a complement
  predicate instead of an object: `be frozen`, `be greater than zero`,
  `be equal to zero`. The complement is any [predicate](#predicates), so the
  passive-voice obligation `Each request shall be logged.` and the numeric
  bound `The account balance shall be equal to zero.` are the same shape.
  When a role preposition immediately follows `be`, there is no complement:
  `The receipt shall be from the gateway.` parses as bare `be` plus a Source
  role. Note that `equal to` wins over the `to` role here — the comparison
  opener is checked first, so `be equal to zero` has no Recipient.
- **Particle verbs — the controlled particle slot.** Immediately after the
  verb, one word from the closed list `out`, `down`, `up`, `off` is the
  verb's **particle**, not an object head: `the session shall time out`,
  `shut down the server` (particle `down`, object `the server`). The rule is
  deterministic — in the list and the verb has no particle yet → particle —
  and a backticked token (`` `out` ``) never matches, so `log `out`.` keeps
  `out` as the object. A particle **reached across the manner run** joins
  the verb the same way: `shut gracefully down` is the particle verb `shut
  down` with manner `gracefully` (canonical render `shut down
  gracefully`), so both spellings share one atom. A particle word left
  **trailing the object** joins
  the verb the same way: `lift the beam up` and `lift up the beam` are one
  particle verb (`lift up`) applied to `the beam` — the trailing word is
  popped off the object only when it would have been the object's head with
  no `of`-chain or relative attached and other noun material remains
  (`start the power up of the system` keeps `up` as a noun head; so does
  `log the up`). The canonical render always places the particle next to
  its verb. Hyphenate a noun spelled like a particle (`the warm-up`) to
  keep it noun material in object-final position. The particle joins the
  verb in the semantic atom (`time out` and
  `time` are different behaviors). Legislated: a particle never combines
  with a following `of` — there is no `out of` chain, so `run out of water`
  leaves `of` as stray material (`unexpected_tokens`). `in` and `on` are
  **not** particles (they open Location roles); for `logs in`-style verbs,
  hyphenation (`logs-in`) remains the workaround, and `be` takes no particle
  (`shall be off` is the state `off`, a complement).
- **Manner adverbs — the controlled manner slot.** After the verb (and its
  particle), a run of bare words ending in ASCII `ly` (length > 2) fills
  the **manner** slot: `The pump shall stop immediately.`, `The daemon
  shall shut down gracefully within 5 seconds.` The rule is positional and
  deterministic — a bare `ly` word where an object or role would start,
  i.e. not determiner-led (`retain exactly 7 copies` keeps its
  quantifier), not a role or locative preposition, not a conjunction or
  boundary. Inside a noun phrase — after a determiner, or as a modifier
  before a head — `ly` words are untouched: `the assembly` and `the
  nightly build` parse as noun phrases. Only juxtaposition extends the run
  (`stop immediately gracefully`); a conjunction ends it, so `quickly and
  safely` is not supported (the leftover `and …` is `unexpected_tokens`).
  **The tradeoff, explicitly:** a bare `ly` word the author means as a
  noun *object* is read as manner — `record supply` takes `supply` as
  manner — and needs backticks to stay a noun: `` record `supply` ``
  keeps the object. Manner renders right after the verb/particle, before
  the object, so the canonical form re-parses to the same tree; it enters
  the semantic atom beside (not inside) the verb words, so `stop` and
  `stop immediately` share a verb kernel and differ exactly in manner.

## Thematic roles

After the verb (and its object or complement), a verb phrase takes zero or
more **thematic-role phrases**. Each is opened by a preposition that is
closed *only in this position*; elsewhere the same words are ordinary
open-class tokens. The preposition fixes the role, and the role is why the
phrase matters: recipients, deadlines, and means are load-bearing
specification content, not decoration on an opaque response string.

| Preposition | Role | Takes | Why it is load-bearing |
| --- | --- | --- | --- |
| `to` | Recipient | noun-phrase group | who or what must receive the effect — `notify` without its recipient is a different obligation |
| `via` / `using` | Means | noun-phrase group | the required mechanism (`via TLS`); the marker word is preserved |
| `about` | Topic | noun-phrase group | what a communication concerns |
| `within` | Deadline | measure | deadlines carry a refinement order of their own — `within 5 seconds` demands strictly more than `within ten seconds` |
| `for` | Duration | **quantity** measure | how long an effect must hold (`retain the log for 30 days`). Round 5: a duration **requires a quantity** — a number (or number word) with an optional unit. A non-quantity `for` (`listen for requests`) is rejected with `ForRequiresMeasure`: write `about <topic>` for a topic, `until <clause>` to wait on an event, or reword |
| `per` | Rate | one unit word | the unit of a recurring action (`poll per second`) |
| `before` | Before | clause | orders the action against another event |
| `after` | After | clause | orders the action against another event |
| `until` | Until | clause | bounds how long the behavior holds against another event (`run until the tank is empty`) |
| `from` | Source | noun-phrase group | the origin of a transfer |
| `into` | Goal | noun-phrase group | the destination of a transfer |
| `in` / `on` / `at` / `under` / `over` / `above` / `below` | Location | noun-phrase group | where the behavior happens (`store the report in the archive`); the preposition is kept as written |
| `by` | Agent | noun-phrase group | the **passive agent**, admitted ONLY in a passive site — a `be` verb phrase with a complement (`shall be logged by the daemon`), after a description's / copular clause's predicate (`is logged by the daemon`), or (round 8) in a copular clause/relative body's role tail (`is stored in the archive by the daemon`). Everywhere else a role-position `by` is rejected with `ByOutsidePassive` (round 5) — including after a bare complement-less `be` (`shall be by the dock`), which has nothing passive in it |
| `with` | — (rejected) | — | reserved at role positions ONLY to be rejected (round 5): instrument vs accompaniment has no single reading (`WithIsAmbiguous`). Write `using <means>` for an instrument; coordinate with `and` for accompaniment |

```text
The gateway shall send the receipt to the customer via TLS.
The service shall copy the record from the queue into the archive.
When an order is submitted, the system shall record the order within 5 seconds.
The system shall store the report in the archive.
The pump shall run at the depot.
```

Rules:

- **Order is free and duplicates are kept** in surface order. `to the
  customer via TLS` and `via TLS to the customer` both parse; the tree
  records the order written.
- **`before` and `after` take a full clause**, not a noun phrase —
  `before the connection closes` names an event with its own subject and
  verb. The clause runs to the end of the sentence part it appears in, so a
  `before`/`after` role is necessarily the last role of its phrase.
- **Temporal-clause INNER attachment (fixed, deterministic — read this
  before writing a role after `before`/`after`/`until`).** Because the
  temporal clause consumes everything to its right, and verbal clause
  bodies carry roles of their own, any role written after the temporal
  keyword belongs to the INNER clause, never to the outer verb phrase:
  `notify the user after the backup completes using email` is the inner
  reading — the Means role sits on `completes`, i.e. the backup completes
  using email. The outer reading must be written with the role BEFORE the
  temporal clause: `notify the user using email after the backup
  completes`. Both spellings parse; they mean different things, and the
  reading is fixed by position, not guessed ([cookbook.md](cookbook.md)
  pairs the two).
- **Role prepositions are closed after a verb.** Verb phrases and the
  verbal bodies of clauses (frames, exceptions, purposes, clause definiens)
  parse the same role loop, so `When the pump runs at the depot,` carries a
  Location role on the frame clause: channel, source, destination,
  location, and timing are stateable wherever a verb is (why that matters
  to frames is [semantics.md](semantics.md)'s story). In a clause's *subject* or
  a description's predicate, `for`, `from`, `to`, and the rest stay
  ordinary words. A definition's definiens noun phrase is parsed with the
  verb-phrase stop set too (`An export means a transfer to the collector
  via OTLP.`). **Restrictive relatives parse the same verbal tail since
  round 7**: particle, manner, object, and role phrases are all available
  inside `that`/`who` bodies, with roles attaching to the relative's own
  verb (innermost attachment — see the relatives section above).
- **The passive agent is a role since round 5.** In a complemented `be`
  verb phrase (`shall be logged by the daemon`) `by <np-group>` is the
  Agent role; descriptions and copular clause bodies record the same agent
  beside their predicate (`is logged by the daemon`, `when the request is
  submitted by the user,`) and digest it under the same Agent role kind, so
  the deontic passive and the described passive meet at one atom. The stop
  holds through every predicate shape: open words, a prepositional
  predicate's noun phrase, and a comparison's noun-phrase measure all end
  at `by` (`is below the limit by the sensor` records agent `the sensor`,
  never folding it into the phrase). Outside a passive site — including
  after a bare complement-less `be` — role-position `by` is
  `ByOutsidePassive`. In a PLAIN (subject)
  noun phrase `by` remains open-class and folds into modifiers (`the
  standby` keeps its noun); bare `with` does NOT — the round-6 rejection
  of `with` is TOTAL in noun-phrase collection contexts, subject
  positions included (`the file with the flag` is `WithIsAmbiguous`
  everywhere, with `using`, coordination, a relative clause, or a
  backticked `` `with` `` as the rewrites). The surviving `with`
  leave-alone is predicate WORDS only: open-word predicate collection
  (`The pump is with…`) still passes it through as an ordinary word.
- **Locative prepositions end the object.** In verb-phrase position `in`,
  `on`, `at`, `under`, `over`, `above`, `below` stop open-class collection,
  so `store the report in the archive` records object `the report` plus a
  Location role — never an object headed by `archive`. `at` opens a Location
  only when it is not the comparison opener `at least`/`at most`
  (`retain at least 3 copies` stays a quantified object). Verbal clause
  bodies stop at these words too and read them the same way: `When the pump
  runs at the depot,` records a Location role on the clause. (Before round
  3, clauses carried no roles and the leftover locative was rejected.)
- **A `be`-complement locative stays a predicate.** `The account shall be in
  flight mode.` is the prepositional *predicate* form below, not a Location
  role; descriptions (`is below the limit`) are likewise unchanged.
- **Copular clause bodies carry role tails too (round 8 — superseding the
  round-3 restriction this bullet used to state).** `While the pump is
  active at the depot,` digests predicate words `active` plus a structured
  Location role (`at` + `depot`), exactly as the verbal phrasing does —
  and a copular body's passive agent digests as an Agent role. Round 12
  (change 6): a CAPABILITY clause body (`is able to hold the lock`) also
  carries its verb phrase's object digests, so `hold the lock` and `hold
  the token` guards differ in the index, not only in the lossless anchor.

---

## Predicates

A predicate is what descriptions assert, copular clauses state, relative
clauses restrict by, and `be`-complements supply. Three forms are tried in
order:

### 1. Comparisons

A comparison is a closed, machine-checkable atom — the part of a sentence an
SMT solver can consume directly once its measures are grounded:

| Opener | Example |
| --- | --- |
| `greater than <measure>` | `The sales amount is always greater than zero.` |
| `less than <measure>` | `The delay is less than the timeout.` |
| `at least <measure>` | `The retry count is at least the minimum.` |
| `at most <measure>` | `The retry count is at most 3.` |
| `equal to <measure>` | `The account balance shall be equal to zero.` |
| `between <measure> and <measure>` | `The delay is between 5 and 30 seconds.` |

Comparisons parse first, but only on these exact openers: `greater` without
`than` is just an open-class word, and a bare `at` falls through to the
locative form below. In predicate position `at least` / `at most` accept any
measure, including a noun phrase (`at least the minimum`) — unlike the
quantifier determiners, which demand a whole number. `between`'s lower bound
is parsed as a single phrase, never a coordination, so the comparison's own
`and` stays visible; a truncated comparison (`greater than.`) is
`EmptyPredicate`. **Round 9: a DESCENDING numeric `between` is rejected**
(`descending_between`): `between 6 and 4` denotes an empty interval nobody
writes on purpose, so the recognizer tells the author to swap the bounds
instead of freezing an unsatisfiable claim. Equal bounds (a point interval)
and noun-phrase bounds (`between the floor and the ceiling` — value names,
not numbers) pass; the same rule guards the bounded `for` measure
(`for between 30 and 10 days` is rejected too).

### 2. Locative and relational prepositional predicates

One of `in`, `on`, `at`, `below`, `above`, `under`, `over` followed by a
noun-phrase group:

```text
While the engine is running, the temperature is always below the limit.
The sensor is at the door.
```

`at` opens this form only when `at least` / `at most` did not claim it. A
preposition with nothing after it is `EmptyPredicate`.

### 3. Open words

Anything else is a run of open-class words up to the next stop token:
`running`, `frozen`, `authenticated`, `sent`. This is the fallback that keeps
adjectives and participles first-class without a dictionary. An empty run is
`EmptyPredicate`.

### The capability predicate — `able to <vp>`

A fourth predicate form, `Predicate::AbleTo`: the token sequence `able to`
exactly after a copula. **Positional-consistent since round 8 (change
5)**: it parses in a description core (directly after the copula, or —
round 5 — after the description adverb), in a copular CLAUSE body, and in
a copular RELATIVE — the same words no longer mean capability in one
position and an opaque word run in another. It takes a **full verb
phrase** — verb, particle, manner, object, roles:

```text
The client is able to retry.
The client is always able to retry.
The client is never able to retry.
The daemon is able to shut down gracefully within 5 seconds.
While the client is able to retry, the pump shall run.
Each daemon that is able to shut down gracefully shall register.
```

`is never able to <vp>` is a NEGATIVE capability: the adverb composes into
the claim's polarity exactly as a description's `never` does (XOR with a
subject `no`; see [semantics.md](./semantics.md)).

**Bare `able to` only, outside descriptions (legislated, round 8)**:
clause bodies and relatives have no adverb slot, so `while the client is
always able to retry` never reads as capability — the words stay ordinary
predicate material, the `to retry` tail included: predicate collection
resumes flat past the `to` of a trailing `able`, so the tail is never
carved into a Recipient role over a verb (the predicate is the word run
`always able to retry`, with no roles). Guard digests represent the
capability STRUCTURALLY
(`able to` + verb kernel, the verb phrase's manner and roles in their own
slots), so capability descriptions and capability guards meet
shape-for-shape. In `be`-complements `able to …` remains an ordinary
open-word run. An empty
capability (`The client is able to.`) is `EmptyVp`. See
[sentences.md](./sentences.md#description--is--are) for the act it performs
and [semantics.md](./semantics.md) for its behavior denotation.

---

## Measures

A measure — the payload of a comparison, a Deadline, or a Duration — is
either a quantity or a noun phrase standing for a value:

- **Quantity**: a number with an optional unit word. The number is a numeral
  (`5`, `30`, decimals like `5.5` stay one token) or a number word from the
  table (round 12: `zero`–`twenty`, tens `thirty`–`ninety`, `hundred`;
  single words only), and it is **kept exactly as written** — `eleven` is
  stored as the string `eleven`, not converted to `11`. Numeric evaluation
  is a downstream concern; the words remain the source of truth (the
  relation engine grounds the same table, so `within eleven seconds`
  refines `within twelve seconds`). The unit is the
  single following word, when there is one and it is neither a stop word nor
  another number: `5 seconds`, `30 days`, bare `zero`.
- **Noun phrase**: `the limit`, `the timeout` — a value named rather than
  written. Round 12 (fail-closed): after `within`, a BARE word-shaped
  token outside the number table is `UnknownNumberWord` (`within eleventy
  seconds` no longer becomes a measure that never grounds) — a
  determiner-led value name (`within the timeout`) is untouched.
- **Bounded quantity** (round 6, under `for` ONLY): a comparison operator
  over a quantity — `for at least 30 days`, `for at most 5 seconds`, `for
  greater than 3 days`, `for less than 2 hours`, `for between 5 and 10
  seconds`. `within` keeps the plain quantity: a deadline already means an
  upper bound, so a bound opener after `within` is REJECTED
  (`WithinTakesPlainMeasure`, round 6 follow-up — it used to be silently
  consumed as a counted noun-phrase measure, `at least 5` of `seconds`,
  that never grounds an interval).
  `for equal to 5 seconds` has no reading — `for 5 seconds` already says
  it. A `between` bound shares ONE unit, written after either number
  (`for between 5 seconds and 10 seconds` renders canonically as `for
  between 5 and 10 seconds`); two written units that disagree are
  rejected.

A unit attaches to the measure it follows, and only that measure:
in a comparison predicate, `between 5 and 30 seconds` has no unit on `5`
and `seconds` on `30`; write `between 5 seconds and 30 seconds` to give
each bound its own unit.

---

## Negation sites

Negation is legal in exactly three places, and `not` is a reserved word
everywhere, so it can never hide inside an open-class run:

| Site | Form | Scope |
| --- | --- | --- |
| after a binding or recommending modal | `shall not` / `must not` / `should not` | the whole verb phrase |
| the description adverb slot | `is never` / `are never` | the described state |
| a noun-phrase determiner | `no` | the noun phrase it determines |

```text
The daemon shall not store derived views.
The temperature is never above the limit.
When no OTLP endpoint is configured, the tracing library should default
OTLP HTTP export to http://192.168.10.4:4318.
```

Because each site is fixed by the grammar, what a negation covers is decided
syntactically — polarity is read off the tree, never scanned for. That is
why the two floating forms are rejected rather than guessed at:

- `may not` is `AmbiguousModal`: English cannot decide between "is permitted
  not to" and "is not permitted to". Write `shall not` for a prohibition.
- a subject `no` under `may` is `NoWithMay`: `No client may retry.` is a
  denial of permission — a prohibition, not the record of an admissibility.
  Write `The client shall not retry.` The subject `no` composes into the
  claim's polarity for every other act; under `may` there is no negative
  admissibility for it to produce.
- `is not` / `are not` is `NegatedDescription`: a description is negated in
  the adverb slot. Write `never`, or `shall not` if an obligation was meant.

`always` occupies the same description slot as `never` and strengthens
without negating. Outside that slot — inside a frame clause's predicate, for
instance — `never` and `always` are ordinary open-class words carried in the
predicate's word list, with no negation reading.

---

## The phrase depth bound

`of`-links, relative clauses, and `before`/`after` clauses are the phrase
grammar's recursion: each `of` steps one level down, each relative body may
contain noun phrases of its own, and a `before`/`after` role nests a full
clause that may itself carry `before`/`after` roles. Recursion depth is
therefore proportional to input length, and an adversarial chain a few
thousand levels deep (`x of x of x of …`, `x y after x y after …`) would
overflow the stack — an abort, not an error, and a hole in the total
recognizer.

The recognizer therefore bounds phrase nesting at **64 levels**. Input beyond
the bound is rejected with `PhraseTooDeep`, which names the limit:

```text
the phrase nests too deeply: more than 64 levels of `of` phrases, relative clauses, or `before`/`after` clauses
```

The bound is a totality guarantee, not a stylistic limit: no sentence a
person writes nests anywhere near 64 levels, and everything unbounded in
honest input — coordination width, role-phrase count, frame count, sentence
count — is iterative in the recognizer and unaffected. With the bound in
place, every input, however deep, gets exactly one tree or exactly one
precise error.

---

## See also

- [errors.md](./errors.md) — the full rejection taxonomy, including
  `MixedCoordination`, `QuantifierNotWhole`, `EmptyPredicate`, and
  `PhraseTooDeep`.
- [semantics.md](./semantics.md) — the interpretations derived over these
  structures, including the definite-reference analysis that reads the
  `a`/`an` vs. `the` distinction.
- [README.md](./README.md) — the index of the grammar reference.
