# Examples cookbook

> Part of the [grammar reference](./README.md).

A skimmable gallery of specifications the [total
recognizer](./README.md#philosophy-a-total-recognizer) accepts, followed by the
constructions it deliberately rejects and their canonical rewrites. Every
accepted example below parses today: the core of the gallery is the acceptance
corpus in [`so_lang/tests/corpus.rs`](../../so_lang/tests/corpus.rs), held
green as the grammar evolves, and the remainder is verified directly against
the recognizer. Every rejected example names the exact `ParseError` kind the
code returns. For the rules behind the examples, follow the links to
[sentences.md](./sentences.md), [phrases.md](./phrases.md), and
[errors.md](./errors.md).

## The six speech-act cores

One accepted sentence per act. The pivot word decides the core; see
[sentences.md](./sentences.md#the-pivot-decides-the-core).

| Input | Speech act | What the tree records |
| --- | --- | --- |
| `A session means a sequence of requests from one client.` | Definition | term `session`; definiens noun phrase `a sequence of requests` with a Source role `one client` |
| `A timeout means that the request expires.` | Definition | `means that` forces the clause definiens (verb `expires`); without `that`, the deterministic NP reading applies |
| `The retry count is at most 3.` | Description | comparison `AtMost` over the quantity `3` |
| `The pump shall stop.` | Obligation | subject `pump`, verb `stop`, no object |
| `The daemon shall not store derived views.` | Prohibition | a deontic core with `negated: true` |
| `The tracing library should install TraceContext and Baggage propagators.` | Recommendation | coordinated `and`-object of two noun phrases |
| `The client may retry.` | Permission | admissibility, not requirement |

Two description variants worth having on hand:

| Input | Notes |
| --- | --- |
| `The sales amount is always greater than zero.` | `always` fills the adverb slot; `greater than zero` is a comparison, with the number word `zero` kept as written |
| `Requests are logged.` | bare-plural subject (no determiner), `are` copula, open-word predicate |
| `The client is able to retry.` | **capability**: `able to` after the copula — directly, or after the `always`/`never` adverb (round 5) — takes a full verb phrase; a description on the surface (no force), denoting behavior through that verb phrase. `The client is always able to retry.` is likewise a capability with the adverb kept, and `is never able to retry` is a negative capability (the adverb composes with a subject `no` exactly like a description's `never`) — see [sentences.md](./sentences.md#description--is--are) |

### Verb-phrase alternatives (round 6)

```text
The server shall either accept the request or reject the request.
The client may either retry or abort.
```

One sentence, one claim, a genuine disjunction: splitting into two `shall`
sentences would oblige BOTH. `either` is required, `or` only, deontic cores
only; see
[phrases.md](./phrases.md#alternatives--either-vp-or-vp-round-6).

## Circumstance frames

One accepted sentence per frame kind. Frames lead the sentence in canonical
order — `Where`, then `While`, then at most one `When`/`If` trigger; see
[sentences.md](./sentences.md#circumstance-frames--where--while--when--if).

| Input | Frame | Notes |
| --- | --- | --- |
| `where the premium plan is enabled, a workspace means a shared folder.` | `Where` (configuration scope) | the only frame a definition admits; surface casing `where` is preserved in the tree |
| `While the engine is running, the temperature is always below the limit.` | `While` (state scope) | a framed description; `below the limit` is a prepositional predicate |
| `When the order is submitted, the system shall record the total.` | `When` (event trigger) | the frame clause is copular: `the order` + `is` + `submitted` |
| `If the balance is negative, then the account shall be frozen.` | `If` (contingency trigger) | `then` is optional on input — the tree is identical without it — and always re-emitted on render |
| `While the engine is running, when the temperature exceeds the limit, the controller shall open the valve.` | `While` + `when` stacked | canonical order; the trigger clause is verbal (`exceeds` + object `the limit`); the lowercase `when` is kept as written |
| `When the order ships and the payment is cleared, the system shall issue the receipt.` | `When` with a **joint guard** | one trigger frame, two coordinated clauses: ONE event (`ships`) plus a state read at its instant (`is cleared`). Two events under `and` (`When the order ships and the payment clears,`) are rejected as `multiple_event_conjuncts` — conjunction of occurrences is simultaneity, which has no single reading. Rewrite the second event as a state (`is/are/remains …`) or move it to a `While` frame (`While the payment clears, when the order ships, …`). `or` groups are exempt: a disjunction of events is alternation — either occurrence triggers — which is well-defined |
| `While the pump runs or the valve is open, the system shall alert the operator.` | `While` with an **alternative guard** | one state frame, either condition suffices; mixing `and`/`or` in one frame is `mixed_coordination` |
| `When the pump and the valve are open, the system shall alert the operator.` | `When`, one clause | noun-phrase coordination, not clause coordination: `the pump` alone is no clause, so this is a single clause with a coordinated subject |

## Thematic roles

Role prepositions are closed only after a verb — in verb phrases and (since
round 3) in the verbal bodies of frame, exception, purpose, and definiens
clauses; each one fixes a role in the tree. See
[phrases.md](./phrases.md#thematic-roles).

| Input | Roles recorded |
| --- | --- |
| `The gateway shall send the receipt to the customer via TLS.` | Recipient `the customer`, then Means `TLS` (marker `via` preserved), in surface order |
| `The system shall notify the operator about the failure.` | Topic `the failure` |
| `When an order is submitted, the system shall record the order within 5 seconds.` | Deadline: quantity `5` with unit `seconds` |
| `The service shall retain the log for 30 days.` | Duration: quantity `30` with unit `days` |
| `The service shall retain the log for at least 30 days.` | **bounded Duration** (round 6): `at least 30 days` — also `for at most 5 seconds`, `for between 5 and 10 seconds`; `for`-only — `within` keeps the plain quantity, and a bound opener after `within` is rejected (`within_takes_plain_measure`, round 6 follow-up) |
| `The service shall copy the record from the queue into the archive.` | Source `the queue`, Goal `the archive` |
| `When no OTLP endpoint is configured, the tracing library should default OTLP HTTP export to http://192.168.10.4:4318.` | Recipient whose head is the URL, kept verbatim; the frame clause's subject carries the determiner `no` |
| `A session means a sequence of requests from one client.` | a definiens takes roles too: Source `one client` |
| `The system shall store the report in the archive.` | Location `the archive` (preposition `in` kept as written); the object is `the report` — the locative never folds into it |
| `The pump shall run at the depot.` | Location with `at`; `at least` / `at most` always stay comparisons (`The retry count is at most 3.`) |
| `When the pump runs at the depot, the system shall stop.` | clause roles: the Location attaches to the frame clause's verb, so guard conditions can state channel, source, destination, location, and timing |
| `When the payment clears after the order ships, the system shall issue the receipt.` | **the sequence pattern**: the trigger stays ONE event (`the payment clears`); its After role nests the ordering clause (`the order ships`). Conjoining two events stays rejected (`multiple_event_conjuncts`) |
| `The pump shall run until the tank is empty.` | Until: the companion of `before`/`after` — the same nested clause parsing and the same depth accounting; the behavior holds up to the clause's occurrence |
| `While the daemon runs until the queue drains, the light shall glow.` | `until` attaches inside guard clauses too, like every clausal role |
| `The request shall be logged by the daemon.` | **Agent** (round 5): `by` after `be <predicate>` records the passive agent; `The request is logged by the daemon.` digests to the same atom |
| `When the request is submitted by the user, the daemon shall log the request.` | a copular guard clause records its agent too (predicate `submitted`, agent `the user`) |
| `The system shall notify the user after the backup completes using email.` | **temporal-clause INNER attachment (fixed, deterministic)**: the temporal clause consumes everything to its right, so the Means role belongs to the INNER clause — the BACKUP completes using email. Not what you meant? See the next row |
| `The system shall notify the user using email after the backup completes.` | the OUTER reading of the same words: Means `email` on `notify`, then the After clause. The two spellings mean different things and the reading is fixed by position, never guessed ([phrases.md](./phrases.md#thematic-roles)) |

## Content complements and role-bearing relatives (round 7)

| Input | Reading |
| --- | --- |
| `The server shall ensure that the token is valid.` | **content complement**: `that <clause>` directly after the verb — the clause is what the ensuring is about, digested into the atom with full fidelity |
| `The system shall verify within 5 seconds that the token is valid.` | roles precede the content — content is FINAL and consumes the rest of the phrase |
| `The server shall either ensure that the token is valid or reject the request.` | content complements work inside alternative items (legislated) |
| `The daemon shall record the fact that carries the flag.` | after a NOUN, `that` is that noun's restrictive relative — the existing rule wins; `record the fact that the token is valid` is rejected (`determiner_as_verb` on `the`: the relative reading has no verb after `the token` — round 9's object-gap needs one) rather than silently re-read as content |
| `Each request that arrives from the gateway shall be logged.` | **role-bearing relative** (round 7): the relative body is the full verbal tail, so the Source role restricts the REQUEST |
| `The daemon shall close the session that holds the lock in the vault.` | roles after a relative's object attach to the RELATIVE's verb — innermost attachment, legislated: the HOLDING is in the vault. For the outer reading, move the restriction into a frame: `While the session holds the lock, the daemon shall close the session in the vault.` |

## Copular role tails and positional capability (round 8)

| Input | Reading |
| --- | --- |
| `While the pump is active at the depot, the daemon shall wait.` | **copular role tail**: the guard predicate is `active` with a structured Location role — no longer flat words |
| `When the request is submitted by the user within 5 seconds, the daemon shall log the request.` | agent immediately after the predicate (round-5 shape), then the role tail — an agent AND a Deadline in one guard |
| `When the record is stored in the archive by the daemon, the auditor shall sign the record.` | a `by` later in the tail is the Agent ROLE (a copular body is a passive site); both agent spellings digest to one Agent role |
| `The request is logged by the daemon within 5 seconds.` | a DESCRIPTION's role tail after its passive agent (round 8 follow-up): Agent `the daemon` plus a structured Deadline — meets `The request shall be logged by the daemon within 5 seconds.` at one atom. Agentless descriptions keep the plain predicate reading |
| `While the client is always able to retry, the pump shall run.` | adverbed able-to outside a description is NEVER capability (bare-only legislation) — and the whole tail stays flat predicate words (`always able to retry`, no roles): the `to retry` is not carved into a Recipient role |
| `Each request that is signed by the user shall be logged.` | copular relatives mirror the clause shape: the agent restricts the request |
| `Each request that is valid within 5 seconds shall be logged.` | a role tail on a copular relative — innermost attachment |
| `The system shall verify that the token is valid within 5 seconds.` | the inner deadline is a STRUCTURED Deadline inside the content clause (attachment stays inner; write `verify within 5 seconds that …` for the outer reading) |
| `While the client is able to retry, the pump shall run.` | **positional capability**: `able to <vp>` after the copula is `Predicate::AbleTo` in clause bodies too — bare form only (clauses have no adverb slot) |
| `Each daemon that is able to shut down gracefully shall register.` | capability in a copular relative, with the verb phrase's particle and manner intact |

## Object-gap relatives and guard content (round 9)

| Input | Reading |
| --- | --- |
| `Each request that the gateway forwards shall be logged.` | **object-gap relative**: the request is the missing OBJECT of `forwards`; the gap opens only when a determiner/quantifier-led phrase follows `that`/`who` (superseding the round-7 `determiner_as_verb` rejection of this sentence) |
| `Each user who the auditor flags shall be reviewed.` | the `who` form of the gap |
| `Each packet that the router sends out via the tunnel within 5 seconds shall be counted.` | the gap tail carries particle, manner, and roles — innermost attachment, like every relative |
| `Each request that the gateway forwards the packet shall be logged.` | REJECTED (`determiner_as_verb`): an explicit determiner-led object after the gap's verb means the head is not the missing object — not a gap |
| `Each daemon that emits telemetry data shall be sampled.` | a BARE phrase after `that` never opens a gap (legislated): verb `emits`, object `telemetry data` — the round-7 subject-gap reading wins |
| `When the monitor ensures that the token is valid, the pump shall stop.` | **guard content** (round 9, revising the round-7 frames-content-free legislation): a verbal clause body takes the same final `that <clause>` a verb phrase does |
| `The pump shall stop, unless the monitor reports that the link is down.` | content in an exception clause |
| `While the pump runs until the monitor confirms that the tank is full, the daemon shall wait.` | content nests through clausal roles, under the one depth budget |
| `The daemon shall purge the cache after no backup completes.` | the nested clause keeps its polarity in the digest (round 8): never confused with `after the backup completes` |

## Particle verbs

The closed particle list is `out`, `down`, `up`, `off`: immediately after a
verb (other than `be`), the word is the verb's particle, and the semantic
atom is verb + particle. See [phrases.md](./phrases.md#verb-phrases).

| Input | Reading |
| --- | --- |
| `The session shall time out within 30 seconds.` | verb `time`, particle `out`, Deadline `30 seconds` |
| `While the operator shuts down the server, the daemon shall wait.` | frame clause with verb `shuts`, particle `down`, object `the server` |
| `When the user logs out, the session shall end.` | verb `logs`, particle `out` — no longer a bare `out` object |
| `The crane shall lift the beam up.` | a particle trailing the object joins the verb: atom `lift up`, object head `beam` (canonical render `lift up the beam`); write `the warm-up` (hyphenated) for a noun spelled like a particle |
| `The daemon shall log `out`.` | backticks defuse the particle: object `` `out` `` |
| `The user shall log-in.` | `in`/`on` are NOT particles (they open Location roles); hyphenation stays the workaround |
| `The pump shall run out of water.` | rejected (`unexpected_tokens` on `of`): a particle never combines with a following `of` — there is no `out of` chain |

## Boundary-less verbal guards fail closed (round 11)

A boundary-less guard clause — no determiner, locative, or role
preposition after the subject's own — whose trailing bare-word run has
**two or more** words after the minimal subject (and a verb-capable first
run word) is the **genuinely ambiguous class**: it admits both the
minimal-subject SVO reading (round 10) and the long-subject final-word
reading (round 3), and no lexicon-free rule can pick the intended one.
Round 11 rejects the class (`ambiguous_verb_boundary`) instead of
scrambling either way; one-word runs keep the round-3 verb-only reading.
See [reference.md §3.3](./reference.md#33-verbal-clause-verb-selection).

| Input | Reading |
| --- | --- |
| `When the client sends telemetry, the daemon shall persist the Node.` | **rejected** (`ambiguous_verb_boundary`): SVO reads verb `sends`, final-word reads verb `telemetry` — write `sends the telemetry` |
| `When the client sends the telemetry data, the pump shall stop.` | the rewrite: the determiner is the boundary — verb `sends`, object `the telemetry data` |
| `When a session expires, the system shall close the session.` | one-word run: verb `expires`, no object — unchanged |
| `When the user logs out, the session shall end.` | the particle pop leaves a one-word run (outside the class): verb `logs`, particle `out` — unchanged |
| `When the client sends telemetry out, the fan shall run.` | **rejected** (`ambiguous_verb_boundary`): popping the particle must not reopen the frontier — the run before `out` is the ambiguous class; write `sends the telemetry out` |
| `When the counter reaches stage zero, the system shall reset.` | **rejected** (`ambiguous_verb_boundary`): same for a bare-number final — `the counter reaches zero` stands, `reaches stage zero` does not; put a determiner on the object (`reaches the stage zero`) to make the boundary provable |
| `When the client quickly sends telemetry, the fan shall run.` | **rejected** (`ambiguous_verb_boundary`): a pre-verbal manner word is skipped, not frontier-closing — the run measures `sends telemetry` and fails closed like the manner-less twin |
| `When the monitor confirms that the client sends telemetry, the fan shall run.` | **rejected** (`ambiguous_verb_boundary`): the content clause is the ambiguous class and the rejection is FINAL — never re-read as an object-gap relative subject; write `confirms that the client sends the telemetry` |
| `When the temperature sensor fails, the pump shall stop.` | **rejected** (`ambiguous_verb_boundary`): SVO scrambled it (verb `sensor`), final-word read verb `fails` — write `the sensor of the temperature fails` or `… sensor fails at the depot` |
| `When the backup daemon sends telemetry, the fan shall run.` | **rejected** (`ambiguous_verb_boundary`): the round-10 SVO trade put every word in a wrong slot here — write `sends the telemetry` to keep the full subject `the backup daemon` |
| `When the client sends telemetry to the admin, the fan shall run.` | **the boundary flip, unchanged**: a role preposition is a boundary (step 1 outranks the fail-closed rule), so this reads subject `the client sends`, verb `telemetry`, recipient `admin`; give the object a determiner — `sends the telemetry to the admin` — to keep verb `sends` under a role |

## Manner adverbs

The controlled manner slot: a bare `-ly` word in post-verbal position — where
an object or a role phrase would start — is a manner adverb, never an object
or a verb. Inside a noun phrase, `-ly` words are untouched. See
[phrases.md](./phrases.md#verb-phrases) and
[lexical.md](./lexical.md#reserved-words-vs-open-words).

| Input | Reading |
| --- | --- |
| `The pump shall stop immediately.` | verb `stop`, manner `immediately` — no longer a bare `immediately` object |
| `When the export completes successfully, the daemon shall archive the export.` | frame clause verb `completes`, manner `successfully` — the clause verb heuristic prefers a non-`-ly` verb |
| `When the peers reply, the server shall log the message.` | an `-ly`-final English VERB is still writable: when stripping the trailing `-ly` word leaves no parseable subject and verb, the heuristic backs off and `reply` is the verb (`the peers reply quickly` keeps verb `reply`, manner `quickly`) |
| `The daemon shall shut down gracefully within 5 seconds.` | manner composes with the particle and roles: verb `shut`, particle `down`, manner `gracefully`, Deadline `5 seconds`; a particle reached across the manner run still joins the verb (`shut gracefully down` = `shut down gracefully`) |
| `The system shall log only the errors.` | the rule is purely morphological: the focus adverb `only` is swept into the manner slot; write `` log `only` the errors `` to keep it an ordinary word |
| `The daemon shall stop immediately gracefully.` | juxtaposed manner words extend the run; a conjunction ends it, so `stop quickly and safely` is rejected (`unexpected_tokens` on `and`) |
| `The system shall verify the assembly.` | inside a noun phrase, `-ly` words are untouched: `the assembly` stays an object, `the nightly build` keeps `nightly` as a modifier, `exactly 7 copies` keeps its quantifier |
| `The system shall record `` `supply` ``.` | **the documented tradeoff**: a bare `-ly` word meant as a noun object needs backticks — without them, `record supply` reads `supply` as manner |

## Quantifiers, determiners, relatives

| Input | Notes |
| --- | --- |
| `Each request shall be logged.` | determiner `Each` preserved; `be` takes the complement `logged` — the passive-voice obligation |
| `The cluster shall keep at least 3 replicas.` | `at least 3` is a counting quantifier, stored as the value `3` |
| `Each request that carries a token shall be logged.` | restrictive relative `that carries a token` inside the subject |
| `The user who is authenticated may open the session.` | copular relative with `who`; the relative's `is` does not end the subject |
| `The user of the workspace who is active shall confirm the change.` | **`who` attaches to the chain ROOT** (round 5): the relative restricts the USER, not the workspace |
| `The user of the workspace that is active shall confirm the change.` | **`that` attaches to the NEAREST head**: the relative restricts the WORKSPACE — the pair gives both attachments a spelling |
| `Both the pump and the valve shall stop.` | marked coordination in subject position: `both` pairs with `and` over exactly two items |
| `Either the cache or the database shall answer.` | `either` pairs with `or` |
| `The system shall record the `` `will` ``.` | the backtick escape hatch: a backticked token is always open-class, kept verbatim (head `` `will` ``); bare `will` stays reserved |
| `The `` `while` `` loop shall terminate.` | a backticked frame keyword as a modifier |

## Comparisons

Comparisons are closed, machine-checkable predicate atoms; see
[phrases.md](./phrases.md#predicates).

| Input | Comparison |
| --- | --- |
| `The sales amount is always greater than zero.` | `GreaterThan`, value `zero` (the word, kept as written) |
| `The retry count is at most 3.` | `AtMost`, value `3` |
| `The retry count is at least the minimum.` | `AtLeast` over a noun-phrase measure — a value named, not written |
| `The delay is between 5 and 30 seconds.` | `Between`; the unit `seconds` attaches only to the upper bound `30` |

## Exception and purpose

The trailing adjuncts: at most one `unless` carve-out, then at most one
purpose, each opened by a top-level comma. See
[sentences.md](./sentences.md#the-exception--unless).

| Input | Notes |
| --- | --- |
| `The pump shall stop, unless the override is active.` | the exception clause lands in `Sentence::exception` |
| `The daemon shall persist the node, so that the auditor traces the decision.` | `so that` takes a full clause — in the present tense (see the rewrite table below) |
| `The system shall log each request, in order to preserve the audit trail.` | `in order to` takes a verb phrase |
| `The pump shall stop, unless the override is active, so that the operator retains control.` | both adjuncts, in their one legal order: exception before purpose |

## Multi-sentence specifications and coreference

A specification is one or more sentences; the input splits at word-final
periods, and each sentence gets its own tree (and, downstream, its own node).
Definite references are resolved across the whole specification by
[`semantics::references`](./semantics.md#definite-references):

```text
A session means a sequence of requests. When a session expires, the system
shall close the session.
```

- Two sentences: a definition, then a framed obligation.
- `the system` → **Unresolved**: no earlier `a system` — deixis to the system
  under specification, not an error.
- `the session` → **Unique**, resolving to the most recent introduction of the
  head `session`: the second sentence's own `a session` (frames are read
  before the core), not the first sentence's term. Same-head introductions
  deduplicate — they are the same term.

Only `a`/`an` introduce and only `the` refers; matching is by exact head word.

## Rejected → rewritten

The recognizer rejects every construction with more than one natural reading,
and each rejection names its rewrite. Every input below returns exactly the
error kind shown; every rewrite parses.

| Written | Error kind | Canonical rewrite |
| --- | --- | --- |
| `The client may not retry.` | `ambiguous_modal` | `The client shall not retry.` |
| `No client may retry.` | `no_with_may` | `The client shall not retry.` — a denial of permission is a prohibition |
| `The client can retry.` | `unsupported_modal` | `The client may retry.` for permission, `The client shall retry.` if required — or, when ability really was meant, the faithful rewrite `The client is able to retry.` |
| `The tracing library should default export to X when no endpoint is configured.` | `mid_sentence_frame` | `When no endpoint is configured, the tracing library should default export to X.` |
| `The pump shall stop unless the override is active.` | `mid_sentence_frame` | `The pump shall stop, unless the override is active.` |
| `The sales amount is not greater than zero.` | `negated_description` | `The sales amount is never greater than zero.` — or `The sales amount shall not be greater than zero.` if an obligation was meant |
| `When the order ships, if the payment fails, the system shall alert the operator.` | `multiple_triggers` | one trigger frame with a joint guard: `If the payment fails and the order is shipped, then the system shall alert the operator.` — one event, the other circumstance as a state. Splitting into two sentences would CHANGE the meaning (each would fire alone) |
| `When the order ships and the payment clears, the system shall issue the receipt.` | `multiple_event_conjuncts` | keep one event and write the other as a state: `When the order ships and the payment is cleared, …` — or move it to a `While` frame: `While the payment clears, when the order ships, …` |
| `The system shall record the total and the tax or the fee.` | `mixed_coordination` | one conjunction throughout — `The system shall record the total and the tax.` — or one sentence per claim: `The system shall record the total. The system shall record the tax or the fee.` |
| `The daemon shall persist the node, so that the auditor shall trace the decision.` | `unexpected_tokens` (on `shall`) | present tense in the purpose: `The daemon shall persist the node, so that the auditor traces the decision.` |
| `The daemon shall listen for requests.` | `for_requires_measure` | a duration takes a quantity (`for 5 seconds`); for a topic write `The daemon shall listen about requests.` — better, name the event: `The daemon shall wait until a request arrives.` |
| `The daemon shall notify the user with the report.` | `with_is_ambiguous` | instrument: `The daemon shall notify the user using the report.` — accompaniment: coordinate, `The daemon shall send the report and the notice to the user.` |
| `The file with the flag shall be archived.` | `with_is_ambiguous` | (round 6) restrict with a relative clause: `The file that carries the flag shall be archived.` — or an `of`-chain; backtick `` `with` `` for noun uses of the word itself |
| `The server shall not either accept the request or reject the request.` | `negated_alternatives` | (round 6) two prohibitions: `The server shall not accept the request. The server shall not reject the request.` |
| `The daemon shall respond by Friday.` | `by_outside_passive` | a deadline is `within`: `The daemon shall respond within 5 days.` — `by` is only the passive agent (`shall be logged by the daemon`) |
| `When the client sends telemetry, the daemon shall persist the Node.` | `ambiguous_verb_boundary` | (round 11) put a determiner on the object: `When the client sends the telemetry, …` — for a long subject use an of-chain (`When the sensor of the temperature fails, …`) or a role boundary (`When the temperature sensor fails at the depot, …`) |
| `The latency is between 6 and 4.` | `descending_between` | (round 9) a descending numeric `between` is an empty interval nobody means: swap the bounds — `between 4 and 6`. Equal bounds and noun-phrase bounds are fine; the same rule covers `for between 30 and 10 days` |

Why each is refused:

- **`may not`** — English cannot decide between denial of permission ("is
  permitted not to") and prohibition ("is not permitted to"). The grammar
  refuses to pick; `shall not` says prohibition unambiguously. A subject
  `no` under `may` (`No client may retry.`) is the same family: a denial of
  permission that would otherwise ingest as the very permission its author
  denied (the grammar has no negative admissibility) — rejected as
  `no_with_may`, with the same rewrite.
- **`can`** — the word blurs ability into permission, so it has no single
  machine-checkable meaning at the pivot. The message names the four
  supported modals (`shall`, `must`, `should`, `may`) and — since round 4 —
  the faithful target for genuine ability: the capability description
  `is able to <response>` (see [sentences.md](./sentences.md)). `will`,
  `would`, `could`, `might`, and `ought` are rejected the same way, and all
  six words are reserved everywhere, so they can be diagnosed at pivot
  position.
- **Trailing conditions** — frames lead the sentence, always. A frame keyword
  after the pivot (`when`, `while`, `if`, or a comma-less `unless`) is
  `mid_sentence_frame`; move the condition to the front, or restore the
  exception's comma.
- **`is not` / `are not`** — a description's only negation site is the adverb
  slot: `never` has a syntactically fixed scope where a floating `not` does
  not. (`no` on a noun phrase and `not` after `shall`/`must`/`should` are the
  other two negation sites; see
  [phrases.md](./phrases.md#negation-sites).)
- **Two triggers** — two trigger *frames* have no single reading: at once? in
  sequence? within some window? State the joint condition inside ONE frame
  with clause coordination: `When the order ships and the payment is
  cleared, …` — one event, the other conjuncts as states read at its instant
  (`or` = any one alternative; one conjunction per frame). The same ambiguity
  inside one frame — two events under `and` — is `multiple_event_conjuncts`.
  Do NOT split a joint guard into separate sentences — each sentence would
  fire on its own trigger, which asserts something weaker and different.
- **Mixed `and`/`or`** — one coordination, one conjunction. Pick one, split
  into separate sentences, or — in subject position — disambiguate with the
  marked forms `both … and …` / `either … or …` over exactly two items.
- **Modals in purposes** — a `so that` clause states an outcome, not a nested
  requirement, so it has no modal slot: `shall`, `can`, and the rest are
  rejected as stray material where the clause's verb belongs. Write the
  outcome in the present tense (`the auditor traces the decision`); if the
  purpose really is a requirement of its own, it is its own sentence.
- **`for` / `with` / `by` at role positions (round 5)** — an
  accepted-but-wrong tree is worse than a rejection. `for` without a
  quantity used to silently parse `listen for requests` as a duration over
  a noun phrase; `with` used to be swallowed into the object; `by` used to
  fold into predicate words. Now: a duration requires a quantity
  (`for_requires_measure`), `with` is refused outright — instrument is
  `using`, accompaniment is coordination (`with_is_ambiguous`) — and `by`
  is admitted exactly once, as the passive agent after `be <predicate>` or
  a description's/copular clause's predicate (`by_outside_passive`
  elsewhere). Round 6 extends the `with` discipline into EVERY noun
  phrase, subject positions included: `the file with the flag` used to pin
  the head to `flag` — the same accepted-but-wrong family — and now
  rejects with the same error; the supported restriction forms are the
  `of`-chain and the relative clause.
- **`not` over `either … or …` (round 6)** — negated alternatives have two
  readings ("neither" vs "not obliged to choose"), so the combination is
  refused at ingest (`negated_alternatives`). Two prohibition sentences
  state the "neither" reading exactly, with no scope ambiguity.

For the full error taxonomy — every variant, its exact message, and its stable
`kind()` name — see [errors.md](./errors.md).

## See also

- [sentences.md](./sentences.md) — the sentence layer the accepted examples
  instantiate.
- [phrases.md](./phrases.md) — noun phrases, verb phrases, predicates,
  measures.
- [lexical.md](./lexical.md) — sentence splitting, tokenization, casing,
  multibyte safety.
- [semantics.md](./semantics.md) — the interpretations derived over these
  sentences.
