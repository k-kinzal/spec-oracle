# The sentence layer

> Part of the [grammar reference](./README.md).

A **specification** — the unit [`parse`] returns — is one or more sentences.
Each **sentence** performs exactly one specification act: it defines a term,
describes the system, or obliges, forbids, recommends, or permits behavior.
Around that act, a sentence may carry leading **circumstance frames**, one
trailing **exception**, and one trailing **purpose**:

```text
[frames] <core> [, unless <clause>] [, so that <clause> | , in order to <verb phrase>] [.]
```

The input is split into sentences at word-final periods (see
[lexical.md](./lexical.md)); the final period is optional. Each sentence keeps
its exact input slice in `Sentence::source` — the raw words remain the source
of truth; the tree is their structure. `Sentence::render` reproduces the
sentence in canonical form: frame keywords title-cased, closed-class words
lowercase, `If …, then …`, single spaces, a trailing period.

After the frames, **every top-level comma opens an adjunct segment**, and each
segment must begin with `unless`, `so that`, or `in order to` — at most one
exception, then at most one purpose, in that order. A comma anywhere else in
the core is rejected as `unexpected_tokens`. The internal grammar of the
clauses and phrases named below — noun phrases, verb phrases, predicates —
is the [phrase grammar](./phrases.md).

---

## The pivot decides the core

The **speech-act core** is chosen by one word. The subject noun phrase is
parsed left to right and stops at the first top-level **pivot** — `shall`,
`must`, `should`, `may`, `is`, `are`, or `means` — and that pivot fixes the
core's kind. Because the choice is a single closed-class word in a fixed
position, every sentence performs exactly one act and has exactly one reading.

| Pivot | Speech-act core | AST |
| --- | --- | --- |
| `means` | definition | `Core::Definition { term, definiens }` |
| `is` / `are` | description | `Core::Description { subject, copula, adverb, predicate }` |
| `shall` / `must` | obligation (`not`: prohibition) | `Core::Deontic { modal: Shall\|Must, negated, .. }` |
| `should` | recommendation | `Core::Deontic { modal: Should, negated, .. }` |
| `may` | permission | `Core::Deontic { modal: May, negated: false, .. }` |

A pivot inside a relative clause does not end the subject: in `The account
that is frozen is never active.`, the first `is` belongs to `that is frozen`
and the second is the sentence's pivot. A sentence with no pivot is rejected
as `missing_pivot`; a pivot with nothing before it, as `empty_subject`.

---

## Definition — `means`

```text
<term> means <definiens>.
```

A definition establishes vocabulary: it says what a term stands for, and
asserts nothing about behavior.

| Slot | Content | AST |
| --- | --- | --- |
| `<term>` | one noun phrase | `Core::Definition { term: Np, .. }` |
| `<definiens>` | a noun phrase with optional thematic-role phrases, or a full clause | `Definiens::Np { np, roles }` / `Definiens::Clause(Clause)` |

```text
A session means a sequence of requests from one client.
A valid token means the signature is correct.
A timeout means that the request expires.
where the premium plan is enabled, a workspace means a shared folder.
```

- **The term is a single noun phrase.** A coordinated term (`A pump and a
  valve means …`) has no single definition, so the conjunction is rejected
  (`unexpected_tokens` on the `and`/`or`).
- **`means that <clause>` forces the clause reading.** An explicit `that`
  right after `means` makes the definiens a full clause (verbal or copular)
  over the rest of the core: `A timeout means that the request expires.`
  parses as `Definiens::Clause` with verb `expires`. The canonical render of
  a clause definiens **always** carries the marker, so a copular definiens
  parsed without `that` renders with it and re-parses to the same tree.
- **Without `that`, the definiens reading is deterministic and unchanged.**
  When it contains a clause copula (`is` / `are` / `remains`) it is a clause;
  otherwise the noun-phrase reading is tried first, falling back to a verbal
  clause. With open-class words opaque, `a shared folder` and `the request
  expires` are the same shape (determiner, word, word), so one reading has to
  win — the noun-phrase one does, and `A timeout means the request expires.`
  parses as an NP definiens (a knowing misread; write `means that` to get the
  clause).
- `means` with nothing after it — including a bare `means that` — is rejected
  as `empty_definiens`.

**Why `is` is never a definition.** In prose, `X is Y` can either describe X
or define it, and the reader guesses from context. This grammar does not
guess: each pivot performs one act, and `is` is claimed by the description.
A sentence that creates vocabulary must say `means`; a sentence that says
`is` always asserts how the system is. The two acts are also checked
differently — a description is a claim the system can violate, a definition
is not — so leaving the choice to context would make every `is`-sentence
ambiguous in exactly the way the language exists to prevent.

Definitions are **timeless**: only `Where` frames may scope them (see
[frames](#circumstance-frames--where--while--when--if) below).

---

## Description — `is` / `are`

```text
<subject> is|are [always|never] <predicate> [by <agent>].
```

A description states how the system is — an invariant — with no deontic
force. It maps to
`Core::Description { subject, copula, adverb, predicate, agent }`:
the copula (`Copula::Is` / `Copula::Are`) is kept as written, the optional
adverb is `DescriptionAdverb::Always` or `::Never`, the predicate is a
comparison, a prepositional predicate, or open-class words (see
[phrases.md](./phrases.md)), and — round 5 — the optional trailing
`by <np-group>` is the PASSIVE AGENT (`The request is logged by the
daemon.`), digested under the same Agent role as the deontic passive
`shall be logged by the daemon`, so the two meet at one atom. After the
agent a thematic-role tail may follow (round 8 follow-up): `The request
is logged by the daemon within 5 seconds.` keeps its Deadline structured
and meets the deontic spelling at one atom too. Without an agent the
description keeps the plain predicate reading — role words in the
predicate itself stay ordinary words.

```text
The retry count is at most 3.
The sales amount is always greater than zero.
The temperature is never above the limit.
Requests are logged.
The request is logged by the daemon.
The request is logged by the daemon within 5 seconds.
```

**Why `is not` is rejected.** Negation in a description has exactly one site:
`never`. A dedicated adverb slot gives the negation a syntactically fixed
scope, where a free-floating `not` would leave open what exactly is denied.
`The sales amount is not greater than zero.` is rejected as
`negated_description`, with the canonical rewrites in the message: write
`never` for a negative invariant, or `shall not` if an obligation was meant.
An empty predicate (`The pump is.`) is rejected as `empty_predicate`.

**Capability — `is [always|never] able to <response>`.** After the copula —
directly, or after the description adverb (round 5) — the token sequence
`able to` takes a full verb phrase and yields the capability predicate
(`Predicate::AbleTo`):

```text
The client is able to retry.
The client is always able to retry.
The client is never able to retry.
The daemon is able to shut down gracefully within 5 seconds.
No client is able to retry.
```

A capability is a description of behavior the subject can exhibit — free of
deontic force, denoting behavior through its verb phrase (see
[semantics.md](./semantics.md)). Its polarity composes exactly like a
description's: `never` XOR a subject `no` — `is never able to` and a `no`
subject each deny the capability, and together they cancel. This is the
faithful rewrite for a `can` that really meant ability; `can` itself stays
rejected (`unsupported_modal`). (Round 4 had kept `is always able to …` as
ordinary open words; round 5 supersedes that pin — the adverb now composes
instead of demoting the form.)

---

## The four deontic acts — `shall` / `must` / `should` / `may`

```text
<subject> shall|must|should [not] <verb phrase>.
<subject> may <verb phrase>.
<subject> shall|must|should|may either <verb phrase> or <verb phrase>.
```

All four map to `Core::Deontic { subject, modal, negated, vp }`, where `vp`
is a `VpGroup` — a single verb phrase, or (round 6) `either … or …`
ALTERNATIVES: `The server shall either accept the request or reject the
request.` obliges the disjunction, which no pair of single sentences can
say (two `shall` sentences oblige both). `not` never combines with
alternatives (`NegatedAlternatives` — write two prohibitions);
`and`-coordination of verb phrases stays unsupported (two sentences already
mean both-required); descriptions and capabilities keep a single verb
phrase. See
[phrases.md](./phrases.md#alternatives--either-vp-or-vp-round-6). The modal
and the optional `not` together decide the act:

| Surface | Speech act | Notes |
| --- | --- | --- |
| `shall` / `must` | obligation | both binding; the word used is preserved (`Modal::Shall` vs `Modal::Must`) |
| `shall not` / `must not` | prohibition | `negated: true` |
| `should` / `should not` | recommendation | a negated recommendation stays a recommendation |
| `may` | permission | admissibility, not requirement |

```text
The pump shall stop.
The daemon must not store derived views.
The daemon should not retry.
The client may retry.
```

- **`shall` and `must` are the same act at the same strength.** Neither is
  normalized into the other: the tree records which word the author wrote,
  and any distinction between them is a downstream view over the words, not
  a grammatical one.
- **`may not` is rejected** as `ambiguous_modal`: English cannot decide
  between denial of permission and prohibition. The canonical rewrite is
  `shall not`.
- **A subject `no` under `may` is rejected** as `no_with_may`, for the same
  reason: `No client may retry.` reads as a denial of permission, not a
  permission over an empty subject. The canonical rewrite is the prohibition
  `The client shall not retry.` A coordinated subject triggers the rule when
  any of its items is determined by `no`.
- **`can`, `will`, `would`, `could`, `might`, `ought` are rejected** as
  `unsupported_modal`, naming the four supported modals and the capability
  rewrite. `can` blurs ability into permission: write `shall`/`must` for an
  obligation, `may` for a permission — or, when ability really was meant,
  the capability description `is able to <response>` (above). These words
  are reserved everywhere — even as nouns (`the will`) — because reserving
  them is what makes the diagnostic possible at pivot position.
- The verb phrase after the modal — verb, optional object, thematic roles,
  and the `be`-complement — is the [phrase grammar](./phrases.md)'s. A modal
  with nothing after it (`The pump shall.`) is rejected as `empty_vp`.

---

## Circumstance frames — `Where` / `While` / `When` / `If`

A frame is `<keyword> <clause>,` — the comma is mandatory and closes the
clause. Frames lead the sentence, in **canonical order**:

```text
{ Where <clause>, } { While <clause>, } [ When <clause>, | If <clause>, [then] ] <core>
```

| Keyword | Reading | AST |
| --- | --- | --- |
| `Where` | configuration scope | `Frames::scopes` (any number) |
| `While` | state scope | `Frames::states` (any number) |
| `When` | trigger: an ordinary event | `Frames::trigger`, `TriggerKind::Event` |
| `If` | trigger: a contingency (EARS' unwanted-behaviour form) | `Frames::trigger`, `TriggerKind::Contingency` |

```text
Where the region is EU, where the plan is premium, while the engine runs,
when the temperature exceeds the limit, the pump shall stop.
```

- **Canonical order.** `Where` before `While` before the trigger. A frame out
  of order is rejected as `frame_order`, naming the keyword and what it
  illegally follows. The rule keeps the sentence's shape canonical: the
  standing scopes come first, the states next, the trigger — the one frame
  that fires — immediately before the core it fires.
- **At most one trigger.** A second `When`/`If` is rejected as
  `multiple_triggers`. The conjunction of two trigger *occurrences* has no
  single reading — at once? in sequence? within some window? — so the grammar
  refuses to pick one. State the joint condition inside ONE frame with clause
  coordination (below): `When the order ships and the payment is cleared, …`
  — one event, the other conjuncts as states read at its instant.
  **Sequencing** — one event *relative to* another — is not conjunction:
  write the trigger event with an `after` (or `before`) role, `When the
  payment clears after the order ships, the system shall issue the
  receipt.` The trigger stays one occurrence (`the payment clears`); the
  nested clause orders it. See the sequence example in
  [cookbook.md](./cookbook.md).
- **`then` belongs to `If` only.** Immediately after an `If` clause's comma,
  `then` is consumed; the trees with and without it are identical, and
  `render` always re-emits it. After any other frame, `then` is rejected as
  `then_without_if`.
- **Definitions take only `Where`.** A definition is timeless — vocabulary
  does not switch on and off with events or states — so a `While`, `When`, or
  `If` frame on a definition is rejected as `frame_on_definition`. All frames
  are available to descriptions and the deontic acts.
- **Frames lead; conditions never trail.** A frame keyword after the pivot
  (`… should default export to X when no endpoint is configured.`) is
  rejected as `mid_sentence_frame`; the canonical rewrite moves the condition
  to the front: `When no endpoint is configured, the tracing library should
  default export to X.`
- Keyword casing from the input is preserved in the tree (`Frame::keyword`,
  `Trigger::keyword`); `render` canonicalizes it. A frame whose comma is
  missing is `unterminated_frame`; a keyword directly followed by its comma
  is `empty_frame`.

The clause inside a frame is a subject plus a copular body (`is` / `are` /
`remains` + predicate) or a verbal body (verb + optional particle + optional
object + thematic roles, the same shape a verb phrase reads after its verb):
`When the pump runs at the depot,` carries a Location role, `When the user
logs out,` a particle. **Round 8: copular bodies carry the same
thematic-role tail** — predicate, then the optional passive agent (`by
<np-group>`, immediately after the predicate: the round-5 shape), then
roles: `While the pump is active at the depot,` carries a Location role,
`When the request is submitted by the user within 5 seconds,` an agent and
a Deadline. A `by` written later in the tail (`When the record is stored
in the archive by the daemon,`) is the Agent ROLE — a copular body is a
passive site, so both spellings are lossless, round-trip, and digest to
one Agent role. `able to <vp>` exactly after the copula is the capability
predicate (round 8, bare form only — see
[phrases.md](./phrases.md#the-capability-predicate--able-to-vp)).
**Round 9: a verbal clause body takes a final CONTENT complement** —
`When the monitor ensures that the token is valid,` — the same `that
<clause>` slot a verb phrase carries, roles preceding it (see
[phrases.md](./phrases.md#content-complements--verb-that-clause-round-7);
supersedes the round-7 frames-content-free legislation on new grounds:
dependency statements belong in guards). The
frame keyword, not a dictionary, fixes the
temporal reading: `When the order is submitted` reads the same copular
clause as an event that `While the order is open` reads as a state. See
[phrases.md](./phrases.md).

### Clause coordination inside a frame

A frame holds a **clause group** (`ClauseGroup { conj, items }`): one clause,
or several coordinated under a single conjunction — one frame either way.

```text
When the order ships and the payment is cleared, the system shall issue the receipt.
While the pump runs or the valve is open, the system shall alert the operator.
```

- **`and` is a joint guard**: all items hold together. In a trigger (`When`/
  `If`) an `and` group takes at most ONE event (verbal) conjunct; every other
  conjunct must be a state (`is/are/remains …`) read at the trigger instant.
  Two events under `and` (`When the order ships and the payment clears,`) are
  rejected as `multiple_event_conjuncts` — the conjunction of two occurrences
  is simultaneity, the same ill-defined reading the one-trigger rule refuses.
  Rewrite the extra event as a state, or move it to a `While` frame.
- **`or` is an alternative guard**: any one suffices. `or` groups are exempt
  from the one-event rule — a disjunction of events is alternation (either
  occurrence triggers), which is well-defined — so `When the order ships or
  the payment clears,` stays legal. Either way the sentence still has ONE
  trigger frame — splitting a joint guard into two sentences would change
  its meaning (each sentence would fire alone).
- **`While`/`Where` groups are unrestricted**: their clauses are scopes and
  states, not occurrences, so any mix of verbal and copular conjuncts is
  legal under either conjunction.
- **One conjunction per frame.** Mixing `and` and `or` in one frame is
  rejected as `mixed_coordination`.
- **Noun-phrase coordination still wins where no prefix is a complete
  clause.** `When the pump and the valve are open,` is ONE clause with a
  coordinated subject (`the pump` alone is no clause); `When the pump runs or
  the valve is open,` is two clauses (`the pump runs` is complete). The
  coordinated reading splits at a conjunction whose prefix parses as a
  complete clause *and* whose remainder reads as clauses the same way, so a
  conjunction inside a coordinated object never opens a split: `While the
  order ships the report and the invoice and the payment clears,` is a
  two-item joint guard whose first clause keeps the coordinated object
  `the report and the invoice`. (Under `When`/`If` this exact pair would then
  be rejected as `multiple_event_conjuncts` — both conjuncts are events — so
  the two-verbal form lives in a `While` frame.)
- **Asymmetry (v0.2 scope):** only frames and triggers coordinate clauses.
  `unless`, `so that`, `before`, `after`, and a clause definiens keep a
  single clause.

---

## The exception — `unless`

```text
<core>, unless <clause>.
```

```text
The pump shall stop, unless the override is active.
```

An exception is a **defeasibility carve-out**: it narrows the circumstances
under which the sentence applies. It is structure, not conflict — a sentence
with an exception does not contradict its unconditional reading; it states
the boundary of its own applicability. The clause lands in
`Sentence::exception`, and derived views carry it alongside the frames.

- At most one exception, and it precedes the purpose; `…, so that …, unless …`
  is rejected (`unexpected_tokens` on the `unless`).
- The comma is part of the form. `The pump shall stop unless the override is
  active.` is rejected as `mid_sentence_frame`; `unless` opening a sentence is
  rejected as `leading_exception` — the exception follows the core.

---

## The purpose — `so that` / `in order to`

```text
<core>, so that <clause>.
<core>, in order to <verb phrase>.
```

```text
The daemon shall persist the node, so that the auditor traces the decision.
The system shall log each request, in order to preserve the audit trail.
```

A purpose is **intent metadata**: it records what the sentence serves, and it
does not constrain behavior. A system that logs each request but loses the
audit trail satisfies the second sentence's requirement while defeating its
recorded intent — that gap is visible to later analysis precisely because the
purpose is kept in the tree (`Purpose::SoThat(Clause)` /
`Purpose::InOrderTo(Vp)`) instead of being folded into the requirement.

At most one purpose, in either form, and it is the sentence's final adjunct.

---

## See also

- [phrases.md](./phrases.md) — the phrase grammar: noun phrases, verb
  phrases, clauses, predicates, measures.
- [lexical.md](./lexical.md) — tokenization, sentence splitting, casing, the
  optional terminator.
- [errors.md](./errors.md) — every rejection named above, with exact messages
  and canonical rewrites.
- [semantics.md](./semantics.md) — the interpretations derived over these
  sentences: speech acts, force, polarity, denotations.

[`parse`]: ../../so_lang/src/parse.rs
