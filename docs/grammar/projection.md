# Assume-guarantee projection & data model

> Part of the [grammar reference](./README.md).

An accepted statement is projected — mechanically and unambiguously — into an
assume-guarantee **Contract**. The projection is a total function on the accepted
language: one accepted statement yields exactly one `Contract`. Statements that do
not parse never reach projection; see [errors.md](./errors.md) for the failure
taxonomy and [reference.md](./reference.md) for the formal grammar and algorithm.

A `Contract` has two parts:

| Part | Source in the statement | Type |
| --- | --- | --- |
| **assumption** | the leading condition clauses (possibly none) | `Assumption` |
| **guarantee** | the `<subject> <shall|must|should> <response>` clause | `Guarantee` |

## Assumption: the conjunction of the condition clauses

Every leading condition clause becomes part of the assumption. The assumption is
the **conjunction** of those clauses — all of them must hold for the guarantee to
apply.

- **No condition clause** (the Ubiquitous form): the assumption is `Top` (`⊤`).
  The guarantee holds unconditionally.
- **One or more condition clauses** (the Conditional and Complex forms): the
  assumption is `Conditions { clauses }`, holding each parsed `Condition` in order.

Each `Condition` keeps the keyword's **surface casing** as written in the input
(e.g. a lower-case `when` is preserved as `when`, not normalized to `When`) and
the condition phrase with the keyword and trailing comma stripped.

| Statement shape | Assumption |
| --- | --- |
| `<subject> <shall\|must\|should> <response>.` | `Top` (`⊤`) |
| `<kw> <c>, <subject> <shall\|must\|should> <response>.` | `Conditions { clauses: [c] }` |
| `<kw> <c1>, <kw> <c2>, <subject> <shall\|must\|should> <response>.` | `Conditions { clauses: [c1, c2] }` |

## Guarantee: opaque subject and response

The `<subject> <shall|must|should> <response>` clause becomes the `Guarantee`:

- **subject** — the noun phrase before the selected guarantee modal. A leading
  `the` is stripped when present so EARS-style statements continue to project
  `The system shall ...` as subject `system`.
- **response** — everything after the selected modal (`shall`, `must`, or
  `should`).

Both are captured as **opaque free text**, trimmed of surrounding whitespace.
Neither is decomposed further at ingest: the subject is not resolved to an entity,
and the response is not parsed into a predicate language. Those are deliberate
[non-goals](#non-goals).

The selected modal is not stored in `Guarantee`. This is deliberate: the raw
statement is the source of truth, and later views such as normative strength can
derive from that text without making ingest depend on a settled strength model.

## Data model

The types below are all `pub` and derive `serde::{Serialize, Deserialize}`.

```rust
struct Condition { keyword: String, text: String }

#[serde(tag = "kind", rename_all = "snake_case")]
enum Assumption {
    Top,
    Conditions { clauses: Vec<Condition> },
}

struct Guarantee { subject: String, response: String }

struct Contract { assumption: Assumption, guarantee: Guarantee }
```

### JSON shapes

`Assumption` is an internally tagged enum: serde writes the variant into a `kind`
field, `snake_case`.

`Top` (the Ubiquitous case):

```json
{ "kind": "top" }
```

`Conditions`:

```json
{
  "kind": "conditions",
  "clauses": [
    { "keyword": "When", "text": "the order is submitted" }
  ]
}
```

`Guarantee`:

```json
{ "subject": "system", "response": "record the total" }
```

## Worked example

Take the Conditional statement:

```text
When the order is submitted, the system shall record the total.
```

It projects to:

| Field | Value |
| --- | --- |
| assumption | `Conditions` with one clause `("When", "the order is submitted")` |
| guarantee subject | `system` |
| guarantee response | `record the total` |

The full `Contract` as JSON:

```json
{
  "assumption": {
    "kind": "conditions",
    "clauses": [
      { "keyword": "When", "text": "the order is submitted" }
    ]
  },
  "guarantee": {
    "subject": "system",
    "response": "record the total"
  }
}
```

## Projection onto a persisted Node

The raw constrained-NL statement is the **source of truth**. On a persisted Node,
`statement` holds that raw string; `assumption` and `guarantee` are stored as
**top-level fields projected from `statement`**. They are a derived view: the
statement, not the projection, is authoritative, and neither subject nor response
is decomposed further at ingest.

## Render forms (display only)

`render()` produces human-readable text for display. Storage keeps the structured
form above; these helpers do not round-trip and are not the persisted
representation.

| Value | `render()` output |
| --- | --- |
| `Assumption::Top` | `⊤` |
| `Assumption::Conditions` | clauses joined by `, `, each as `<keyword> <text>` |
| `Guarantee` | `the <subject> shall <response>` (canonical display form) |

For example, a two-clause assumption renders as:

```text
While the engine is running, when the temperature exceeds the limit
```

and its guarantee as:

```text
the controller shall open the valve
```

## Non-goals

The projection stops at opaque subject/response text. The following are explicitly
deferred and are **not** performed at ingest:

- **subject resolution** — the subject stays free text; it is not linked to an
  entity or identifier.
- **a formal predicate language for the response** — the response stays free text;
  it is not parsed into a logical form.

Strength, edges (refinement/composition/conjunction/quotient), and
classification/review are likewise out of scope for the projection.
