# Lexical & tokenization rules

> Part of the [grammar reference](./README.md).

This file is the authority on how the recognizer treats **whitespace**, the
**trailing period**, **word boundaries**, **casing**, the optional **`then`**,
and **multibyte text**. Other pages ([forms](./forms.md),
[reference](./reference.md), [errors](./errors.md)) link here instead of
restating these rules.

Everything below is what `so_lang::grammar::parse` does in
[`so_lang/src/grammar.rs`](../../so_lang/src/grammar.rs) — nothing more.

## Where these rules apply

`parse` normalizes the input, then consumes zero or more condition clauses, then
parses one guarantee clause. The lexical rules act at specific points in that
order:

| Step | Rule | Section |
| --- | --- | --- |
| 1 | Trim outer whitespace; reject if empty | [Whitespace](#whitespace-trimming) |
| 2 | Strip at most one trailing `.`, trim again; reject if empty | [Trailing period](#trailing-period-at-most-one) |
| 3 | Match condition keywords at a **whitespace** boundary | [Word boundaries](#word-boundaries-two-different-notions) |
| 3 | Drop one optional `then` after a clause comma | [Optional `then`](#the-optional-then) |
| 4 | Optionally strip determiner `the` at a **whitespace** boundary; find modal `shall`, `must`, or `should` at an **alphanumeric** boundary | [Word boundaries](#word-boundaries-two-different-notions) |

## Whitespace trimming

The input is `trim()`-med first. Leading and trailing spaces, tabs, and newlines
never reach the grammar. An input that is empty or all-whitespace is rejected as
[`Empty`](./errors.md#empty).

```text
"   The pump shall stop.  "   ->  body: "The pump shall stop"
"   "                         ->  Empty
```

Whitespace **inside** the statement is preserved as-is within the captured
subject, response, and condition text (each of those is `trim()`-med only at its
own edges).

## Trailing period (at most one)

After trimming, the recognizer strips **at most one** trailing `.`
(`strip_suffix('.')`) and trims once more to form the `body`. If the body is then
empty, the input is rejected as [`Empty`](./errors.md#empty).

Two consequences follow, both intentional:

- **`.` alone is `Empty`.** The single period is stripped, leaving an empty body.
- **A second trailing period, and any internal period, is kept** as literal text
  inside the clause. Only one period comes off, and only from the very end.

```text
"The pump shall stop."    ->  response: "stop"
"The pump shall stop"     ->  response: "stop"     (period is optional)
"The pump shall stop.."   ->  response: "stop."    (one '.' stripped; one remains)
"The system shall log v1.2."  ->  response: "log v1.2"   (internal '.' kept)
```

## Word boundaries: two different notions

The recognizer uses **two different** boundary tests, and the asymmetry is real
and load-bearing. Getting this wrong is the most common source of surprising
accept/reject outcomes.

| Token(s) | Boundary test | A match requires the next character to be… |
| --- | --- | --- |
| Condition keywords (`While` `When` `If` `Where`), optional determiner `the`, `then` | `starts_with_word` | **whitespace** |
| Modals `shall` / `must` / `should` | `find_word_from` | **non-alphanumeric** (or a string edge) |

### Whitespace boundary — keywords, optional `the`, `then`

`starts_with_word` matches the token as a case-insensitive prefix **only when the
character immediately after it is whitespace**. A comma, a letter, or end-of-string
does not count.

```text
"When the door opens, ..."   ->  keyword "When"   (followed by a space)
"Whenever the door opens"    ->  NOT a keyword     (next char is 'e')
"If, the pump shall stop."   ->  NOT a keyword     (next char is ',')
```

Because `Whenever` is not the keyword `When`, the condition loop does not fire and
the text is handled as an ordinary (here, malformed) guarantee clause. Because
`If,` is not the keyword `If`, no clause is opened. **A keyword must be followed by
a space to count** — which also means the keyword can never absorb the comma that
terminates its own clause.

The same test guards the optional guarantee determiner: when a guarantee clause
opens with `the` followed by whitespace, that word is stripped from the projected
subject. It is not required; `AddContract shall return the node.` is also a valid
guarantee clause.

### Alphanumeric boundary — the modals `shall`, `must`, and `should`

`find_word_from` scans for `shall`, `must`, and `should` (case-insensitive)
bounded on **both** sides by a non-alphanumeric byte or a string edge. This lets
punctuation hug the modal but prevents a modal buried inside a longer word from
matching.

```text
"The marshalling yard shall be clear."   ->  subject "marshalling yard",
                                             response "be clear"
```

Here the `shall` inside **mar·shall·ing** is preceded by `r` (alphanumeric), so it
is *not* the modal; the real `shall` later in the sentence wins. Similarly,
`must` inside `mustard` and `should` inside `shoulder` are not modals.
Conversely, punctuation-adjacent forms *do* match, because commas, parentheses,
and brackets are non-alphanumeric:

```text
"... shall, ..."   ->  matches the modal
"... (shall) ..."  ->  matches the modal
"... [should] ..." ->  matches the modal
```

> Why two notions? Keywords and the optional determiner sit at the *start* of a
> clause and are always separated from their argument by a space, so a whitespace
> boundary is the right, strict test. The modal sits *mid-clause* between
> free-form subject and response text, where adjacent punctuation is normal, so
> an alphanumeric boundary is the right test there.

## Casing

The four condition keywords, the optional determiner `the`, the modals `shall`,
`must`, and `should`, and `then` are all matched **case-insensitively** (ASCII
case folding). `WHEN`, `When`, and `when` are all recognized as the keyword;
`SHALL` and `shall`, `MUST` and `must`, or `SHOULD` and `should`, pivot the
guarantee.

The captured **condition keyword preserves the surface casing from the input** —
it is not normalized to the canonical `CONDITION_KEYWORDS` spelling.

```text
"when the order ships, the system shall notify the customer"
    ->  condition keyword captured as "when"   (lowercase, as written)
```

Subject, response, and condition **text** are always captured verbatim; no case
folding is applied to them. If multiple modal candidates exist, the parser uses
the first one that leaves both a non-empty subject and a non-empty response, so
literal-token subjects such as `The shall clause shall ...` remain expressible.

## The optional `then`

EARS allows `If <condition>, then <response>`. The recognizer drops a single
leading `then` **only immediately after a clause's comma**, and only when it is
whitespace-bounded (same `starts_with_word` test as above). It is stripped once,
not repeatedly.

```text
"If the balance is negative, then the account shall be frozen."
    ->  condition ("If", "the balance is negative"); response "be frozen"
        ("then" dropped)
```

A `then` that is not in this position — for example inside the response text — is
ordinary text and is left untouched.

## UTF-8 / multibyte safety

The recognizer is **total**: it returns `Ok` or `Err` for *every* input and
**never panics**, including on arbitrary multibyte UTF-8. `starts_with_word` uses
`str::get(..len)`, which returns `None` (rather than panicking) when a token length
would fall inside a codepoint — exactly the "not this token" answer we want.
`find_word_from` scans bytes with ASCII boundary checks and never splits a
codepoint.

Non-ASCII **subject, response, and condition text is captured verbatim**. Only the
keywords, optional determiner, modals, and `then` are ASCII (matched
ASCII-case-insensitively); everything else is opaque UTF-8.

```text
"The café shall serve crêpes."              ->  subject "café",
                                                response "serve crêpes"
"When the café is open, the barista shall greet the guest."
    ->  condition ("When", "the café is open"); subject "barista"
```

## See also

- [Errors](./errors.md) — the exact `ParseError` each rule can raise.
- [Reference](./reference.md) — the EBNF and the full parsing algorithm, including
  greedy clause consumption.
- [Forms](./forms.md) — the three accepted statement shapes these tokens build.
