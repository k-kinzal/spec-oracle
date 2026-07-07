# Lexical & tokenization rules

> Part of the [grammar reference](./README.md).

This file is the authority on the recognizer's lowest layer: how raw text is
split into **sentences** and **tokens**, which characters are structural, which
words are **reserved**, how **casing** works, what the canonical **render**
normalizes and what it keeps, and how **multibyte** input stays safe. Other
pages ([sentences](./sentences.md), [phrases](./phrases.md),
[reference](./reference.md), [errors](./errors.md)) link here instead of
restating these rules.

Everything below is what the code does — `split_sentences` and `tokenize` in
[`so_lang/src/parse.rs`](../../so_lang/src/parse.rs), plus `Sentence::source`
and the `render` family in [`so_lang/src/ast.rs`](../../so_lang/src/ast.rs) —
nothing more.

## Order of operations

`parse` maps the whole input to one specification (one or more sentences) or
one error. The lexical layer acts first, in this order:

| Step | What happens | Section |
| --- | --- | --- |
| 1 | The input is split into per-sentence slices at terminating periods | [Sentence splitting](#sentence-splitting) |
| 2 | Each slice is recorded verbatim as `Sentence::source` | [`Sentence::source`](#sentencesource-is-exact) |
| 3 | Each slice is tokenized: whitespace split, then trailing `,` / `.` peeled | [Tokenization](#tokenization) |
| 4 | The phrase grammar runs over the tokens; closed-class words are recognized case-insensitively and positionally | [Casing](#casing-closed-class-matching-is-case-insensitive), [Reserved words](#reserved-words-vs-open-words) |

An input with no sentence at all — empty, all whitespace, or a lone `.` (the
terminator strips to nothing) — is rejected as `Empty`.

## Sentence splitting

A specification is one or more sentences in a single string. The **only**
sentence boundary is a terminating period: a word whose final character is `.`,
followed by whitespace or end of input, ends a sentence there. The final
sentence may omit its period — the terminator is optional at end of input.

```text
"A session means a sequence of requests. When a session expires, the system
 shall close the session."
    ->  two sentences, split after "requests."

"The pump shall stop"          ->  one sentence (terminator optional)
"The delay is 5.5 seconds."    ->  one sentence ("5.5" does not end anything:
                                    its dot is not word-final before whitespace)
```

There is no other separator. Two sentences written without a period between
them are read as one sentence and rejected as stray material
(`UnexpectedTokens`) — the recognizer never guesses where one sentence ends and
the next begins.

Each per-sentence slice is trimmed to its first and last non-whitespace
character; the terminator, when present, is inside the slice.

## Tokenization

Each sentence slice is tokenized independently. The token alphabet has three
members:

| Token | What it is |
| --- | --- |
| `Word` | Any whitespace-delimited word, after punctuation peeling. Keeps its surface casing and every non-structural character. |
| `Comma` | A `,` split off the **end** of a word. |
| `Terminator` | A sentence-final `.` split off the **end** of a word. |

The procedure: split on ASCII whitespace, then peel trailing `,` and `.` marks
off each word, repeatedly, so every mark becomes its own token in surface
order. What remains of the word (if anything) is a `Word` token.

```text
"stop, now."   ->  Word("stop") Comma Word("now") Terminator
"total.,"      ->  Word("total") Terminator Comma
"."            ->  Terminator          (no word remains)
","            ->  Comma
```

Only ASCII whitespace, a word-final `,`, and a word-final `.` are structural.
Every other character — colons, slashes, parentheses, quotes, hyphens,
non-ASCII punctuation — stays glued to its word and travels through the phrase
grammar as opaque open-class material.

### Backtick tokens: the reserved-word escape hatch

A token wrapped in backticks (`` `will` ``, length ≥ 3) is **always an
open-class word**. The backticks are part of the token text: they are stored
in the tree exactly as written (`head: "`will`"`), re-emitted by the
canonical render (losslessness), and — because every closed-class test
compares the full token text — a backticked token never matches a keyword:
not as a modal, frame keyword, pivot, preposition, conjunction, or
determiner.

```text
The system shall record the `will`.    ->  object head `will` (with backticks)
The `while` loop shall terminate.      ->  modifier `while`, head loop
```

An unmatched single backtick is not special: `` `will `` and `` will` `` are
ordinary word characters (and, not being equal to `will`, are open-class
too). Punctuation peeling still applies outside the backticks:
`` the `will`. `` peels the terminator.

### The period rule

A `.` is a terminator **only at the end of a whitespace-delimited word**, which
by construction means only when it is followed by whitespace or end of input.
A period with a non-whitespace character after it is ordinary word content.
This is what keeps decimals, version strings, and URLs whole:

```text
"5.5"                          ->  Word("5.5")
"http://192.168.10.4:4318."    ->  Word("http://192.168.10.4:4318") Terminator
"The system shall log v1.2."   ->  "v1.2" survives; only the final '.' splits
```

One trailing `Terminator` per sentence is the end marker and is dropped before
parsing. Any *other* `Terminator` token is stray material: `"The pump shall
stop.."` peels two terminators, the second-to-last one has no role, and the
sentence is rejected with `UnexpectedTokens` naming `.`.

### The comma rule

A `,` is likewise structural only at the end of a word — that is, only when
followed by whitespace or end of input. A comma glued to the next word does
not split:

```text
"When x, the pump shall stop."   ->  frame comma recognized
"When x,the pump shall stop."    ->  Word("x,the") — no Comma token, so the
                                     frame never finds its comma:
                                     UnterminatedFrame
```

Write a space after every structural comma. Commas embedded inside a word are
never separators.

## Casing: closed-class matching is case-insensitive

Every closed-class test is a **whole-token, ASCII-case-insensitive**
comparison. `SHALL`, `Shall`, and `shall` all pivot a deontic core; `WHERE`
opens a scope frame; `MEANS` opens a definition. Because the comparison is
whole-token, punctuation glued to a word defeats recognition: `(shall)` is not
a pivot, it is an open-class word.

Surface casing is preserved in the tree wherever the word is stored as a
string, and collapsed wherever the word is stored as an enum:

| Tree position | Stored as | Casing |
| --- | --- | --- |
| Frame keywords (`Frame::keyword`, `Trigger::keyword`) | string | **surface casing kept** (`WHERE` stays `WHERE`) |
| All open-class words: modifiers, heads, verbs, predicate words, units | string | surface casing kept |
| Prepositional-predicate preposition (`Predicate::Pp`) | string | surface casing kept |
| Measure numbers (`Measure::Quantity`) | string | kept as written (`zero`, `ZERO`, `5`) |
| Modals, copulas, determiners, quantifier kinds, conjunctions, `both`/`either`, `that`/`who`, comparison operators, thematic-role kinds | enum | collapsed to the canonical form |
| Error fields (e.g. `UnsupportedModal { word }`) | string | surface casing kept (`CAN` is reported as `CAN`) |

```text
"the pump SHALL stop."   ->  Modal::Shall (casing collapsed), heads verbatim
"WHERE the flag is set, the pump shall stop."
                          ->  scope keyword captured as "WHERE"
```

## Canonical rendering

`Sentence::render` (and `Specification::render`, which joins sentences with a
single space) reproduces a sentence in **canonical form**. Render is
canonical, not verbatim — `Sentence::source` is the verbatim record.

Render **normalizes**:

- **Closed-class casing.** Every enum-stored word is emitted in its canonical
  lowercase form: modals, copulas, determiners, `and`/`or`, `both`/`either`,
  `that`/`who`, `of`, `not`, `always`/`never`, comparison operators, and role
  prepositions. A sentence-initial determiner renders lowercase: `The pump
  shall stop.` renders as `the pump shall stop.`
- **Frame keywords to title case.** `Where` / `While` / `When` / `If`,
  whatever the input casing.
- **`If …, then`.** An `If` trigger always re-emits `then`, whether or not the
  input wrote it. (`When` frames never emit one.)
- **Quantifier number words to digits.** `at least` / `at most` / `exactly`
  store a numeric value, so `at most two` renders as `at most 2`.
- **Whitespace and punctuation.** Single spaces throughout, one comma after
  each frame clause, `, unless` and `, so that` / `, in order to` attached
  with their comma, and exactly one trailing period.

Render **keeps**:

- Open-class words — modifiers, heads, verbs, predicate words, unit words —
  in surface order and surface casing.
- Frame keyword *choice* (`When` vs `If`, `Where` vs `While`) — only casing is
  normalized.
- Measure numbers exactly as written: `zero` stays `zero`, `5` stays `5`; a
  number word in a measure is never converted to a digit.
- The preposition of a prepositional predicate as written (it is stored as a
  string, not an enum).

The round-trip property, pinned by tests: for any accepted sentence,
`parse(render(t))` yields a tree equal to `t` up to `source` and frame-keyword
casing — the two places render is deliberately not verbatim.

## Reserved words vs open words

Open-class collection (subject and phrase material, predicate words) gathers
words until it hits a **reserved word**. The always-reserved set is:

| Group | Words |
| --- | --- |
| Pivots | `shall` `must` `should` `may` `is` `are` `means` |
| Excluded modals | `can` `will` `would` `could` `might` `ought` |
| Frame keywords | `where` `while` `when` `if` `unless` |
| Phrase structure | `of` `that` `who` `and` `or` `both` `either` `remains` `then` `not` — round 6: directly after a deontic modal, `either` followed by anything but a determiner opens VERB-PHRASE alternatives (`shall either accept the request or reject the request`) |

A reserved word can never be open-class material — never a modifier, head,
verb, or predicate word — in any position. A subject named `of` or a verb
named `will` is inexpressible as a bare word; wrap it in backticks
(`` the `will` ``) to use it as content — see
[backtick tokens](#backtick-tokens-the-reserved-word-escape-hatch).

**Why the excluded modals stay reserved.** `can`, `will`, `would`, `could`,
`might`, and `ought` are not part of the language, but they are reserved
precisely so they surface as diagnostics rather than noise. Because a reserved
word ends subject collection, `The client can retry.` stops the subject at
`can` and reports `UnsupportedModal` with the exact word and the fix (use
`shall`, `must`, `should`, or `may`). If those words were open-class, they
would be swallowed into the subject and the author would get an unhelpful
`MissingPivot` instead. The same holds for `unless` (a `LeadingException` /
mid-sentence diagnosis, not a mystery word) and `then` (a `ThenWithoutIf`
diagnosis when misplaced).

Beyond the always-reserved set, the closed class is **positional** — a word is
special only where its construction is possible, and an ordinary word
everywhere else:

| Words | Closed only… |
| --- | --- |
| `to` `via` `using` `about` `within` `for` `per` `before` `after` `until` `from` `into` `with` `by` | after a verb — inside a verb phrase or a verbal clause body — where they open thematic-role phrases. In a subject they are ordinary words. Round 5: `with` is reserved here only to be REJECTED (`WithIsAmbiguous` — write `using` or coordinate), and round 6 closes bare `with` inside EVERY noun phrase — plain subject positions included — with the same error (backtick `` `with` `` for noun uses); `by` opens the Agent role in a complemented `be` verb phrase and is rejected elsewhere (`ByOutsidePassive`); `for` requires a quantity (`ForRequiresMeasure` otherwise). `by` additionally ends open-class collection everywhere in a copular/description PREDICATE — in its open words, inside a prepositional predicate's noun phrase, and inside a comparison's noun-phrase measure alike — where it introduces the passive agent (`is logged by the daemon`, `is below the limit by the sensor`); the other role words stay ordinary in a DESCRIPTION's predicate — but AFTER a description's passive agent they open the role tail (round 8 follow-up: `is logged by the daemon within 5 seconds` carries a structured Deadline). Round 8: in a copular CLAUSE or RELATIVE body's predicate the role and locative prepositions are closed exactly as after a verb — they end the predicate and open its thematic-role tail (`while the pump is active at the depot`); exception, legislated: when collection stopped with `able` before `to` (an adverbed `is always able to retry`, never a capability outside descriptions), the predicate resumes flat — the whole tail stays ordinary predicate material rather than misreading `to <verb>` as a Recipient role. |
| `in` `on` `at` `below` `above` `under` `over` | at the start of a predicate, where they open a prepositional predicate; and after a verb (verb phrase or verbal clause body) or a copular clause/relative predicate (round 8), where they end open-class collection and open a Location role (`at least`/`at most` stay comparisons). |
| `out` `down` `up` `off` | immediately after a verb other than `be` — or reached across the verb's manner run (`shut gracefully down` = `shut down gracefully`) — as the verb's particle (`logs out`, `shuts down the server`); or trailing that verb's object (`lift the beam up` = `lift up the beam`). Everywhere else they are ordinary open-class words. |
| `the` `a` `an` `each` `every` `all` `any` `no`, `at least` / `at most` / `exactly` + number | at the start of a noun phrase. Mid-phrase, `the` is just a word. |
| `greater than` `less than` `at least` `at most` `equal to` `between` | at the start of a predicate, as comparisons. `at` alone falls back to the prepositional reading. |
| `so` + `that`, `in` + `order` + `to` | at the start of a comma-separated adjunct segment. |
| `always` `never` | immediately after a description's copula, as adverbs (`never` is a negation site). Everywhere else they are ordinary open-class words — `No request shall not never be logged.` parses with *verb* `never`, so the apparent third negation does not flip polarity. |
| bare words ending in `ly` (ASCII, longer than two letters) | in **post-verbal position** — where an object or a role phrase would start: not determiner-led, not a role or locative preposition, not a conjunction or boundary — as manner adverbs (`stop immediately`, `completes successfully`). Juxtaposed `ly` words extend the run; a conjunction ends it. **The rule is purely morphological**, so `ly`-final words that are not manner semantically are swept in too: the focus adverb `only` (`log only the errors` puts `only` in the manner slot, changing the atom digest) and words like `early` — write `` log `only` the errors `` when the word must stay an ordinary open-class word. Inside a noun phrase — after a determiner or as a modifier before a head — `ly` words are untouched (`the assembly`, `the nightly build`), and `exactly` + number stays a quantifier. A bare `ly` word meant as a noun object needs backticks: `` record `supply` ``. The clause verb heuristic prefers a non-`ly` verb — trailing `ly` words are read as manner (`the export completes successfully` → verb `completes`) — but when stripping them leaves no parseable subject and verb, it backs off innermost-first and the `ly` word itself is the verb (`the peers reply`, `the peers reply quickly` → verb `reply`). |

**The fail-closed verb boundary (round 11).** None of the words above mark
where a boundary-less verbal clause's subject ends and its verb begins, so
a trailing bare-word run of two or more words after the *minimal* subject
(with a verb-capable first run word) admits two readings at once —
minimal-subject SVO and long-subject final-word — and is **rejected** as
`ambiguous_verb_boundary` rather than legislated either way (round 11,
superseding the round-10 SVO acceptance and the round-3 final-word
acceptance for exactly this class). A pre-verbal manner word is skipped,
not frontier-closing (`the client quickly sends telemetry` rejects like
its manner-less twin), and a trailing particle or bare number keeps its
round-3/4 reading only when popping it leaves a run outside the class
(`the user logs out` stands; `the client sends telemetry out` rejects).
A determiner on the object, an
of-chain or relative on the subject, or any role/locative boundary makes
the verb position provable again. See
[reference.md §3.3](./reference.md#33-verbal-clause-verb-selection) and
[errors.md](./errors.md#ambiguousverbboundary--ambiguous_verb_boundary).

## Number words and numerals

Two spellings of a number are recognized, in quantifier and measure positions
only:

- **Number words** (round 12 extends the table): `zero` through `twenty`,
  the tens `thirty`, `forty`, `fifty`, `sixty`, `seventy`, `eighty`,
  `ninety`, and `hundred` — matched case-insensitively. **Single words
  only**: compounds (`twenty-one`, `one hundred`) are not recognized —
  write digits.
- **Numerals**: digits with an optional single decimal part — `5`, `42`,
  `5.5`. The match is full-token: `5.`, `.5`, `5.5.5`, and signed forms are
  not numerals, they are ordinary words.

Where the number lands decides its fate:

- In a **quantifier** (`at least` / `at most` / `exactly`), the number becomes
  a stored numeric value, so `at least three` and `at least 3` are the same
  tree (and render as `at least 3`). A quantifier's number must be a whole
  number that fits in 64 bits: `at least 5.5 retries` is rejected as
  `QuantifierNotWhole` rather than silently degrading into open-class words.
- In a **measure** (`within 5 seconds`, `greater than zero`), the number is
  kept exactly as written, with an optional following unit word. Numeric
  evaluation is a downstream concern.
- A bare number can close a verbal clause as its object (`the counter reaches
  zero`).

**Fail closed on unknown number words (round 12).** In a position that
requires a number — after a quantifier opener (`at least` / `at most` /
`exactly`), after `within`, or after a bound opener under `for` — a
word-shaped token (ASCII letters and hyphens) that is not in the table and
not a numeral is rejected as `UnknownNumberWord` with the rewrite hint
(write digits): `At least eleventy nodes shall run.` no longer degrades
silently into open-class modifiers, and `within eleventy seconds` no
longer becomes a noun-phrase measure that never grounds an interval.
Determiner-led phrases and reserved words are exempt (legislated): `within
the timeout` keeps its noun-phrase measure, `for at least the limit` keeps
its `ForRequiresMeasure` rewrite.

Elsewhere, number words are ordinary open-class words — they are not reserved.

## Multibyte safety

The recognizer is **total**: it returns `Ok` or `Err` for every input and
never panics, including on arbitrary multibyte UTF-8. This holds structurally:

- Sentence splitting walks `char_indices` and advances by each character's
  UTF-8 length; slices always land on character boundaries.
- Tokenization splits on ASCII whitespace and peels single ASCII characters
  (`,`, `.`) from word ends — there is no fixed-byte prefixing anywhere.
- All closed-class tests are whole-token ASCII-case-insensitive comparisons,
  which are byte-safe on any UTF-8 word.

Only the closed class is ASCII. Non-ASCII words are opaque open-class tokens,
captured verbatim: `The café shall serve crêpes.` parses with subject head
`café`. Non-ASCII punctuation (`。`, `、`, `«»`, …) is never structural — it
stays glued to its word. The totality suite
([`so_lang/tests/attack_totality.rs`](../../so_lang/tests/attack_totality.rs))
drives this with CJK/emoji mixes, lone combining marks, `×`, 100k-character
emoji tokens, and seeded random word soup and Unicode noise.

## `Sentence::source` is exact

Every parsed sentence carries `source`: the **exact input slice** it was
parsed from, trimmed of surrounding whitespace, terminator included when the
author wrote one. Internal whitespace, casing, and punctuation are verbatim —
`source` is not re-rendered.

```text
"   The pump shall stop.   "   ->  source "The pump shall stop."
"The pump shall stop"          ->  source "The pump shall stop"
"A session means a sequence of requests. When a session expires, …"
    ->  sentence 1 source "A session means a sequence of requests."
        sentence 2 source "When a session expires, …"
```

This anchors losslessness: the raw words are the source of truth wherever a
sentence is persisted; the tree is their structure, and `render` is a
canonical projection of the tree — never a replacement for `source`.

## See also

- [errors.md](./errors.md) — the full `ParseError` taxonomy these rules can
  raise.
- [reference.md](./reference.md) — the formal grammar and the parsing
  algorithm over these tokens.
- [sentences.md](./sentences.md) — the sentence layer (speech-act cores,
  circumstance frames, exceptions, purposes) the tokens build.
