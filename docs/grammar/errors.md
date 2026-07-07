# Syntax errors (the `ParseError` taxonomy)

> Part of the [grammar reference](./README.md).

The parser is a [total recognizer](./README.md#philosophy-a-total-recognizer):
every input yields exactly one `Specification` or exactly one `ParseError` —
never a panic, never a partial tree, never a guess. A `ParseError` is the only
way a specification fails to parse; there is no confidence score, no partial
acceptance, and no human review. If `parse` returns `Err`, the specification is
not in the language and nothing downstream runs.

Every variant carries a fixed, human-readable `Display` message that speaks the
surface vocabulary — sentences, circumstance frames, speech-act cores,
subjects, predicates — and each has a stable snake_case name from
`ParseError::kind()` for telemetry (the daemon records it as the
`spec.parse.error.kind` span attribute). The thirty-one variants below are
exhaustive; the single source of truth is
[`so_lang/src/parse.rs`](../../so_lang/src/parse.rs). Parsing is per sentence:
in a multi-sentence specification, the first sentence that fails rejects the
whole input with that sentence's error.

Several rejections are deliberate language design, not accidents of the
recognizer: `may not`, `can` and its cousins, mixed `and`/`or` in one
coordination, a condition trailing the sentence, a leading `unless`, and a
negated description all have more than one natural reading, so each is refused
with an error that names the canonical rewrite.

## The variants at a glance

Placeholders (`{keyword}`, `{word}`, `{token}`, …) are substituted with text
from the input, keeping its surface casing.

| Variant | `kind()` | `Display` message |
| --- | --- | --- |
| `Empty` | `empty` | ``the specification is empty: write at least one sentence`` |
| `UnterminatedFrame { keyword }` | `unterminated_frame` | ``the `{keyword}` frame is missing the comma that ends its clause`` |
| `EmptyFrame { keyword }` | `empty_frame` | ``the `{keyword}` frame has an empty clause`` |
| `FrameOrder { keyword, after }` | `frame_order` | ``the `{keyword}` frame must come before {after}: frames read Where, While, then When/If`` |
| `MultipleTriggers { first, second }` | `multiple_triggers` | ``a sentence takes one trigger frame: `{second}` cannot follow `{first}` `` |
| `ThenWithoutIf` | `then_without_if` | `` `then` belongs only after an `If …,` clause`` |
| `FrameOnDefinition { keyword }` | `frame_on_definition` | ``a definition is timeless: only `Where` frames may scope it, not `{keyword}` `` |
| `MidSentenceFrame { keyword }` | `mid_sentence_frame` | `` `{keyword}` appears mid-sentence: conditions lead the sentence, as in `{keyword} …, <subject> shall …` `` |
| `MissingPivot` | `missing_pivot` | ``the sentence has no pivot: expected shall, must, should, may, is, are, or means after the subject`` |
| `UnsupportedModal { word }` | `unsupported_modal` | `` `{word}` is not a supported modal: use shall, must, should, or may — or write capability as `is able to <response>` `` |
| `AmbiguousModal` | `ambiguous_modal` | `` `may not` is ambiguous: write `shall not` for a prohibition`` |
| `NoWithMay` | `no_with_may` | `` `no` with `may` is a denial of permission: write `<subject> shall not <response>` for a prohibition`` |
| `NegatedDescription` | `negated_description` | ``a description is not negated with `not`: write `never`, or `shall not` for an obligation`` |
| `EmptySubject` | `empty_subject` | ``the sentence has no subject before its pivot`` |
| `EmptyVp` | `empty_vp` | ``the modal needs a response: write what the subject shall do`` |
| `EmptyPredicate` | `empty_predicate` | ``the predicate is empty: write what is asserted of the subject`` |
| `EmptyDefiniens` | `empty_definiens` | `` `means` needs a definiens: write what the term stands for`` |
| `MixedCoordination` | `mixed_coordination` | ``a coordination uses one conjunction throughout: `both … and …` or `either … or …`, never mixed`` |
| `UnexpectedTokens { token }` | `unexpected_tokens` | ``unexpected `{token}`: the sentence was complete before it`` |
| `PhraseTooDeep { limit }` | `phrase_too_deep` | ``the phrase nests too deeply: more than {limit} levels of `of` phrases, relative clauses, or `before`/`after` clauses`` |
| `MultipleEventConjuncts` | `multiple_event_conjuncts` | ``a trigger's `and` group takes one event: keep one verbal conjunct and write the others as states (`is/are/remains …`), or move them to a `While` frame`` |
| `LeadingException` | `leading_exception` | `` `unless` cannot open a sentence: the exception follows the core, as in `The pump shall stop, unless the override is active` `` |
| `QuantifierNotWhole { word }` | `quantifier_not_whole` | ``a quantifier counts whole things: `{word}` is not a usable whole number`` |
| `UnknownNumberWord { word }` | `unknown_number_word` | `` `{word}` is not a recognized number word (`zero`–`twenty`, tens to `ninety`, `hundred`; no compounds): write the number in digits`` |
| `ForRequiresMeasure` | `for_requires_measure` | `` `for` opens a duration and needs a quantity, as in `for 5 seconds`: write `about <topic>` for a topic, `until <clause>` to wait on an event, or reword`` |
| `WithIsAmbiguous` | `with_is_ambiguous` | `` `with` is ambiguous between instrument, accompaniment, and attachment: write `using <means>` for an instrument, coordinate the phrases with `and`, restrict with a relative clause (`the file that carries the flag`), or backtick the word (`` `with` ``) to use it as a noun`` |
| `NegatedAlternatives` | `negated_alternatives` | `` `not` does not combine with `either … or …` alternatives: write two prohibitions, one per alternative`` |
| `ByOutsidePassive` | `by_outside_passive` | `` `by` marks a passive agent and belongs after `be <predicate>` or a description's predicate: write `within <measure>` for a deadline, `until <clause>` to wait on an event, or reword the active sentence`` |
| `DeterminerAsVerb { word }` | `determiner_as_verb` | `` `{word}` opens a noun phrase where a verb is required: each response — and each `either … or …` alternative — is a verb phrase, as in `either notify the admin or notify the owner` (for a choice of objects, write `notify either the admin or the owner`)`` |
| `WithinTakesPlainMeasure` | `within_takes_plain_measure` | `` `within` already means an upper bound and takes a plain measure, as in `within 5 seconds`: bounded measures belong to `for` durations (`for at least 30 days`)`` |
| `DescendingBetween { lower, upper }` | `descending_between` | `` `between {lower} and {upper}` is a descending, empty interval: swap the bounds and write `between {upper} and {lower}` `` |
| `AmbiguousVerbBoundary` | `ambiguous_verb_boundary` | ``the verb boundary is ambiguous: the clause reads both subject-verb-object from the minimal subject (`the client | sends | telemetry`) and verb-last from the long subject (`the client sends | telemetry`): put a determiner on the object (`sends the telemetry`), use an of-chain or a relative clause for a long subject (`the sensor of the temperature fails`), or add a role boundary (`fails at the depot`)`` |

## Specification level

### `Empty` — `empty`

- **Message:** `the specification is empty: write at least one sentence`
- **Trigger:** The input contains no sentence at all: an empty string,
  whitespace only, or a sentence that is only its terminator (a lone `.`).
- **Example:**

  ```text
  ""     ->  the specification is empty: write at least one sentence
  "   "  ->  the specification is empty: write at least one sentence
  "."    ->  the specification is empty: write at least one sentence
  ```

- **Fix:** Write at least one full sentence, e.g. `The pump shall stop.`

## Circumstance frames and the exception

### `UnterminatedFrame { keyword }` — `unterminated_frame`

- **Message:** ``the `{keyword}` frame is missing the comma that ends its clause``
- **Trigger:** A frame keyword (`Where`/`While`/`When`/`If`) opens a clause,
  but no comma follows anywhere in the sentence. Each frame clause runs from
  its keyword to the next comma; without one, the clause is never closed.
- **Example:**

  ```text
  "When the order is submitted the system shall record the total."
    ->  the `When` frame is missing the comma that ends its clause
  ```

- **Fix:** Close the clause with the comma:
  `When the order is submitted, the system shall record the total.`

### `EmptyFrame { keyword }` — `empty_frame`

- **Message:** ``the `{keyword}` frame has an empty clause``
- **Trigger:** A frame keyword is immediately followed by its comma, so the
  clause has no words. (`When,` and `When ,` are the same: a trailing comma is
  always split off its word.)
- **Example:**

  ```text
  "When, the pump shall stop."
    ->  the `When` frame has an empty clause
  ```

- **Fix:** Put the clause between the keyword and the comma:
  `When the tank is full, the pump shall stop.`

### `FrameOrder { keyword, after }` — `frame_order`

- **Message:** ``the `{keyword}` frame must come before {after}: frames read Where, While, then When/If``
- **Trigger:** Frames out of canonical order: a `Where` after a `While`, or a
  `Where`/`While` after the trigger (`When`/`If`). Both fields keep the surface
  casing from the input. Repeating `Where` or `While` is legal; only the order
  between the kinds is fixed.
- **Example:**

  ```text
  "While the engine is running, where the premium plan is enabled, the pump shall stop."
    ->  the `where` frame must come before While: frames read Where, While, then When/If
  ```

- **Fix:** Reorder to scopes, then states, then the trigger:
  `Where the premium plan is enabled, while the engine is running, the pump
  shall stop.`

### `MultipleTriggers { first, second }` — `multiple_triggers`

- **Message:** ``a sentence takes one trigger frame: `{second}` cannot follow `{first}` ``
- **Trigger:** A second `When`/`If` frame after a first one. A sentence takes
  at most one trigger.
- **Example:**

  ```text
  "When the order ships, if the balance is negative, the pump shall stop."
    ->  a sentence takes one trigger frame: `if` cannot follow `When`
  ```

- **Fix:** Fold the second condition into a `While` state: `While the balance
  is negative, when the order ships, the pump shall stop.` Split into two
  sentences only if two independent requirements were meant — for a joint
  condition, splitting changes the meaning (each sentence would fire alone).

### `ThenWithoutIf` — `then_without_if`

- **Message:** `` `then` belongs only after an `If …,` clause``
- **Trigger:** `then` directly after a frame's comma when that frame is not an
  `If` clause. (After `If …,` the `then` is optional, consumed, and re-emitted
  on render.)
- **Example:**

  ```text
  "While the engine is running, then the pump shall stop."
    ->  `then` belongs only after an `If …,` clause
  ```

- **Fix:** Drop the `then` — `While the engine is running, the pump shall
  stop.` — or make the frame an `If` clause.

### `FrameOnDefinition { keyword }` — `frame_on_definition`

- **Message:** ``a definition is timeless: only `Where` frames may scope it, not `{keyword}` ``
- **Trigger:** A `While`, `When`, or `If` frame on a sentence whose core is a
  definition (`means`). A definition may be scoped by `Where` frames only; the
  check runs after the whole sentence parses, so the frame itself must be
  well formed.
- **Example:**

  ```text
  "While the engine is running, a workspace means a shared folder."
    ->  a definition is timeless: only `Where` frames may scope it, not `While`
  ```

- **Fix:** Scope the definition with `Where`, or drop the frame:
  `Where the premium plan is enabled, a workspace means a shared folder.`

### `MidSentenceFrame { keyword }` — `mid_sentence_frame`

- **Message:** `` `{keyword}` appears mid-sentence: conditions lead the sentence, as in `{keyword} …, <subject> shall …` ``
- **Trigger:** A frame keyword (`where`/`while`/`when`/`if`/`unless`) inside
  the speech-act core — most often a condition written trailing the sentence,
  or an `unless` missing the comma that separates the exception from the core.
- **Example:**

  ```text
  "The pump shall stop while the engine runs."
    ->  `while` appears mid-sentence: conditions lead the sentence, as in `while …, <subject> shall …`
  "The pump shall stop unless the override is active."
    ->  `unless` appears mid-sentence: conditions lead the sentence, as in `unless …, <subject> shall …`
  ```

- **Fix:** For `where`/`while`/`when`/`if`, move the condition to the front:
  `While the engine runs, the pump shall stop.` For `unless`, keep it after
  the core but add the comma: `The pump shall stop, unless the override is
  active.`

### `LeadingException` — `leading_exception`

- **Message:** `` `unless` cannot open a sentence: the exception follows the core, as in `The pump shall stop, unless the override is active` ``
- **Trigger:** `unless` where the core should begin — opening the sentence, or
  directly after the leading frames. The exception is the one clause that
  trails the core instead of leading it.
- **Example:**

  ```text
  "Unless the override is active, the pump shall stop."
    ->  `unless` cannot open a sentence: the exception follows the core, as in `The pump shall stop, unless the override is active`
  ```

- **Fix:** Move the exception after the core:
  `The pump shall stop, unless the override is active.`

## The speech-act core

### `MissingPivot` — `missing_pivot`

- **Message:** `the sentence has no pivot: expected shall, must, should, may, is, are, or means after the subject`
- **Trigger:** The core contains none of the seven pivot keywords after its
  subject phrase, so no speech act can be recognized.
- **Example:**

  ```text
  "The pump quickly."
    ->  the sentence has no pivot: expected shall, must, should, may, is, are, or means after the subject
  ```

- **Fix:** Pivot the sentence on a modal, a copula, or `means`:
  `The pump shall stop quickly.`

### `UnsupportedModal { word }` — `unsupported_modal`

- **Message:** `` `{word}` is not a supported modal: use shall, must, should, or may — or write capability as `is able to <response>` ``
- **Trigger:** One of the deliberately excluded modals — `can`, `will`,
  `would`, `could`, `might`, `ought` — at the pivot position. Each blurs
  ability, prediction, or hedging into the normative claim, so none has one
  machine-checkable meaning. The surface casing of the word is preserved.
- **Example:**

  ```text
  "The client can retry."
    ->  `can` is not a supported modal: use shall, must, should, or may — or write capability as `is able to <response>`
  ```

- **Fix:** Say what is meant: `may` for permission, `shall`/`must` for an
  obligation, `should` for a recommendation — `The client may retry.` When
  `can` really meant ability rather than permission, the faithful rewrite is
  now a capability description: `The client is able to retry.`

### `AmbiguousModal` — `ambiguous_modal`

- **Message:** `` `may not` is ambiguous: write `shall not` for a prohibition``
- **Trigger:** `not` directly after `may`. English reads `may not` both as a
  prohibition and as a permission that can be withheld, so the language
  rejects it outright.
- **Example:**

  ```text
  "The client may not retry."
    ->  `may not` is ambiguous: write `shall not` for a prohibition
  ```

- **Fix:** `The client shall not retry.` for a prohibition; for the absence of
  permission, state the permission the other way around.

### `NoWithMay` — `no_with_may`

- **Message:** `` `no` with `may` is a denial of permission: write `<subject> shall not <response>` for a prohibition``
- **Trigger:** A `may` core whose subject carries the determiner `no` on any
  of its (possibly coordinated) items. In specification English `No client
  may retry.` is a prohibition — a denial of permission — not the record of
  an admissibility; the grammar has no negative admissibility, so read as a
  permission the sentence would record the opposite of what its author
  denied. The same legislated-ambiguity family
  as `may not`. Only the subject's own determiner counts: `no` inside an
  `of`-chain or in object position does not trigger it.
- **Example:**

  ```text
  "No client may retry."
    ->  `no` with `may` is a denial of permission: write `<subject> shall not <response>` for a prohibition
  ```

- **Fix:** `The client shall not retry.` (or `Each client shall not retry.`
  for the explicit universal) — a prohibition, with the negation carried by
  `shall not`.

### `NegatedDescription` — `negated_description`

- **Message:** ``a description is not negated with `not`: write `never`, or `shall not` for an obligation``
- **Trigger:** `not` after the copula of a description (`is not` / `are not`),
  including after an adverb (`is always not`). A description states what
  holds; its only negative form is the adverb `never`.
- **Example:**

  ```text
  "The sales amount is not greater than zero."
    ->  a description is not negated with `not`: write `never`, or `shall not` for an obligation
  ```

- **Fix:** `The sales amount is never greater than zero.` as a description, or
  `The sales amount shall not be greater than zero.` as a prohibition.

### `EmptySubject` — `empty_subject`

- **Message:** `the sentence has no subject before its pivot`
- **Trigger:** A pivot (or excluded modal) with no subject phrase before it:
  the core opens with the pivot, or the material before it is only a
  determiner. The same diagnosis applies inside a frame clause whose copula or
  verb has no subject (`When is submitted, …`).
- **Example:**

  ```text
  "The shall run."   ->  the sentence has no subject before its pivot
  "shall run."       ->  the sentence has no subject before its pivot
  ```

- **Fix:** Name the subject: `The engine shall run.`

### `EmptyVp` — `empty_vp`

- **Message:** `the modal needs a response: write what the subject shall do`
- **Trigger:** A modal (with or without `not`) followed by nothing.
- **Example:**

  ```text
  "The pump shall."      ->  the modal needs a response: write what the subject shall do
  "The pump shall not."  ->  the modal needs a response: write what the subject shall do
  ```

- **Fix:** State the response after the modal: `The pump shall stop.`

### `EmptyPredicate` — `empty_predicate`

- **Message:** `the predicate is empty: write what is asserted of the subject`
- **Trigger:** A copula or comparison site with nothing after it: `is`/`are`
  at the end of the sentence, a comparison operator without its measure
  (`greater than.`), or a predicate preposition without its phrase (`in.`).
- **Example:**

  ```text
  "The pump is."                  ->  the predicate is empty: write what is asserted of the subject
  "The delay is greater than."    ->  the predicate is empty: write what is asserted of the subject
  ```

- **Fix:** Complete the predicate: `The pump is idle.` /
  `The delay is greater than zero.`

### `EmptyDefiniens` — `empty_definiens`

- **Message:** `` `means` needs a definiens: write what the term stands for``
- **Trigger:** `means` with nothing after it.
- **Example:**

  ```text
  "A session means."
    ->  `means` needs a definiens: write what the term stands for
  ```

- **Fix:** Write what the term stands for:
  `A session means a sequence of requests.`

## The phrase grammar

### `MixedCoordination` — `mixed_coordination`

- **Message:** ``a coordination uses one conjunction throughout: `both … and …` or `either … or …`, never mixed``
- **Trigger:** Any ill-formed coordination in a single noun-phrase group:
  `and` and `or` mixed (`the total and the tax or the fee`), two conjunctions
  in a row (`and or`), a `both` not paired with `and` over exactly two items,
  an `either` not paired with `or` over exactly two items, or a `both`/
  `either` marker with no conjunction at all. A mixed group has no single
  grouping, so no reading is chosen for the author. Clause coordination
  inside one frame is held to the same rule: `When the order ships and the
  payment clears or the invoice posts,` mixes the frame's conjunctions and is
  rejected the same way.
- **Example:**

  ```text
  "The system shall record the total and the tax or the fee."
    ->  a coordination uses one conjunction throughout: `both … and …` or `either … or …`, never mixed
  ```

- **Fix:** Use one conjunction per group — `the total and the tax and the
  fee` — or split into sentences. Unmarked groups may have any number of
  items; `both … and …` and `either … or …` take exactly two.

### `UnexpectedTokens { token }` — `unexpected_tokens`

- **Message:** ``unexpected `{token}`: the sentence was complete before it``
- **Trigger:** Well-formed material followed by tokens the grammar cannot
  place. `{token}` is the first offending token — a word, `,`, `.`, or
  `end of sentence` when a phrase was truncated where more was required.
  Typical cases:
  - stray words after a complete core, in a comma segment that is neither an
    exception nor a purpose: `The pump shall stop, quickly.` → `` `quickly` ``;
  - a second `unless` segment, or an `unless` after the purpose:
    → `` `unless` `` (one exception, then one purpose, in that order);
  - a coordinated definition term — `A pump and a valve means a machine.` →
    `` `and` `` (a coordinated term has no single definition; write one
    sentence per term);
  - `of` or a preposition with nothing after it:
    `The pump shall stop the flow of.` → `end of sentence`;
  - a particle followed by `of` — a particle never combines with a
    following `of` (there is no `out of` chain), so `The pump shall run out
    of water.` → `` `of` ``;
  - a period inside the sentence (`the total., unless …`) → `` `.` ``.
- **Example:**

  ```text
  "A pump and a valve means a machine."
    ->  unexpected `and`: the sentence was complete before it
  ```

- **Fix:** Remove or complete the stray material:
  `A pump means a machine. A valve means a machine.`

### `PhraseTooDeep { limit }` — `phrase_too_deep`

- **Message:** ``the phrase nests too deeply: more than 64 levels of `of` phrases, relative clauses, or `before`/`after` clauses``
- **Trigger:** A phrase nesting through `of` links, relative clauses, or
  `before`/`after` clauses past the recognizer's depth budget (`limit` is
  always 64, the compiled `MAX_NP_DEPTH`). The bound exists to keep the recognizer total on
  adversarially deep input — recursion depth is otherwise proportional to
  input length; no sentence a person writes nests anywhere near it.
- **Example:**

  ```text
  "The size of the box of the box of … (65+ `of` links) … shall shrink."
    ->  the phrase nests too deeply: more than 64 levels of `of` phrases, relative clauses, or `before`/`after` clauses
  ```

- **Fix:** Break the chain: name the intermediate thing with a definition and
  refer to it.

### `MultipleEventConjuncts` — `multiple_event_conjuncts`

- **Message:** ``a trigger's `and` group takes one event: keep one verbal conjunct and write the others as states (`is/are/remains …`), or move them to a `While` frame``
- **Trigger:** An `and` clause group under `When`/`If` with two or more
  verbal (event) conjuncts. The conjunction of two occurrences is
  simultaneity — the same reading the one-trigger rule refuses: at once? in
  sequence? within some window? `or` groups are exempt (a disjunction of
  events is alternation: either occurrence triggers, which is well-defined),
  and `While`/`Where` groups are unrestricted (their clauses are states and
  scopes, not occurrences).
- **Example:**

  ```text
  "When the order ships and the payment clears, the system shall issue the receipt."
    ->  a trigger's `and` group takes one event: keep one verbal conjunct and write the others as states (`is/are/remains …`), or move them to a `While` frame
  ```

- **Fix:** Keep one event and read the rest as states at its instant — `When
  the order ships and the payment is cleared, …` — or carry the second
  circumstance in its own state frame: `While the payment clears, when the
  order ships, …`. If the intent is a *sequence*, order the trigger event
  with an `after` role instead of conjoining: `When the payment clears
  after the order ships, …`.

### `QuantifierNotWhole { word }` — `quantifier_not_whole`

- **Message:** ``a quantifier counts whole things: `{word}` is not a usable whole number``
- **Trigger:** A quantifier opener (`at least` / `at most` / `exactly`) in
  noun-phrase position whose number token is numeric but not countable — a
  decimal, or an integer beyond 64 bits. Letting the words fall through as
  open-class material would silently erase the quantifier from the tree, so
  the phrase is an error instead. Measures are unaffected: numbers in measure
  position are kept as written, so `within 5.5 seconds` and the comparison
  `is at least 2.5 seconds` both parse.
- **Example:**

  ```text
  "At least 2.5 nodes shall respond."
    ->  a quantifier counts whole things: `2.5` is not a usable whole number
  ```

- **Fix:** Count whole things — `At least 3 nodes shall respond.` — or state
  the fraction as a measure: `The delay is at least 2.5 seconds.`

### `UnknownNumberWord { word }` — `unknown_number_word`

- **Message:** `` `{word}` is not a recognized number word (`zero`–`twenty`, tens to `ninety`, `hundred`; no compounds): write the number in digits``
- **Trigger:** A word-shaped token (ASCII letters and hyphens) in a
  position that requires a number — after a quantifier opener (`at least` /
  `at most` / `exactly`), after `within`, or after a bound opener under
  `for` — that is neither a numeral nor a word from the number table
  (round 12: `zero`–`twenty`, the tens `thirty`–`ninety`, `hundred`;
  single words only, so compounds like `twenty-one` land here too).
  Before round 12, `at least eleven nodes` silently degraded the
  quantifier into open-class modifier words and `within eleventy seconds`
  became a noun-phrase measure that never grounds an interval —
  accepted-but-wrong trees; `eleven` now parses, and everything outside
  the table fails closed. Determiner-led phrases and reserved words are
  exempt (legislated): `within the timeout` keeps its noun-phrase
  measure, `for at least the limit` keeps `ForRequiresMeasure`.
- **Example:**

  ```text
  "At least eleventy nodes shall run."
    ->  `eleventy` is not a recognized number word (`zero`–`twenty`, tens to `ninety`, `hundred`; no compounds): write the number in digits
  ```

- **Fix:** Write digits — `At least 110 nodes shall run.` — or use a word
  from the table: `At least eleven nodes shall run.`

### `ForRequiresMeasure` — `for_requires_measure`

- **Message:** `` `for` opens a duration and needs a quantity, as in `for 5 seconds`: write `about <topic>` for a topic, `until <clause>` to wait on an event, or reword``
- **Trigger:** A role-position `for` not followed by a quantity — a number
  (numeral or number word, see [lexical.md](./lexical.md#number-words-and-numerals)) with an optional unit, plain or
  BOUNDED (round 6): `for 5 seconds`, `for at least 30 days`, `for at most
  5 seconds`, `for greater than 3 days`, `for less than 2 hours`, `for
  between 5 and 10 seconds`. Before round 5, `listen for requests`
  silently parsed as a Duration over a noun phrase — an accepted-but-wrong
  tree; a duration requires a quantity measure. `within` (Deadline) still
  admits a noun-phrase measure (`within the grace period`) and keeps the
  PLAIN quantity only — `within` already means an upper bound, so bounded
  forms are `for`-only (legislated); a bound opener after `within` is its
  own rejection, [`WithinTakesPlainMeasure`](#withintakesplainmeasure--within_takes_plain_measure)
  (round 6 follow-up). A bound over a noun phrase (`for at
  least the grace period`) and `for equal to 5 seconds` (redundant with
  `for 5 seconds`) still trigger this error.
- **Example:**

  ```text
  "The daemon shall listen for requests."
    ->  `for` opens a duration and needs a quantity, as in `for 5 seconds`: …
  ```

- **Fix:** For a real duration, quantify it (`for 30 days`, `for five
  seconds`). For a topic, write `about requests`. To wait on an event,
  write `until a request arrives`. Otherwise reword the response.

### `WithIsAmbiguous` — `with_is_ambiguous`

- **Message:** `` `with` is ambiguous between instrument, accompaniment, and attachment: write `using <means>` for an instrument, coordinate the phrases with `and`, restrict with a relative clause (`the file that carries the flag`), or backtick the word (`` `with` ``) to use it as a noun``
- **Trigger:** `with` where a thematic role could start (after a verb
  phrase's or verbal clause body's object), and — round 6 — bare `with`
  inside ANY noun phrase, plain subject positions included. Before round 5
  the word was swallowed into the object noun phrase (`notify the user
  with the report` became one flat object); before round 6, a plain
  subject folded it into the modifiers, pinning `The file with the flag`
  to head `flag` — accepted-but-wrong, now rejected under the same
  ambiguity discipline. Description predicate WORDS are not noun phrases,
  so `The pump is compatible with the valve.` keeps its open-words
  predicate (documented leave-alone). A backticked `` `with` `` is an
  ordinary noun everywhere.
- **Example:**

  ```text
  "The daemon shall notify the user with the report."
    ->  `with` is ambiguous between instrument, accompaniment, and attachment: …
  "The file with the flag shall be archived."
    ->  (round 6) the same rejection, in subject position
  ```

- **Fix:** Instrument: `The daemon shall sign the report using the key.`
  Accompaniment: coordinate — `The daemon shall send the user and the
  report …`. Attachment/restriction: use an `of`-chain or a relative
  clause — `The file that carries the flag shall be archived.` Noun use of
  the word itself: backtick it — `` The `with` clause shall be
  documented. ``

### `ByOutsidePassive` — `by_outside_passive`

- **Message:** `` `by` marks a passive agent and belongs after `be <predicate>` or a description's predicate: write `within <measure>` for a deadline, `until <clause>` to wait on an event, or reword the active sentence``
- **Trigger:** A role-position `by` outside a passive site. The passive
  sites are: a `be` verb phrase WITH a complement (`shall be logged by the
  daemon`), a description's predicate (`is logged by the daemon`), and a
  copular clause body (`when the request is submitted by the user,`) —
  there `by <np-group>` is the Agent role/slot. Active verb phrases and
  verbal clause bodies take no agent, and a bare `be` with no complement
  has nothing passive in it, so the locative `The daemon shall be by the
  dock.` is rejected rather than misread as an agent.
- **Example:**

  ```text
  "The daemon shall respond by Friday."
    ->  `by` marks a passive agent and belongs after `be <predicate>` …
  ```

- **Fix:** Deadline: `The daemon shall respond within 5 seconds.` Waiting:
  `… until the review closes.` Otherwise keep the sentence active and name
  the channel or means with `via`/`using`, or rewrite in the passive if the
  agent is the point.

### `NegatedAlternatives` — `negated_alternatives`

- **Message:** `` `not` does not combine with `either … or …` alternatives: write two prohibitions, one per alternative``
- **Trigger:** `shall not either <vp> or <vp>` (round 6). Negation over an
  alternation has two readings a reader will disagree on — "must do
  neither" (De Morgan) vs "is not obliged to choose" — so the grammar
  rejects the combination at ingest instead of picking one silently.
- **Example:**

  ```text
  "The server shall not either accept the request or reject the request."
    ->  `not` does not combine with `either … or …` alternatives: …
  ```

- **Fix:** Write the intended prohibitions separately: `The server shall
  not accept the request. The server shall not reject the request.` (Two
  prohibition sentences conjoin — exactly the "neither" reading, stated
  without a scope ambiguity.)

### `DeterminerAsVerb` — `determiner_as_verb`

- **Message:** `` `{word}` opens a noun phrase where a verb is required: each response — and each `either … or …` alternative — is a verb phrase, as in `either notify the admin or notify the owner` (for a choice of objects, write `notify either the admin or the owner`)``
- **Trigger:** A determiner (or counting quantifier) at the start of any
  verb phrase (round 6 follow-up): directly after the modal (`The pump
  shall the valve.`), after `is able to`, and — the exposed round-6
  surface — as the TAIL of an `either … or …` alternative (`The server
  shall either notify the admin or the owner.`), which used to parse with
  the word `the` as an open-class VERB — an accepted-but-wrong tree that
  even round-tripped its render. Round 7 (attack fix) extends the gate to
  EVERY verbal tail, verbal relative bodies and verbal clause bodies
  included. Round 9: well-formed OBJECT-GAP relatives are now part of the
  grammar (`Each request that the gateway forwards shall be logged.`
  parses — see
  [phrases.md](./phrases.md#restrictive-relative-clauses)), so this
  rejection no longer covers them; it still fires exactly where the gap
  reading refuses — a determiner-led relative with an explicit object
  (determiner/quantifier-led, group-marked, or a bare number) after a
  candidate verb (`each request that the gateway forwards the packet` —
  the head is not the missing object) or with no
  verb-position word at all (`each request that the gateway`).
- **Example:**

  ```text
  "The server shall either notify the admin or the owner."
    ->  `the` opens a noun phrase where a verb is required: …
  ```

- **Fix:** Give every alternative its own verb — `The server shall either
  notify the admin or notify the owner.` For a choice of objects under one
  verb, move `either` into object position: `The server shall notify
  either the admin or the owner.`

### `WithinTakesPlainMeasure` — `within_takes_plain_measure`

- **Message:** `` `within` already means an upper bound and takes a plain measure, as in `within 5 seconds`: bounded measures belong to `for` durations (`for at least 30 days`)``
- **Trigger:** A bound opener (`at least`, `at most`, `greater than`,
  `less than`, `between`) after a role-position `within` (round 6
  follow-up). `within at least 5 seconds` used to be silently consumed as
  a counted noun-phrase measure (`at least 5` as the determiner of
  `seconds`) — an accepted-but-misleading tree that never grounds an
  interval, and an asymmetry with `for`, which errors loudly on the same
  surface. Plain quantities (`within 5 seconds`) and noun-phrase value
  names (`within the grace period`) are unaffected.
- **Example:**

  ```text
  "The daemon shall reply within at least 5 seconds."
    ->  `within` already means an upper bound and takes a plain measure: …
  ```

- **Fix:** For a deadline, keep the plain measure: `within 5 seconds.`
  For a lower-bounded duration, use `for`: `for at least 5 seconds.`

### `DescendingBetween` — `descending_between`

- **Message:** `` `between {lower} and {upper}` is a descending, empty interval: swap the bounds and write `between {upper} and {lower}` ``
- **Trigger:** A `between` whose two bounds are both numeric (numerals —
  decimals included — or number words) with the LOWER strictly greater
  than the UPPER (round 9): `between 6 and 4 seconds` denotes the empty
  interval — a claim that can never hold and, under the interval rules,
  contradicts everything including itself. Nobody writes an empty
  interval on purpose, so the shape is a typo and the recognizer rejects
  it instead of freezing an unsatisfiable claim (superseding the round-6
  doctrine that documented the empty interval instead of policing it).
  Applies to comparison predicates and bounded `for` durations alike.
  EQUAL bounds are a point interval — accepted — and noun-phrase bounds
  (`between the floor and the ceiling`) are value names, never checked.
  Hand-built trees can still hold an empty interval; the relation
  engine's satisfiability machinery keeps covering those.
- **Example:**

  ```text
  "The latency is between 6 and 4."
    ->  `between 6 and 4` is a descending, empty interval: swap the bounds and write `between 4 and 6`
  ```

- **Fix:** Swap the bounds: `between 4 and 6.` The same fix applies to
  durations: `for between 10 and 30 days.`

### `AmbiguousVerbBoundary` — `ambiguous_verb_boundary`

- **Message:** ``the verb boundary is ambiguous: the clause reads both subject-verb-object from the minimal subject (`the client | sends | telemetry`) and verb-last from the long subject (`the client sends | telemetry`): put a determiner on the object (`sends the telemetry`), use an of-chain or a relative clause for a long subject (`the sensor of the temperature fails`), or add a role boundary (`fails at the depot`)``
- **Trigger:** A verbal clause whose subject region is boundary-less — no
  determiner-led object, no role or locative preposition, no of-chain or
  relative structure — and whose trailing bare-word run has two or more
  words after the *minimal* subject with a verb-capable first word
  (round 11, FAIL-CLOSED; supersedes the round-10 SVO acceptance and the
  round-3 final-word acceptance for exactly this class). The run admits
  both readings — minimal-subject SVO and long-subject final-word — the
  two scramble each other's intended sentences, and no lexicon-free rule
  can pick the intended split, so accepted-but-wrong yields to rejection
  (the `with`/`for`/`by` discipline). Class membership is decided by
  SHAPE, never by attempting both parses. Length-1 runs (`a session
  expires`), det-led two-word slices (`the pump runs` — the readings
  coincide), runs whose first word cannot be a verb (`the power up
  fails`), structured subjects, and role-boundaried shapes all keep
  their readings. Particle and bare-number finals keep theirs only when
  popping the final token leaves a run OUTSIDE the class: `the user
  logs out` and `the counter reaches zero` stand, while `the client
  sends telemetry out` and `the counter reaches stage zero` reject —
  the pop must not reopen the frontier. Pre-verbal manner words are
  SKIPPED, not frontier-closing: `the client quickly sends telemetry`
  rejects like its manner-less twin (an `ly` word is never the verb,
  but it does not disambiguate the split either). And the rejection is
  FINAL when it arises inside a content `that`-clause whose enclosing
  split is well-formed: `When the monitor confirms that the client
  sends telemetry,` rejects — the noun-phrase-first fallback must not
  re-read the content clause as an object-gap relative of a longer
  subject.
- **Example:**

  ```text
  "When the client sends telemetry, the daemon shall persist the Node."
    ->  the verb boundary is ambiguous: …
  ```

- **Fix:** Put a determiner on the object: `When the client sends the
  telemetry,`. For a long subject, use an of-chain or a relative clause:
  `When the sensor of the temperature fails,`. Or add a role boundary
  after the verb: `When the temperature sensor fails at the depot,`.

## How errors surface in `spec add`

The grammar is a hard gate, checked first. `specd` parses the specification at
the start of ingest (`so_daemon/src/add.rs`), before any evidence
normalization, snapshot, or store access — a syntax error preempts evidence
capture entirely: no locator is read, no snapshot is taken, and nothing is
persisted.

- The daemon rejects the specification with the message
  `syntax error in specification: <message>`, where `<message>` is the exact
  `Display` text from the tables above, and the `spec` CLI prints it on
  stderr.
- The process exits with **code 2** (`EXIT_USAGE` in `so_cli/src/main.rs`):
  bad input the caller can fix. The same exit code covers an evidence/locator
  syntax error; a specification syntax error simply happens first. Runtime
  failures (connection, capture, store) exit with code 1.
- On telemetry spans the daemon records the stable `kind()` name as
  `spec.parse.error.kind`, so rejection rates can be broken down by variant
  without capturing specification text.

Fixing the reported error is therefore a prerequisite for the specification
being ingested at all.

## See also

- [README.md](./README.md) — the speech-act cores, frames, exceptions, and
  purposes these errors guard, and the total-recognizer philosophy.
- [cookbook.md](./cookbook.md) — accepted and rejected specifications side by
  side.
- [`so_lang/src/parse.rs`](../../so_lang/src/parse.rs) — the `ParseError` enum,
  its messages, and `kind()`.
