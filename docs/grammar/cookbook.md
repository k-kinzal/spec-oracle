# Examples cookbook

> Part of the [grammar reference](./README.md).

A skimmable gallery of statements that the [total recognizer](./README.md#philosophy-a-total-recognizer)
accepts and rejects. Each accepted row shows the projected
[assumption and guarantee](./projection.md); each rejected row shows the
[`ParseError`](./errors.md) variant and a one-phrase reason. Every example here is
a test case in [`so_lang/src/grammar.rs`](../../so_lang/src/grammar.rs) or is traced directly
through the parsing algorithm — for the rules behind them, follow the links to
[lexical.md](./lexical.md) and [errors.md](./errors.md).

## Accepted

The assumption is `⊤` (Top) for the Ubiquitous form, or the list of condition
clauses (each a `keyword` + `text` pair) for the Conditional and Complex forms.

| Input | Form | Assumption | subject | response |
| --- | --- | --- | --- | --- |
| `The sales amount shall be greater than zero.` | Ubiquitous | `⊤` | `sales amount` | `be greater than zero` |
| `The pump shall stop` | Ubiquitous | `⊤` | `pump` | `stop` |
| `The marshalling yard shall be clear.` | Ubiquitous | `⊤` | `marshalling yard` | `be clear` |
| `The café shall serve crêpes.` | Ubiquitous | `⊤` | `café` | `serve crêpes` |
| `AddContract shall return the persisted node.` | Ubiquitous | `⊤` | `AddContract` | `return the persisted node` |
| `The daemon crate must provide the specd binary.` | Ubiquitous | `⊤` | `daemon crate` | `provide the specd binary` |
| `The tracing library should install TraceContext and Baggage propagators.` | Ubiquitous | `⊤` | `tracing library` | `install TraceContext and Baggage propagators` |
| `The shall clause shall become the guarantee.` | Ubiquitous | `⊤` | `shall clause` | `become the guarantee` |
| `The should clause should become the guarantee.` | Ubiquitous | `⊤` | `should clause` | `become the guarantee` |
| `The shoulder harness should lock.` | Ubiquitous | `⊤` | `shoulder harness` | `lock` |
| `When the order is submitted, the system shall record the total.` | Conditional | `When` → `the order is submitted` | `system` | `record the total` |
| `When OpenTelemetry is enabled, the tracing library should install TraceContext and Baggage propagators.` | Conditional | `When` → `OpenTelemetry is enabled` | `tracing library` | `install TraceContext and Baggage propagators` |
| `If the balance is negative, then the account shall be frozen.` | Conditional | `If` → `the balance is negative` | `account` | `be frozen` |
| `when the order ships, the system shall notify the customer` | Conditional | `when` → `the order ships` | `system` | `notify the customer` |
| `When the café is open, the barista shall greet the guest.` | Conditional | `When` → `the café is open` | `barista` | `greet the guest` |
| `While the engine is running, when the temperature exceeds the limit, the controller shall open the valve.` | Complex | `While` → `the engine is running`; `when` → `the temperature exceeds the limit` | `controller` | `open the valve` |

Notes on the non-obvious rows:

- **`The pump shall stop`** — the trailing period is optional; the statement
  parses with or without it.
- **`The marshalling yard shall be clear.`** — the `shall` inside `marshalling`
  is **not** the modal (it is preceded by an alphanumeric `r`), so the real modal
  wins and the subject is `marshalling yard`. See the
  [word-boundary rules](./lexical.md).
- **`The café shall serve crêpes.`** — non-ASCII subject and response are captured
  verbatim; the recognizer is [multibyte-safe](./lexical.md).
- **`AddContract shall ...`** — the guarantee subject can be a natural technical
  noun phrase without a leading determiner.
- **`... must ...` / `... should ...`** — `must` and `should` are accepted as
  guarantee modals alongside `shall`.
- **`The shall clause ... shall ...` / `The should clause ... should ...`** — the
  first modal candidate would leave an empty subject, so the later modal
  candidate is selected.
- **`The shoulder harness should lock.`** — the `should` inside `shoulder` is
  not the modal; the later whole-word `should` is.
- **`If the balance is negative, then the account shall be frozen.`** — the
  optional `then` after the clause comma is dropped from the guarantee.
- **`when the order ships, ...`** — the keyword's **surface casing** is preserved
  (`when`, not normalized to `When`).
- **The Complex example** — two leading clauses are conjoined in order; both must
  hold for the guarantee to apply. See the [projection](./projection.md#assumption-the-conjunction-of-the-condition-clauses).

## Rejected

| Input | `ParseError` | Reason |
| --- | --- | --- |
| `   ` | `Empty` | blank after trimming |
| `.` | `Empty` | nothing left once the trailing period is stripped |
| `The sales amount is always greater than zero.` | `MissingModal` | no `shall`, `must`, or `should` anywhere |
| `When the order is submitted the system shall record the total.` | `MissingComma { keyword: "When" }` | condition clause never closed by a comma |
| `The shall run.` | `EmptySubject` | no usable modal leaves a non-empty subject |
| `The pump shall.` | `EmptyResponse` | no usable modal leaves a non-empty response |
| `When , the pump shall stop.` | `EmptyCondition { keyword: "When" }` | condition clause has no text before the comma |

For the exact `Display` message of each variant, its trigger, and the exit code,
see [errors.md](./errors.md).

## Common mistakes → fix

Each fix turns one of the rejected inputs above into an accepted statement.

| Mistake | Rejected | Fix | Accepted |
| --- | --- | --- | --- |
| No modal — a bare verb phrase | `The sales amount is always greater than zero.` | State the response with `shall`, `must`, or `should` | `The sales amount shall be greater than zero.` |
| Missing comma after the condition | `When the order is submitted the system shall record the total.` | Close the condition clause with a comma | `When the order is submitted, the system shall record the total.` |
| No subject before the modal | `The shall run.` | Name the subject | `The pump shall run.` |
| No response after the modal | `The pump shall.` | State the response | `The pump shall stop.` |
| Empty condition text | `When , the pump shall stop.` | Fill in the condition, or drop the keyword for the Ubiquitous form | `When the tank is full, the pump shall stop.` |

Two traps worth calling out, both from the [lexical rules](./lexical.md):

- **A condition clause cannot contain a comma.** The clause ends at the **first**
  comma, so an intended comma inside the condition splits it and the following
  fragment must parse as a guarantee.
- **A keyword only counts when followed by whitespace.** `Whenever ...` is not the
  keyword `When`, and `If,` is not the keyword `If` — the keyword must be followed
  by a space. See [lexical.md](./lexical.md) for the `starts_with_word` vs
  `find_word_from` boundary asymmetry.
