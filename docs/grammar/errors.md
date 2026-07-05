# Syntax errors (ParseError taxonomy)

> Part of the [grammar reference](./README.md).

The grammar is a **total recognizer**: every input either parses into exactly one
`Contract` or is rejected with a precise error. A `ParseError` is therefore the
**only** way a statement fails to produce a contract — there is no "low
confidence" middle ground, no partial parse, and no human review. If `parse`
returns `Err`, the statement is not in the language and nothing downstream runs.

Every variant carries a fixed, human-readable `Display` message. The seven
variants below are exhaustive; each states the exact message, what triggers it,
a minimal example, and how to fix it. The rules each error enforces are defined
in [forms.md](./forms.md) and [lexical.md](./lexical.md).

## The seven variants at a glance

Placeholders (`<keyword>`, `<found>`) are substituted with text from the input.

| Variant | `Display` message | Triggered when |
| --- | --- | --- |
| `Empty` | `statement is empty` | Input is blank, or reduces to blank after trimming and stripping one trailing period. |
| `MissingComma` | `a condition clause opened with '<keyword>' must be closed by a comma before the guarantee clause` | A condition keyword opens a clause but no comma closes it. |
| `EmptyCondition` | `condition clause opened with '<keyword>' has no text` | A condition keyword is followed only by whitespace before its closing comma. |
| `MissingModal` | `the guarantee clause must be of the form 'the <subject> shall <response>' but no 'shall' was found` | The guarantee clause contains no `shall` as a whole word. |
| `MissingDeterminer` | `the guarantee clause must start with the determiner 'the' but starts with '<found>'` | The guarantee clause does not open with `the` (but a `shall` is present). |
| `EmptySubject` | `the guarantee clause has no subject between 'the' and 'shall'` | Nothing sits between the determiner `the` and the modal `shall`. |
| `EmptyResponse` | `the guarantee clause has no response after 'shall'` | Nothing follows the modal `shall`. |

## Per-variant detail

### `Empty`

- **Message:** `statement is empty`
- **Trigger:** After `input.trim()` the statement is empty, or it becomes empty
  after stripping at most one trailing `.` and trimming again. So both a blank
  string and a lone period reduce to empty.
- **Example:**

  ```text
  "   "  ->  statement is empty
  "."    ->  statement is empty
  ```

- **Fix:** Write a full statement in one of the three [forms](./forms.md), e.g.
  `The pump shall stop.`

### `MissingComma`

- **Message:** `a condition clause opened with '<keyword>' must be closed by a comma before the guarantee clause`
  (`<keyword>` is the surface spelling from the input, e.g. `When`).
- **Trigger:** The text opens with a condition keyword (`While` / `When` / `If` /
  `Where`, followed by whitespace), but there is no comma to end the clause. Each
  condition clause runs from its keyword to the **first** comma; with no comma the
  clause is never closed.
- **Example:**

  ```text
  "When the order is submitted the system shall record the total."
    ->  a condition clause opened with 'When' must be closed by a comma before the guarantee clause
  ```

- **Fix:** Insert the comma that separates the condition from the guarantee:
  `When the order is submitted, the system shall record the total.` Note that a
  single condition clause cannot itself contain a comma — the first comma always
  ends it (see [lexical.md](./lexical.md)).

### `EmptyCondition`

- **Message:** `condition clause opened with '<keyword>' has no text`
- **Trigger:** A condition keyword is present and a comma closes it, but the text
  between the keyword and the comma is empty (or only whitespace).
- **Example:**

  ```text
  "When , the pump shall stop."
    ->  condition clause opened with 'When' has no text
  ```

- **Fix:** Supply the condition phrase between the keyword and the comma:
  `When the tank is full, the pump shall stop.`

### `MissingModal`

- **Message:** `the guarantee clause must be of the form 'the <subject> shall <response>' but no 'shall' was found`
- **Trigger:** The guarantee clause contains no `shall` as a whole word.
  `shall` is matched with alphanumeric boundaries on both sides, so an inner
  `shall` inside another word (e.g. `marshalling`) does **not** count as the
  modal. This is also the error you get when the whole statement simply omits the
  modal.
- **Example:**

  ```text
  "The sales amount is always greater than zero."
    ->  the guarantee clause must be of the form 'the <subject> shall <response>' but no 'shall' was found
  ```

- **Fix:** Pivot the guarantee on the modal `shall`:
  `The sales amount shall be greater than zero.`

### `MissingDeterminer`

- **Message:** `the guarantee clause must start with the determiner 'the' but starts with '<found>'`
  (`<found>` is the first whitespace-delimited token of the clause, e.g. `System`).
- **Trigger:** The guarantee clause does not open with the determiner `the` (as a
  word, followed by whitespace), **and** a `shall` is present. If both the
  determiner and the modal are missing, the missing modal is reported instead —
  see [Precedence](#precedence-missing-modal-before-missing-determiner) below.
- **Example:**

  ```text
  "System shall record the total."
    ->  the guarantee clause must start with the determiner 'the' but starts with 'System'
  ```

- **Fix:** Open the guarantee clause with `the`:
  `The system shall record the total.`

### `EmptySubject`

- **Message:** `the guarantee clause has no subject between 'the' and 'shall'`
- **Trigger:** The clause opens with `the` and contains `shall`, but the text
  between them is empty.
- **Example:**

  ```text
  "The shall run."
    ->  the guarantee clause has no subject between 'the' and 'shall'
  ```

- **Fix:** Name the subject between the determiner and the modal:
  `The engine shall run.`

### `EmptyResponse`

- **Message:** `the guarantee clause has no response after 'shall'`
- **Trigger:** The clause opens with `the` and contains `shall`, a non-empty
  subject precedes the modal, but nothing follows the modal.
- **Example:**

  ```text
  "The pump shall."
    ->  the guarantee clause has no response after 'shall'
  ```

- **Fix:** State the response after `shall`: `The pump shall stop.`

## Precedence: missing modal before missing determiner

When the guarantee clause does **not** open with the determiner `the`, the parser
first checks whether a `shall` exists anywhere in the clause:

- If **no** `shall` is present, it reports `MissingModal` — the absent modal is
  treated as the more fundamental defect and is reported *before* the missing
  determiner.
- Only if a `shall` **is** present does it report `MissingDeterminer`.

So a clause that lacks both surfaces as `MissingModal`, not `MissingDeterminer`:

```text
"System records the total."   ->  the guarantee clause must be of the form 'the <subject> shall <response>' but no 'shall' was found   (MissingModal)
"System shall record the total."  ->  the guarantee clause must start with the determiner 'the' but starts with 'System'   (MissingDeterminer)
```

## How errors surface in the CLI

Grammar is a **hard gate, checked first** — before any evidence capture,
snapshot, or store access — so a grammar error preempts everything else: the
statement never reaches the store, and nothing is written. In the client/daemon
split this gate runs on the **daemon** (`specd` calls `parse` at the start
of ingest; see `so_daemon/src/add.rs`), not in the `spec` process.

- On a grammar failure the daemon returns gRPC **`INVALID_ARGUMENT`** carrying
  the message `syntax error in statement: <message>`, where `<message>` is the
  exact `ParseError` `Display` text from the table above.
- The `spec` CLI surfaces that status on **stderr**, wrapped in its own framing.
  For `parse("   ")` the actual output is:

  ```text
  error: daemon returned an error: status: InvalidArgument, message: "syntax error in statement: statement is empty", details: [], metadata: MetadataMap { headers: {} }
  ```

  The `ParseError` text is still embedded verbatim in `message`; only the
  surrounding gRPC status envelope is new. Don't match the exact byte string —
  key off the embedded message, or better, off the exit code.
- The process exits with **code 2** (bad input). The same exit code covers an
  evidence/locator syntax error; a grammar error just happens first.

Because parsing is a hard gate, fixing the reported `ParseError` is a prerequisite
for the statement being ingested at all.

## See also

- [forms.md](./forms.md) — the three accepted forms these errors guard.
- [lexical.md](./lexical.md) — trimming, the trailing period, word boundaries,
  casing, and `then`: the lexical rules whose violation produces these errors.
