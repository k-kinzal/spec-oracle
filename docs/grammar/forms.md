# The three EARS forms

> Part of the [grammar reference](./README.md).

Every accepted statement matches one of three EARS-derived surface forms:
**Ubiquitous**, **Conditional**, and **Complex**. They are not three separate
parser branches — they are one algorithm seen at three sizes. The parser
consumes **zero or more** leading condition clauses (greedily), then exactly one
guarantee clause:

| Form | Leading condition clauses | Assumption |
| --- | --- | --- |
| Ubiquitous | 0 | `Top` (`⊤`) |
| Conditional | 1 | `Conditions` with one clause |
| Complex | 2 or more | `Conditions` with the clauses conjoined in order |

Two building blocks appear in every form:

- **Condition clause** — `<keyword> <condition>`, opened by one of the four
  keywords `While`, `When`, `If`, `Where` and closed by a comma. Contributes to
  the **assumption**.
- **Guarantee clause** — `the <subject> shall <response>`, opened by the
  determiner `the` and pivoting on the modal `shall`. Becomes the **guarantee**.

The trailing period shown below is optional; casing and whitespace handling for
keywords, the determiner, and the modal are governed by the tokenizer — see
[lexical.md](./lexical.md). For what happens when a form is malformed, see
[errors.md](./errors.md). For how the parsed parts become a `Contract`, see
[projection.md](./projection.md).

---

## Ubiquitous

An unconditional guarantee: the response always holds.

```text
The <subject> shall <response>.
```

| Slot | Meaning |
| --- | --- |
| `The` | the subject determiner that opens the guarantee clause |
| `<subject>` | the noun phrase between the determiner and the modal |
| `shall` | the guarantee modal (the pivot) |
| `<response>` | everything after the modal |

Because no condition keyword leads the body, the condition loop consumes
nothing and the assumption is `Top` (`⊤`).

**Accepted example**

```text
The sales amount shall be greater than zero.
```

| Projection | Value |
| --- | --- |
| assumption | `Top` (`⊤`) |
| subject | `sales amount` |
| response | `be greater than zero` |

More accepted Ubiquitous statements (each projects to `Top`):

| Input | subject | response | Note |
| --- | --- | --- | --- |
| `The pump shall stop` | `pump` | `stop` | trailing period optional |
| `The marshalling yard shall be clear.` | `marshalling yard` | `be clear` | the inner `shall` of `marshalling` is not the modal |
| `The café shall serve crêpes.` | `café` | `serve crêpes` | subject and response captured verbatim, multibyte-safe |

**Rules specific to this form**

- The clause must open with the determiner `the` at a word boundary; otherwise
  it is not a guarantee clause.
- The first whole-word `shall` is the pivot. A `shall` embedded inside a larger
  word (as in `marshalling`) is not a boundary, so the real modal wins.

---

## Conditional

A single guard on the guarantee.

```text
<While|When|If|Where> <condition>, [then] the <subject> shall <response>.
```

| Slot | Meaning |
| --- | --- |
| `<While\|When\|If\|Where>` | the condition keyword (exactly one of these four) |
| `<condition>` | the condition phrase, from the keyword to the comma |
| `,` | mandatory separator closing the condition clause |
| `[then]` | optional and discarded (EARS' `If ..., then ...`) |
| `the <subject> shall <response>` | the guarantee clause |

**Accepted example**

```text
When the order is submitted, the system shall record the total.
```

| Projection | Value |
| --- | --- |
| assumption | `Conditions` → `[("When", "the order is submitted")]` |
| subject | `system` |
| response | `record the total` |

**Rules specific to this form**

- **The comma is mandatory.** It closes the condition clause; without it the
  keyword's clause is never terminated and parsing fails with `MissingComma`
  (see [errors.md](./errors.md)).
- **`then` is optional and discarded.** It is stripped exactly once, only
  immediately after the comma, and only when whitespace-bounded. The
  guarantee's meaning is unchanged whether or not it is present:

  ```text
  If the balance is negative, then the account shall be frozen.
  ```

  | Projection | Value |
  | --- | --- |
  | assumption | `Conditions` → `[("If", "the balance is negative")]` |
  | subject | `account` |
  | response | `be frozen` (`then` dropped) |

- **Keyword casing is preserved.** Keywords are recognized
  case-insensitively, but the surface casing from the input is kept in the
  parsed clause:

  ```text
  when the order ships, the system shall notify the customer
  ```

  projects the assumption `Conditions` → `[("when", "the order ships")]` (lower-case
  `when` retained), subject `system`, response `notify the customer`.

- The condition phrase is captured verbatim, including non-ASCII text — e.g.
  `When the café is open, the barista shall greet the guest.` yields the clause
  `("When", "the café is open")`, subject `barista`, response `greet the guest`.

---

## Complex

Two or more condition clauses guarding one guarantee. Each is `<keyword>
<condition>,` and the guarantee is whatever remains after the greedy condition
loop — i.e. it follows the comma of the *last leading condition clause*, not the
last comma in the string (a response may itself contain commas).

```text
<kw> <c1>, <kw> <c2>, ... the <subject> shall <response>.
```

The keywords may differ between clauses, and each keeps its own surface casing.
The clauses are conjoined **in order** into the assumption.

**Accepted example**

```text
While the engine is running, when the temperature exceeds the limit, the controller shall open the valve.
```

| Projection | Value |
| --- | --- |
| assumption | `Conditions` → `[("While", "the engine is running"), ("when", "the temperature exceeds the limit")]` |
| subject | `controller` |
| response | `open the valve` |

**Rules specific to this form**

- **Clauses are conjoined in order.** The assumption preserves the sequence in
  which the clauses appear.
- **Consumption is greedy and stops at the guarantee.** The loop keeps taking
  clauses as long as the remaining text starts with a condition keyword. The
  guarantee clause opens with `the`, which is not a keyword, so the loop halts
  there naturally.
- **A condition phrase cannot contain a comma.** Each clause ends at the
  *first* comma after its keyword. A comma placed inside intended condition text
  will split it early, so the following segment (unless it starts with a keyword)
  is treated as the guarantee — typically producing `MissingDeterminer` (see
  [errors.md](./errors.md)).
- Every keyword must still be followed by a comma; a later clause missing its
  comma fails with `MissingComma`.

---

## See also

- [lexical.md](./lexical.md) — precise word-boundary, casing, trailing-period,
  and multibyte rules referenced above.
- [errors.md](./errors.md) — the exact `ParseError` produced when a form is
  malformed.
- [reference.md](./reference.md) — the formal EBNF and the greedy parsing
  algorithm behind all three forms.
- [projection.md](./projection.md) — how these surface parts become an
  assume-guarantee `Contract`.
