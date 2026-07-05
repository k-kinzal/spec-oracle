# Formal grammar & parsing algorithm

> Part of the [grammar reference](./README.md).

This is the rigorous companion to the prose in [forms.md](./forms.md) (the three
EARS forms) and [lexical.md](./lexical.md) (tokenization rules). It gives a formal
EBNF grammar, the authoritative disambiguation rules that EBNF cannot express, and
a step-by-step account of the parser as implemented in `so_lang/src/grammar.rs`. For the
failure cases the algorithm can emit, see [errors.md](./errors.md).

The parser is a **total recognizer**: `parse(input: &str) -> Result<Contract,
ParseError>` maps every input to exactly one of — one unambiguous [`Contract`](./projection.md)
or one precise [`ParseError`](./errors.md). There is no ambiguity, no confidence
score, and no probabilistic parse.

## 1. EBNF grammar

The grammar below captures the recognizer's *structure*. It is an **aid**: pure
EBNF cannot express the whitespace-vs-alphanumeric boundary asymmetry, the
"first comma" / "first `shall`" longest-match choices, or the case-insensitive
terminal matching. Those are pinned down in [§2](#2-terminals--case-insensitivity)
and [§3](#3-authoritative-disambiguation-rules), which **govern** wherever the EBNF
is loose.

Notation: `=` defines, `,` concatenation, `|` alternation, `{ }` zero-or-more,
`[ ]` optional, `" "` terminal, `? … ?` a prose-defined token, `(* … *)` comment.

```ebnf
(* ── Top level ─────────────────────────────────────────────────────── *)
statement        = body , [ "." ] ;                (* at most ONE trailing period *)
body             = { condition-clause } , guarantee-clause ;

(* ── Condition clauses  →  the assumption ──────────────────────────── *)
condition-clause = keyword , WS , condition-text , "," , [ WS , "then" ] ;
condition-text   = ? one or more characters, none of which is "," ? ;

(* ── Guarantee clause ──────────────────────────────────────────────── *)
guarantee-clause = "the" , WS , subject , WS , "shall" , WS , response ;
subject          = ? text between the determiner and the first whole-word "shall" ? ;
response         = ? text after the first whole-word "shall" ? ;

(* ── Terminals ─────────────────────────────────────────────────────── *)
keyword          = "While" | "When" | "If" | "Where" ;   (* ASCII case-insensitive *)
WS               = ? one or more Unicode whitespace characters ? ;
```

Mapping to the three [accepted forms](./forms.md):

| Form | `body` shape |
| --- | --- |
| **Ubiquitous** | `guarantee-clause` (zero condition clauses → assumption `⊤`) |
| **Conditional** | one `condition-clause` then `guarantee-clause` |
| **Complex** | two or more `condition-clause` then `guarantee-clause` |

Whitespace shown as `WS` is a *boundary*, not significant content: the parser
trims at every clause edge, so subject, response, and condition text never carry
leading or trailing whitespace. The optional `"then"` is stripped after a
condition clause's comma; in practice it is only written before the guarantee
clause (EARS `If …, then …`), but the parser will discard one wherever it may
legally appear (see [§3](#3-authoritative-disambiguation-rules)).

## 2. Terminals & case-insensitivity

There are exactly four condition keywords plus three fixed lexemes. All are ASCII
and all are matched **ASCII-case-insensitively**.

| Terminal | Value(s) | Notes |
| --- | --- | --- |
| `keyword` | `While`, `When`, `If`, `Where` | Surface casing from the input is **preserved** in the parsed [`Condition.keyword`](./projection.md); only matching is case-insensitive (so `when` and `WHEN` both match, and the exact bytes are kept). |
| determiner | `the` | Opens every guarantee clause. |
| modal | `shall` | The single pivot of the guarantee clause. |
| `then` | `then` | Optional filler after a condition comma; discarded, never stored. |

Non-terminal captures (`subject`, `response`, `condition-text`) are **opaque free
text** taken verbatim, including non-ASCII — e.g. `café`, `crêpes`. Nothing inside
them is decomposed at ingest (subject resolution and a predicate language for the
response are deliberately deferred; see [projection.md](./projection.md)).

## 3. Authoritative disambiguation rules

Where the EBNF is ambiguous, these rules — as implemented — decide the parse.

**a. Greedy, left-to-right condition consumption.** `body` is scanned from the
left; as long as the remaining text begins with a `keyword` at a whitespace
boundary, another `condition-clause` is consumed. The loop halts at the first
token that is not a keyword. The guarantee clause opens with `the`, which is not a
keyword, so consumption naturally stops there.

**b. Each condition clause ends at the FIRST comma.** `condition-text` runs from
just after the keyword to the *first* comma in the remaining text. A condition
phrase therefore **cannot contain a comma** — the first comma always terminates it.
(A comma placed inside intended condition text splits it early and usually
surfaces as [`MissingDeterminer`](./errors.md).)

**c. The subject ends at the FIRST whole-word `shall`.** Within a guarantee
clause, the subject is the text between the determiner and the *first* whole-word
occurrence of `shall`; everything after that `shall` is the response.

**d. Boundary asymmetry — two different notions of "word".** This asymmetry is
real and load-bearing:

| Token(s) | Boundary function | Requirement |
| --- | --- | --- |
| `keyword`, `the`, `then` | `starts_with_word` | case-insensitive prefix **immediately followed by a whitespace character** |
| `shall` | `find_word` | case-insensitive match whose neighbors on **both** sides are non-alphanumeric (or a string edge) |

Consequences (full walkthroughs in [lexical.md](./lexical.md)):

- `Whenever …` is **not** the keyword `When` — the next character is `e`, not whitespace.
- `If,` is **not** the keyword `If` — the next character is `,`, not whitespace; a keyword must be followed by a space.
- `marshalling` does **not** contain the modal — the inner `shall` is preceded by `r` (alphanumeric). See the accepted example `The marshalling yard shall be clear.`
- `shall,` or `(shall)` **would** match the modal — the neighbors are non-alphanumeric.

## 4. The parse algorithm

The steps below mirror `so_lang/src/grammar.rs` in order. Any step may short-circuit with
a [`ParseError`](./errors.md); the first defect encountered wins.

### 4.1 Top level — `parse`

1. **Trim.** `trimmed = input.trim()`. If empty → `Empty`.
2. **Strip one trailing period.** `body = trimmed.strip_suffix('.').unwrap_or(trimmed).trim()`.
   At most **one** trailing `.` is removed, then the result is trimmed again. If
   now empty → `Empty`. (So `"."` → `Empty`. Internal periods and any *second*
   trailing period are **not** stripped — they stay in the clause text; e.g.
   `The pump shall stop..` yields response `stop.`.)
3. **Consume condition clauses (greedy loop).** With `rest = body`, while `rest`
   begins with a `keyword` at a whitespace boundary (`leading_condition_keyword`):
   1. Find the first comma in `rest`. If none → `MissingComma { keyword }` (surface casing).
   2. `text = rest[keyword.len()..comma].trim()`. If empty → `EmptyCondition { keyword }`.
   3. Push `Condition { keyword: <surface casing>, text }`.
   4. Advance past the comma, `trim_start`, then discard one leading `then`
      (`strip_leading_then`, whitespace-bounded). Assign the result back to `rest`.
4. **Parse the guarantee.** `guarantee = parse_guarantee(rest.trim())` (see [§4.2](#42-guarantee-clause--parse_guarantee)).
5. **Select the assumption.** `Top` if no condition clauses were consumed, else
   `Conditions { clauses }`. Return `Contract { assumption, guarantee }`.

### 4.2 Guarantee clause — `parse_guarantee`

Input is the text remaining after the condition loop, trimmed.

1. Compute `has_modal = find_word(clause, "shall").is_some()`.
2. Check `opens_with_determiner = starts_with_word(clause, "the")`.
3. If it does **not** open with the determiner:
   - if `!has_modal` → `MissingModal` — a missing modal is treated as the **more
     fundamental** defect and reported first;
   - else → `MissingDeterminer { found }`, where `found` is the first
     whitespace-delimited token of the clause.
4. `after_determiner = clause[3..].trim_start()` (past `the`).
5. `modal_at = find_word(after_determiner, "shall")`. If none → `MissingModal`.
6. `subject = after_determiner[..modal_at].trim()`. If empty → `EmptySubject`.
7. `response = after_determiner[modal_at + 5..].trim()`. If empty → `EmptyResponse`.
8. Return `Guarantee { subject, response }`.

### Worked traces

Two end-to-end walkthroughs; the [cookbook](./cookbook.md) has the full gallery.

`When the order ships, the system shall notify the customer` (no period):

| Step | State |
| --- | --- |
| trim, strip period | `body = "When the order ships, the system shall notify the customer"` |
| loop: `When ` is a keyword | first comma at `ships,`; `text = "the order ships"` → push `Condition { "When", "the order ships" }` |
| after comma, no `then` | `rest = "the system shall notify the customer"` |
| loop halts | `the` is not a keyword |
| guarantee | opens with `the`; first whole-word `shall` splits `subject = "system"`, `response = "notify the customer"` |
| assumption | one clause → `Conditions[("When","the order ships")]` |

`If the balance is negative, then the account shall be frozen.`:

| Step | State |
| --- | --- |
| trim, strip period | `body = "If the balance is negative, then the account shall be frozen"` |
| loop: `If ` is a keyword | first comma; `text = "the balance is negative"` → push `Condition { "If", "the balance is negative" }` |
| after comma, strip `then` | `rest = "the account shall be frozen"` |
| guarantee | `subject = "account"`, `response = "be frozen"` |
| assumption | `Conditions[("If","the balance is negative")]` (the `then` is dropped, not stored) |

## 5. Total recognizer & multibyte safety

The recognizer is **total** and **never panics** on any `&str`, including
arbitrary multibyte / UTF-8 input. Two facts guarantee this:

- `starts_with_word` slices with `s.get(..len)`, which returns `None` (rather than
  panicking) when `len` would fall inside a codepoint — exactly the "not this
  keyword/determiner" outcome.
- `find_word` scans **bytes** with ASCII-only boundary checks, so it never slices
  inside a codepoint and treats any multibyte byte as a non-alphanumeric neighbor,
  which satisfies the whole-word boundary condition just like a space or
  punctuation (it counts as a boundary, matching §3d).

The four keywords, `the`, `shall`, and `then` are all ASCII and matched
ASCII-case-insensitively; every other span (subject, response, condition text) is
captured verbatim. Consequently inputs such as `€`, `中文`, `🔥 shall stop`, or
`The café shall serve crêpes.` all yield a well-defined `Ok` or `Err` — never a
panic. This is a language requirement, verified by the recognizer's test suite.
