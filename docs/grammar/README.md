# The specification description language

> This is the index of the grammar reference.

`spec add` accepts specification statements written in an **EARS-derived
constrained natural language**, and projects each one into an **assume-guarantee
contract**: leading condition clauses become the **assumption**, and the
`the <subject> shall <response>` clause becomes the **guarantee**. This directory
documents that language: its forms, its lexical rules, the projection, the error
taxonomy, and a formal grammar.

The single source of truth is [`so_lang/src/grammar.rs`](../../so_lang/src/grammar.rs). These
docs describe only what that code does.

## Philosophy: a total recognizer

The parser — `so_lang::grammar::parse(input: &str) -> Result<Contract, ParseError>`
— is a **total recognizer**. Every input is *either*:

- **accepted**, yielding exactly one `Contract` (one unambiguous parse), *or*
- **rejected**, with a precise [`ParseError`](./errors.md).

There is nothing in between. Concretely, this means:

- **No confidence score, no probabilistic parse, no inference.** A statement is
  not *scored* for how spec-like it is; it either conforms to the grammar or it
  does not.
- **No human-in-the-loop review.** Parseability is a *language requirement*, not
  a judgement call. If the statement parses, its A/G projection is mechanical and
  fixed; if it does not, you get a specific error explaining what to fix.
- **Grammar is checked first.** `spec add` calls `parse` *before* any
  evidence, snapshot, or store work, so a grammar error preempts everything else.
  A rejected statement exits with **code 2** (bad input) and writes nothing.

## Quick reference

Three accepted forms. The determiner `the`, the modal `shall`, and the four
condition keywords `While` / `When` / `If` / `Where` are the fixed vocabulary;
everything else (subject, response, condition text) is opaque free text.

| Form | Shape | Example | Assumption |
| --- | --- | --- | --- |
| **Ubiquitous** | `The <subject> shall <response>.` | `The sales amount shall be greater than zero.` | `⊤` (Top) |
| **Conditional** | `<While\|When\|If\|Where> <condition>, [then] the <subject> shall <response>.` | `When the order is submitted, the system shall record the total.` | one condition clause |
| **Complex** | `<kw> <c1>, <kw> <c2>, ... the <subject> shall <response>.` | `While the engine is running, when the temperature exceeds the limit, the controller shall open the valve.` | conjunction of clauses |

The trailing period is optional (`The pump shall stop` parses). See
[forms.md](./forms.md) for each form in full and [cookbook.md](./cookbook.md)
for a gallery of accepted and rejected statements.

## Doc map

| File | Topic |
| --- | --- |
| [forms.md](./forms.md) | The three EARS forms — Ubiquitous, Conditional, Complex — in detail. |
| [lexical.md](./lexical.md) | Lexical & tokenization rules: trimming, the optional trailing period, the two word-boundary notions, casing, `then`, multibyte safety. |
| [projection.md](./projection.md) | The assume-guarantee projection, the data model (`Condition` / `Assumption` / `Guarantee` / `Contract`), JSON shapes, and `render()`. |
| [errors.md](./errors.md) | The `ParseError` taxonomy: exact messages, what triggers each, how to fix, and the exit code. |
| [reference.md](./reference.md) | The formal EBNF grammar and the parsing algorithm (greedy clause consumption, word-boundary asymmetry). |
| [cookbook.md](./cookbook.md) | A gallery of accepted and rejected examples, each traced to its projection or error. |

## Scope

This directory covers **only** the statement grammar. The evidence/locator
syntax — the separate input language for the evidence a node is grounded in — is
documented in the top-level [`README.md`](../../README.md), not here.

Deliberately deferred and **not** part of this language today: subject
resolution, a formal predicate language for the response, contract strength,
edges (refinement / composition / conjunction / quotient), and
classification/review. At ingest, the subject and response are opaque free text.
