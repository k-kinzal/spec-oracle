# The specification description language

> This is the index of the grammar reference.

`spec add` accepts a **specification**: one or more sentences written in an
EARS-derived constrained natural language. Each sentence performs one
**speech-act core** — defining a term, describing the system, or obliging,
forbidding, recommending, or permitting behavior — under zero or more
**circumstance frames** (`Where` / `While` / `When` / `If`), with an optional
**exception** (`unless`) and an optional **purpose** (`so that` /
`in order to`). The daemon creates **one node per sentence**.

The language constrains **ambiguity, not expressiveness**. The closed-class
skeleton — frame keywords, modals, copulas, determiners and quantifiers,
coordination, thematic-role prepositions, comparison operators — is owned by
the grammar; the open-class vocabulary — nouns, verbs, adjectives, URLs,
identifiers — is free and passes through as opaque words. Every accepted
sentence has exactly one reading, and every meaning-bearing word lands in the
parse tree; the raw sentence text remains the source of truth.

The single source of truth is the code:
[`so_lang/src/ast.rs`](../../so_lang/src/ast.rs),
[`so_lang/src/parse.rs`](../../so_lang/src/parse.rs), and
[`so_lang/src/semantics.rs`](../../so_lang/src/semantics.rs). These docs
describe only what that code does.

## Philosophy: a total recognizer

The parser — `so_lang::parse::parse(input: &str) -> Result<Specification,
ParseError>` — is a **total recognizer**. Every input is *either*:

- **accepted**, yielding exactly one `Specification` (one unambiguous parse
  tree per sentence), *or*
- **rejected**, with one precise [`ParseError`](./errors.md).

There is nothing in between. Concretely:

- **No confidence score, no probabilistic parse, no inference.** A sentence is
  not *scored* for how spec-like it is; it either conforms to the grammar or
  it does not, and no dictionary or model guesses at the author's intent.
- **No panic, on any input.** Empty strings, lone punctuation, emoji, and
  multibyte text all yield a parse or an error — never a crash.
- **Precise rejection is a feature.** Constructions with more than one natural
  reading — `may not`, `can`, mixed `and`/`or` in one coordination, a
  condition trailing the sentence — are rejected with an error that names the
  canonical rewrite. See [errors.md](./errors.md).

## Quick reference: the six speech-act cores

The pivot word decides the core; the subject is everything before it.

| Speech act | Pivot | Example |
| --- | --- | --- |
| **Definition** | `means` | `A session means a sequence of requests.` |
| **Description** | `is` / `are` | `The retry count is at most 3.` |
| **Obligation** | `shall` / `must` | `The pump shall stop.` |
| **Prohibition** | `shall not` / `must not` | `The daemon shall not store derived views.` |
| **Recommendation** | `should` | `The library should install propagators.` |
| **Permission** | `may` | `The client may retry.` |

**Frames**, in canonical order before the core: any number of `Where <clause>,`
(configuration scopes), then any number of `While <clause>,` (state scopes),
then at most one trigger — `When <clause>,` (event) or `If <clause>, [then]`
(contingency; `then` is optional on input, always emitted on render). After
the core: `, unless <clause>` (exception), then `, so that <clause>` or
`, in order to <verb phrase>` (purpose).

Each constraining sentence taken alone also projects to an assume-guarantee
contract — a guarantee under the trivial assumption `⊤`. Definitions
(vocabulary) and permissions (admissibility: they admit behavior rather than
constrain it) carry no lone-sentence contract; that reading lives entirely in
[semantics.md](./semantics.md).

## Doc map

| File | Topic |
| --- | --- |
| [sentences.md](./sentences.md) | The sentence layer: specifications, the six cores, circumstance frames and their canonical order, exceptions, purposes. |
| [phrases.md](./phrases.md) | The phrase grammar: noun phrases, determiners and quantifiers, relative clauses, coordination, verb phrases, thematic roles, predicates, measures. |
| [lexical.md](./lexical.md) | Tokenization: whitespace, the sentence terminator, commas, decimals and URLs, casing, number words, multibyte safety. |
| [semantics.md](./semantics.md) | Derived interpretations: speech acts, force, polarity, denotations, the ingest projection, definite references. |
| [errors.md](./errors.md) | The `ParseError` taxonomy: every variant, what triggers it, and the canonical rewrite. |
| [reference.md](./reference.md) | The formal grammar and the recognizer's algorithmic commitments. |
| [cookbook.md](./cookbook.md) | A gallery of accepted and rejected specifications, each traced to its structure or error. |

## Scope

This directory covers **only** the specification language. The evidence and
locator syntax — the separate input language for the evidence a node is
grounded in — is documented in the top-level [`README.md`](../../README.md),
not here.
