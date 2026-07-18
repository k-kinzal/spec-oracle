# Formal grammar & parsing algorithm

> Part of the [grammar reference](./README.md).

This is the rigorous companion to the prose in [sentences.md](./sentences.md)
(the sentence layer) and [phrases.md](./phrases.md) (the phrase grammar). It
gives the full EBNF of the language as implemented, the closed-class vocabulary
and stop sets the EBNF leans on, and the deterministic-reading rules that EBNF
cannot express — the choices the recognizer makes so that every accepted
sentence has exactly one tree. Everything here is derived from
[`so_lang/src/parse.rs`](../../so_lang/src/parse.rs) over the AST of
[`so_lang/src/ast.rs`](../../so_lang/src/ast.rs); the lexical layer is in
[lexical.md](./lexical.md) and the rejection taxonomy in
[errors.md](./errors.md).

The parser is a **total recognizer**: `so_lang::parse::parse(input: &str) ->
Result<Specification, ParseError>` maps every input to exactly one
specification or exactly one precise error — never a panic, never a partial
tree, never a guess. There is no ambiguity, no confidence score, and no
probabilistic parse.

## 1. EBNF grammar

The grammar below captures the recognizer's *structure*. It is an **aid**:
pure EBNF cannot express the positional stop sets, the "parse the whole
delimited slice" discipline, the subject/copula split search, or the
definiens priority. Those are pinned down in [§2](#2-closed-classes-and-stop-sets)
and [§3](#3-the-deterministic-reading), which **govern** wherever the EBNF is
loose.

Notation: `=` defines, `,` concatenation, `|` alternation, `{ }` zero-or-more,
`[ ]` optional, `" "` terminal, `? … ?` a prose-defined token, `(* … *)`
comment. Every quoted terminal is matched **ASCII-case-insensitively** over
one token; surface casing is preserved in the tree where the AST keeps the
word. `","` and `"."` are the comma and terminator tokens of
[lexical.md](./lexical.md).

```ebnf
(* ── Sentence layer ─────────────────────────────────────────────────── *)
specification  = sentence , { sentence } ;
sentence       = frames , core , [ exception ] , [ purpose ] , [ "." ] ;

frames         = { "where" , clause-group , "," } ,
                 { "while" , clause-group , "," } ,
                 [ trigger ] ;                        (* canonical order *)
trigger        = "when" , clause-group , ","
               | "if" , clause-group , "," , [ "then" ] ;
clause-group   = clause , { conj , clause } ;         (* one conj throughout;
                                                         NP-vs-clause: §3.3 *)

exception      = "," , "unless" , clause ;
purpose        = "," , ( "so" , "that" , clause
                       | "in" , "order" , "to" , vp ) ;

(* ── The speech-act core ────────────────────────────────────────────── *)
core           = definition | description | deontic ;
definition     = np , "means" , definiens ;           (* term: one np, §3.7 *)
definiens      = "that" , clause                      (* forces the clause *)
               | clause                               (* priority: §3.4 *)
               | np-group , { role-pp } ;
description    = np-group , ( "is" | "are" ) ,
                 [ "always" | "never" ] , "able" , "to" , vp
                                                      (* capability; the
                                                         adverb composes
                                                         into polarity
                                                         (round 5) *)
               | np-group , ( "is" | "are" ) ,
                 [ "always" | "never" ] , predicate ,
                 [ "by" , np-group ,
                   { role-pp } ] ;                    (* passive agent:
                                                         round 5; role tail
                                                         after the agent:
                                                         round 8 follow-up —
                                                         agentless
                                                         descriptions keep
                                                         the plain predicate
                                                         reading *)
deontic        = np-group , ( "shall" | "must" | "should" ) , [ "not" ] , vp-group
               | np-group , "may" , vp-group ;        (* never "may not";
                                                        a `no` subject under
                                                        "may" is rejected *)

(* ── Clause layer (frames, unless, so that, before/after, definiens) ── *)
clause         = np-group , clause-body ;
clause-body    = clause-copula ,
                 ( "able" , "to" , vp                 (* capability: round 8,
                                                         bare form only —
                                                         clauses have no
                                                         adverb slot *)
                 | predicate , [ "by" , np-group ] ,
                   { role-pp }                        (* copular: §3.2;
                                                         passive agent:
                                                         round 5; role tail:
                                                         round 8 — a later
                                                         "by" is the Agent
                                                         role (passive site) *)
                 )
               | verb , [ particle ] , { manner } ,
                 [ np-group ] , { role-pp } ,
                 [ "that" , clause ] ;                (* verbal: §3.3.
                                                         Round 9: the final
                                                         "that" clause is the
                                                         CONTENT complement —
                                                         same shape as in a
                                                         vp; after a noun the
                                                         "that" is a relative
                                                         instead *)
clause-copula  = "is" | "are" | "remains" ;
verb           = open-word ;                          (* not a determiner:
                                                         DeterminerAsVerb,
                                                         round 6 follow-up *)
particle       = "out" | "down" | "up" | "off" ;      (* closed list; never
                                                         after "be". Surface
                                                         "verb np particle"
                                                         and "verb manner
                                                         particle" normalize
                                                         into the particle
                                                         slot: §3.4 *)

(* ── Phrase layer: verb phrases and thematic roles ──────────────────── *)
vp-group       = vp                                   (* round 6: VP
                                                         alternatives —
                                                         deontic cores only.
                                                         "not" never combines
                                                         with alternatives
                                                         (NegatedAlternatives) *)
               | "either" , vp , "or" , vp , { "or" , vp } ;
vp             = ( "be" , [ predicate ] , { role-pp }
               | verb , [ particle ] , { manner } ,
                 [ np-group ] , { role-pp } ) ,
                 [ "that" , clause ] ;                (* round 7: content
                                                         complement — final,
                                                         consumes the rest of
                                                         the phrase; after a
                                                         NOUN the "that" is
                                                         that noun's relative
                                                         instead (§3.6) *)
manner         = ly-word ;                            (* a bare open-class
                                                         word ending in "ly"
                                                         (ASCII, length > 2),
                                                         positional: only in
                                                         post-verbal position,
                                                         never determiner-led,
                                                         never inside an np;
                                                         a conj ends the run *)
role-pp        = "to" , np-group                      (* Recipient *)
               | ( "via" | "using" ) , np-group       (* Means *)
               | "about" , np-group                   (* Topic *)
               | "from" , np-group                    (* Source *)
               | "into" , np-group                    (* Goal *)
               | "within" , measure                   (* Deadline — a bound
                                                         opener after
                                                         "within" is
                                                         WithinTakesPlain-
                                                         Measure (round 6
                                                         follow-up) *)
               | "for" , duration-measure             (* Duration — a
                                                         QUANTITY, plain or
                                                         bounded (rounds 5–6):
                                                         a non-quantity `for`
                                                         is
                                                         ForRequiresMeasure *)
               | "per" , open-word                    (* Rate *)
               | loc-prep , np-group                  (* Location *)
               | "by" , np-group                      (* Agent — only in a
                                                         complemented "be"
                                                         vp (round 5);
                                                         elsewhere
                                                         ByOutsidePassive.
                                                         "with" is reserved
                                                         here only to reject:
                                                         WithIsAmbiguous *)
               | ( "before" | "after" | "until" ) , clause ;
                                                      (* final: §3.5 *)
loc-prep       = "in" | "on" | "at" | "under" | "over" | "above" | "below" ;
                             (* "at" only when not followed by least/most *)

(* ── Phrase layer: noun phrases ─────────────────────────────────────── *)
np-group       = [ "both" | "either" ] , np , { conj , np } ;   (* §3.7 *)
conj           = "and" | "or" ;                       (* one throughout *)
np             = [ det ] , { open-word } , open-word ,
                 [ "of" , np ] , [ relative ] ;       (* depth: §3.8.
                                                         Round 6: bare "with"
                                                         inside ANY np —
                                                         plain positions
                                                         included — is
                                                         WithIsAmbiguous *)
det            = "the" | "a" | "an" | "each" | "every" | "all" | "any" | "no"
               | "at" , "least" , count
               | "at" , "most" , count
               | "exactly" , count ;
relative       = ( "that" | "who" ) , relative-body ; (* attachment: §3.6 *)
relative-body  = clause-copula ,
                 ( "able" , "to" , vp                 (* capability: round 8,
                                                         bare form only *)
                 | predicate , [ "by" , np-group ] ,
                   { role-pp }                        (* round 8: agent + role
                                                         tail mirror the
                                                         copular clause body *)
                 )
               | verb , [ particle ] , { manner } ,
                 [ np-group ] , { role-pp }           (* round 7: the verbal
                                                         body is the FULL
                                                         verbal tail; roles
                                                         attach to the
                                                         relative's verb —
                                                         innermost attachment,
                                                         legislated. NO
                                                         content clause in a
                                                         relative (v0.2) *)
               | np-group , verb , [ particle ] ,
                 { manner } , { role-pp } ;           (* round 9: OBJECT-GAP —
                                                         the restricted head
                                                         is the missing
                                                         object. Opens only
                                                         when a DETERMINER/
                                                         quantifier leads the
                                                         gap's subject; the
                                                         subject split is the
                                                         shortest np-group
                                                         followed by a verb-
                                                         position word. A
                                                         det-led object after
                                                         the gap's verb → not
                                                         a gap
                                                         (DeterminerAsVerb) *)

(* ── Predicates, comparisons, measures ──────────────────────────────── *)
predicate      = comparison                           (* tried first *)
               | pred-prep , np-group
               | open-word , { open-word } ;
comparison     = ( "greater" | "less" ) , "than" , measure
               | "at" , ( "least" | "most" ) , measure
               | "equal" , "to" , measure
               | "between" , measure-single , "and" , measure ;
                                                      (* round 9: two NUMERIC
                                                         bounds must not
                                                         descend — "between 6
                                                         and 4" is
                                                         DescendingBetween;
                                                         equal bounds (a
                                                         point) and np bounds
                                                         are fine. Same rule
                                                         for the bounded
                                                         "for" measure below *)
pred-prep      = "in" | "on" | "at" | "below" | "above" | "under" | "over" ;
measure        = quantity | np-group ;
measure-single = quantity | np ;                      (* never coordinated *)
duration-measure = quantity                           (* round 6: bounded
                                                         quantities under
                                                         "for" only; one unit,
                                                         written after either
                                                         "between" bound *)
               | ( "at" , ( "least" | "most" )
                 | ( "greater" | "less" ) , "than" ) , quantity
               | "between" , quantity , "and" , quantity ;
quantity       = number , [ unit ] ;
unit           = open-word ;                          (* and not a number *)
number         = numeral | number-word ;
numeral        = ? digits , [ "." , digits ] — one whole token ? ;
number-word    = "zero" | "one" | "two" | "three" | "four" | "five"
               | "six" | "seven" | "eight" | "nine" | "ten"
               | "eleven" | "twelve" | "thirteen" | "fourteen" | "fifteen"
               | "sixteen" | "seventeen" | "eighteen" | "nineteen"
               | "twenty" | "thirty" | "forty" | "fifty" | "sixty"
               | "seventy" | "eighty" | "ninety" | "hundred" ;
                                (* single words only — no compounds;
                                   round 12 *)
count          = ? a number whose value is whole and fits 64 bits ? ;
open-word      = ? any word token that is not a stop word
                   in its position — see §2 ? ;
```

Reading the EBNF against the AST: `specification` is `Specification`,
`sentence` is `Sentence`, `core`'s three arms are `Core::Definition`,
`Core::Description`, and `Core::Deontic`, `clause` is `Clause`, `np-group`
is `NpGroup`, `role-pp` is `RolePp`, and `predicate`'s three arms are
`Predicate::Comparison`, `Predicate::Pp`, and `Predicate::Words`.

Two structural facts the EBNF understates:

- **Commas are segment boundaries, not punctuation.** After the frames, the
  recognizer splits the rest of the sentence at *every* remaining comma; the
  first segment must be the whole core, and each later segment must be a
  complete `unless` / `so that` / `in order to` adjunct ([§4](#4-the-recognizer-step-by-step)).
  A comma can therefore never appear inside a core, a clause, or an adjunct.
- **Delimited slices must be consumed exactly.** A frame clause owns the
  tokens up to its comma, a core owns its segment, a definiens owns
  everything after `means`. Leftover tokens in any of these are
  `UnexpectedTokens`, not silently dropped.

## 2. Closed classes and stop sets

The closed-class vocabulary is owned by the grammar and matched
case-insensitively; everything else is open-class and passes through as
opaque words. These lists are the constants at the top of `parse.rs`:

| Class | Words | Closed where |
| --- | --- | --- |
| Pivots | `shall` `must` `should` `may` `is` `are` `means` | everywhere (reserved) |
| Excluded modals | `can` `will` `would` `could` `might` `ought` | everywhere (reserved), so they are diagnosable at pivot position |
| Frame keywords | `where` `while` `when` `if` `unless` | everywhere (reserved) |
| Structural words | `of` `that` `who` `and` `or` `both` `either` `remains` `then` `not` | everywhere (reserved) |
| Role prepositions | `to` `via` `using` `about` `within` `for` `per` `before` `after` `until` `from` `into` `with` `by` | **only after a verb** — inside a verb phrase, a verbal clause body, or a definiens. Round 5: `with` is closed here only to be rejected (`WithIsAmbiguous`); `by` opens the Agent role at a passive site (`be <predicate>`, a description's/copular clause's predicate) and is rejected elsewhere (`ByOutsidePassive`) |
| Locative prepositions | `in` `on` `at` `under` `over` `above` `below` | after a verb (Location roles, in verb phrases and verbal clause bodies alike) and at the start of a predicate (`Predicate::Pp`); `at least`/`at most` always stay the comparison path |
| Particles | `out` `down` `up` `off` | immediately after a verb other than `be` (the particle slot), reached across the verb's manner run (`shut gracefully down` = `shut down gracefully`), or trailing that verb's object (`lift the beam up` = `lift up the beam`); elsewhere ordinary words |
| Manner adverbs | any bare word ending in ASCII `ly` (length > 2) | **positional, not a word list** — only in post-verbal position, where an object or role would start: not determiner-led (`exactly 7` stays a quantifier), not a role/locative preposition, not a conjunction or boundary; inside a noun phrase `ly` words stay ordinary (`the assembly`, `the nightly build`) |
| Number words | `zero` … `twenty`, tens `thirty` … `ninety`, `hundred` (round 12; single words, no compounds) | only in quantifier and measure positions. An UNKNOWN word-shaped token where those positions require a number is `UnknownNumberWord` (fail-closed, round 12) |

The **reserved set** is the union of the first four rows. Open-class
collection — the `{ open-word }` runs in `np` and `predicate` — always stops
at a reserved word, and the recognizer carries the collection **context**
(`NpCtx` in `parse.rs`):

- **Plain** (subjects, frame/exception/purpose clause subjects, description
  predicates): the reserved set only — which is why `The sensor is at the
  door.` and `The backup is for the auditor.` parse: `at` and `for` are
  ordinary words there. (A DESCRIPTION's predicate stays Plain; since
  round 8 a copular CLAUSE or RELATIVE predicate does not — next bullet.)
- **Verb phrase** (inside a `vp`, a verbal clause body's object, a
  `be`-complement, a definiens — and, since round 8, a copular clause or
  relative body's predicate, agent phrase, and role tail): the reserved
  set plus the role prepositions
  plus the locative prepositions — which is why roles (including Location)
  are recognized in those positions and only there. Since round 3 verbal
  clause bodies share this context: their objects stop at role and locative
  prepositions, which then open the clause's own role phrases; round 8
  extends the same discipline to copular bodies, whose predicates stop
  where their agent or role tail begins.

A token wrapped in backticks matches no closed-class word in any context
(see [lexical.md](./lexical.md#backtick-tokens-the-reserved-word-escape-hatch)).
The context propagates into every nested phrase: an object's relative
clause, a measure's noun phrase, and a coordination item all inherit the
enclosing stop set. Determiner words (`the`, `a`, `each`, …) are *not*
reserved — they are recognized positionally at the start of a noun phrase
and are otherwise ordinary words.

## 3. The deterministic reading

With open-class words opaque, several surface shapes have more than one
conceivable parse. The recognizer resolves each with a fixed rule; these
rules are the authority wherever the EBNF is loose.

### 3.1 Pivot detection is structural and leftmost

The core's subject is parsed left to right as a noun-phrase group with the
sentence stop set; collection halts at the first reserved word. The word at
that halt is the **pivot**, and its identity alone selects the core:

| Word at the halt | RelationVerdict |
| --- | --- |
| `shall` / `must` / `should` / `may` | deontic core |
| `is` / `are` | description core |
| `means` | definition core |
| `can` `will` `would` `could` `might` `ought` | `UnsupportedModal` |
| a frame keyword | `MidSentenceFrame` (the condition was written trailing) |
| any other reserved word | `UnexpectedTokens` |
| end of segment | `MissingPivot` |

Three properties follow:

- **No pivot kind outranks another** — there is no precedence among the
  deontic modals, `means`, and the copulas. The *leftmost* top-level pivot
  always wins. `The mode is manual shall stop.` is a description whose
  predicate ends at `shall`, and the leftover `shall stop` is rejected as
  `UnexpectedTokens` — the `is` won by position, not by kind.
- **"Top-level" is structural, not a text scan.** A relative clause consumes
  its own copula or verb ([§3.6](#36-relative-clause-attachment)), so a pivot
  word inside the subject's relative clause never ends the subject: in
  `The account that is frozen is never active.` the first `is` belongs to
  `that is frozen` and the second is the pivot.
- **A sentence that opens on a pivot has no subject** (`EmptySubject`), and
  one that opens on `unless` is diagnosed as `LeadingException` — the
  exception trails the core, it never leads.

After the pivot, each core has one fixed shape: the deontic core takes an
optional `not` (rejected as `AmbiguousModal` after `may`) and then a verb
phrase; the description takes an optional `always`/`never`, rejects `not`
(`NegatedDescription`), and then a predicate; the definition hands the rest
of the segment to the definiens. Deontic and description cores then require
their segment to be exhausted (`expect_core_end`): a frame keyword in the
leftover is `MidSentenceFrame`, anything else `UnexpectedTokens`.

### 3.2 The clause subject/copula split

A clause (`parse_clause`) owns a delimited slice and must consume all of it.
The **copular reading is tried first**: the recognizer visits every position
holding `is`, `are`, or `remains`, left to right, and the split lands on the
first one whose left side parses *exactly* — no leftover — as a noun-phrase
group. That subject-exactness test is what keeps a copula belonging to a
relative clause inside the subject from ending the subject early:

```text
If the user who is authenticated is active, the pump shall stop.
```

At the first `is`, the left side `the user who` is not a well-formed phrase
(the relative marker has no body), so the split advances; at the second `is`,
`the user who is authenticated` parses exactly, and that split wins. The
predicate after the chosen copula must consume the rest of the slice.

One guard on the winning split: when the left side contains a bare clausal
role preposition (`before`, `after`, `until` — open-class words in plain
noun phrases), the copula may belong to a clause **nested under that
role**, so the verbal reading is preferred wherever it parses. `While the
pump runs until the tank is full,` therefore keeps the verbal reading —
subject `the pump`, verb `runs`, role `Until(the tank is full)` — instead
of swallowing `the pump runs until the tank` into one flat subject noun
phrase; a copular subject that merely contains such a word with no verbal
reading (`While the after image is ready,`) stays copular.

If copula positions exist but no split yields a well-formed subject, the
copula may sit inside a copular relative of a *verbal* clause's subject —
`the user who is authenticated logs out` — so the noun-phrase-first verbal
reading ([§3.3](#33-verbal-clause-verb-selection)) is tried next; only if it
too fails is the clause an error, reported with the leftmost copular split's
diagnosis. When the slice contains **no** copula token at all the clause
falls through to the verbal reading directly. A copula at position 0 is
`EmptySubject`.

### 3.3 Verbal-clause verb selection

A verbal clause has no marker for where the subject ends and the verb
begins. Two candidate readings are tried, and when both succeed **the
shorter subject wins** (on a tie they are the same split):

**Noun-phrase-first (structured subjects).** The shortest prefix that parses
exactly as a noun-phrase group *carrying `of`-chain or relative structure*,
followed by a verbal tail — verb (an open-class, non-locative,
non-determiner word), optional particle, optional object, role phrases —
consuming the rest, is the clause: `When the owner of the file logs out,`
parses with subject head `owner`, of-chain `file`, verb `logs`, particle
`out`. Subjects *without* such structure never take this path, so the
determiner heuristic below keeps its readings and diagnoses.

The shorter-subject preference keeps a `before`/`after` guard from being
swallowed whole when its *nested* subject carries structure: in `When the
payment clears after the owner of the file approves,` the determiner
heuristic's split at `clears` (subject `the payment`, role
`After(the owner of the file approves)`) beats the noun-phrase-first
reading that would have read everything up to `approves` as one flat
subject noun phrase.

**The determiner heuristic (plain subjects).** The recognizer locates the
position just after the verb and reads the rest as the verbal tail:

1. Scan from the second token for the first word that opens a determiner
   (the subject's own determiner at position 0 is skipped), a locative
   preposition, or a role preposition. If found, the **verb is the word
   immediately before it** — `the temperature exceeds the limit`, `the pump
   runs at the depot`, `the payment clears after the order ships`. When
   that word is a particle with room for a subject and verb before it, the
   verb shifts one left (`the operator shuts down the server`).
2. Otherwise, if the slice has at least three tokens and ends in a bare
   number or a particle, the verb is the word before it — `the counter
   reaches zero`, `the user logs out` — **provided popping the final
   token leaves a run outside the ambiguous class of step 3**: `the
   client sends telemetry out` and `the counter reaches stage zero`
   REJECT (`ambiguous_verb_boundary`) exactly like their popped twins —
   the pop must not reopen the frontier.
3. Otherwise — **the fail-closed rule, round 11, superseding both the
   round-10 SVO acceptance and the round-3 final-word calibration for
   this class** — the subject is the *minimal* noun phrase (the
   position-0 determiner, multi-token count determiners included, plus
   one word; or a single bare word), and the trailing bare-word run after
   it decides:
   * a run of **two or more** words whose first word could be a verb (not
     a particle, not a reserved word; a pre-verbal manner prefix is
     SKIPPED before measuring — an `ly` word is never the verb, but it
     does not disambiguate the split either, so `the client quickly
     sends telemetry` is in the class) is the
     **genuinely ambiguous class** and is REJECTED
     (`ambiguous_verb_boundary`): the run admits both the
     minimal-subject SVO reading (`the client | sends | telemetry` —
     round 10) and the long-subject final-word reading (`the client
     sends | telemetry` — round 3), the two scramble each other's
     intended sentences (`the backup daemon sends telemetry` under SVO
     put every word in a wrong slot; `the client sends telemetry` under
     final-word swallowed the verb into the subject), and no
     lexicon-free rule can pick the intended split. Accepted-but-wrong
     is worse than rejection — the same discipline as `with`/`for`/`by`
     — so the class fails closed. Class membership is decided by
     **shape** (the run length and a verb-capable first run word), never
     by attempting both parses. The rewrites, each with a provable verb
     position:
     - a determiner on the object — `sends the telemetry` (the boundary
       of step 1);
     - an of-chain or a relative clause for a long subject — `the sensor
       of the temperature fails` (the noun-phrase-first path);
     - a role boundary after the verb — `fails at the depot` (step 1
       again).
     When the run's first word cannot be a verb, only one reading
     exists and it stands: `when the power up fails` keeps verb `fails`
     (a particle never opens a run), `the owner of files logs` keeps
     verb `logs` (`of` is reserved).
     The rejection is FINAL when it arises inside a content
     `that`-clause whose enclosing split is well-formed: `the monitor
     confirms that the client sends telemetry` rejects — the
     noun-phrase-first fallback must not re-read the content clause as
     an object-gap relative of a longer subject. Only when the
     enclosing split itself has no reading (its subject region does not
     parse — `the request that the gateway forwards fails` puts it at
     the bare determiner `the`) does the object-gap-relative reading
     proceed.
     Step 1 still outranks this rule, so a bare run followed by a role
     phrase reads by the boundary: `the client sends telemetry to the
     admin` parses subject `the client sends`, verb `telemetry`,
     recipient `admin` — the round-10 legislated flip, unchanged. Give
     the object a determiner to keep the intended reading under a role
     (`sends the telemetry to the admin`).
   * a run of **one** word keeps the verb-only reading — `a session
     expires`; a det-led two-word slice (`the pump runs`) is the same
     case (the SVO and final-word readings coincide there: verb only).

The final-word-verb rule prefers a non-`ly` verb: trailing `ly` words are
stripped first (while a subject token and a verb candidate remain) and
re-read as the manner run, so `When the export completes successfully,`
keeps `completes` as the verb with manner `successfully` — and the same
guard walks the boundary heuristic's verb position back over manner words
(`the export completes successfully before the timer expires`). When the
fully stripped reading leaves no parseable subject and verb, the rule
**backs off** innermost-first and the `ly`-final word itself is the verb —
`When the peers reply,` parses with verb `reply`, and `When the peers
reply quickly,` keeps verb `reply` with manner `quickly` (an `ly`-final
English verb such as `reply`, `apply`, `fly` under a plural subject is
writable without backticks).

The tail after the verb reads like a verb phrase — optional particle,
optional object, then thematic roles, consuming the slice exactly
(`unexpected_tokens` otherwise). The verb must not be a reserved word or a
locative preposition, and everything before it must parse exactly as the
subject.

**Clause groups (frames only).** A frame slice tries the coordinated reading
first: each conjunction whose prefix parses as a complete clause opens a
candidate split, tried in order, and a split is kept only if the remainder
itself reads as clauses the same way; all conjunctions must match
(`mixed_coordination` otherwise). The split therefore backtracks past a
conjunction that belongs to a coordinated object — `While the order ships the
report and the invoice and the payment clears,` splits at the second `and`,
keeping `the report and the invoice` inside the first clause. Where no split
survives, the slice is one clause — which is how `When the pump and the
valve are open,` stays a single clause with a coordinated subject while
`When the order ships and the payment is cleared,` becomes a two-clause
joint guard. After a trigger group parses, a semantic restriction applies:
an `and` group under `When`/`If` takes at most one event (verbal) conjunct —
more is `multiple_event_conjuncts`; `or` groups (alternation) and
`While`/`Where` frames are unrestricted.

### 3.4 Definiens: noun phrase before clause

The definiens owns everything after `means`. Its reading is decided in a
fixed order:

0. **If the definiens opens with `that`**, it is a full clause (verbal or
   copular) over the rest, unconditionally —
   `A timeout means that the request expires.` The canonical render of a
   clause definiens always re-emits the marker.
1. **If any token of the definiens is a clause copula** (`is` / `are` /
   `remains`), the definiens is a clause —
   `A valid token means the signature is correct.` If no clause exists
   because the copula belongs to a relative inside a noun phrase —
   `A widget means a part that is small.` — the noun-phrase reading is
   taken instead; if both readings fail, the clause reading's error is
   reported.
2. **Otherwise the noun-phrase reading is tried first**: a noun-phrase group
   (with the verb-phrase stop set, so trailing role phrases are recognized)
   that must consume the whole definiens —
   `A session means a sequence of requests from one client.`
3. **Only if the noun-phrase reading fails** is a verbal clause tried; if
   both fail, the noun-phrase reading's error is reported.

The rationale for NP-over-clause: with open-class words opaque, `a shared
folder` and `the request expires` are the *same shape* — determiner, word,
word. No dictionary distinguishes noun from verb, so one deterministic
reading has to win, and the noun-phrase one does: a bare phrase must never be
misread as subject `a shared` + verb `folder`. The price is symmetrical and
deliberate: `A timeout means the request expires.` is an NP definiens with
head `expires`. An author who wants the clause reading writes a copula —
`A timeout means the request is expired.` — which rule 1 makes unambiguous.

### 3.5 Role-phrase attachment

Thematic-role prepositions are closed only under the verb-phrase stop set
([§2](#2-closed-classes-and-stop-sets)), and role phrases are parsed in a
loop *after* the verb's object or complement completes. Because the stop set
propagates into nested phrases, the object's own material — including a
relative clause inside it — stops at any role preposition, so **a role
phrase always attaches to the enclosing verb phrase (or definiens), never to
a noun**: in `The system shall notify the user that owns the file via
email.`, `the file` ends at `via` and the Means role belongs to `notify`.
The only noun-attached preposition in the language is `of`.

The individual roles follow the EBNF, with three positional rules:

- **`be` takes a complement predicate unless a role preposition immediately
  follows it.** `be frozen` and `be equal to zero` have complements;
  `The receipt shall be from the gateway.` is bare `be` plus a Source role.
  Inside a complement the comparison openers are tried first, which is why
  `be equal to zero` has a comparison and no Recipient. A complement is
  parsed with the verb-phrase stop set, so it too ends at a role
  preposition: `be retained for 30 days` is complement `retained` plus a
  Duration.
- **`before` / `after` consume a clause running to the end of the current
  slice**, so one of them is necessarily the last role phrase of its verb
  phrase.
- **Order is free and duplicates are kept** in surface order; the loop simply
  attaches roles until the next token is not a role preposition.

### 3.6 Relative-clause attachment

A relative clause (`that` / `who` + body) is recognized at the end of a noun
phrase, *after* that phrase's `of`-chain. The two markers attach differently
(round 5, legislated):

- **`that` attaches to the nearest preceding head still open.** The
  `of`-chain is parsed recursively — an inner phrase claims its own `of`
  and its own `that`-relative before returning — so in `a sequence of
  requests that carry a token`, the relative belongs to `requests`.
- **`who` attaches to the ROOT of the `of`-chain.** An `of`-chain link
  leaves a `who` unconsumed for the chain root to claim, so in `the user
  of the workspace who is active`, the relative restricts the USER. The
  rule is linguistically motivated (`who` is animate; the chain root is
  the phrase's referent) and gives both attachments a spelling: `that`
  for the inner head, `who` for the outer. Both render after the full
  chain and round-trip.

The relative body is one copular or verbal unit. Since round 7 the verbal
unit is the FULL shared verbal tail — verb, optional particle, manner run,
optional object, and role phrases, parsed in verb-phrase context — so
`each request that arrives from the gateway` restricts by Source, and a
role written after a relative's object attaches to the RELATIVE's verb
(innermost attachment, legislated). Since round 9 a THIRD unit exists: the
OBJECT-GAP body — `each request that the gateway forwards` — recognized
deterministically when a determiner/quantifier-led noun phrase follows the
marker (the copular reading is tried first, so `that is …` never reaches
the gap trigger). The gap's subject is the SHORTEST prefix that parses
exactly as a noun-phrase group with a verb-position word after it, and its
tail is the shared verbal tail WITHOUT an object slot — the restricted
head is the missing object. A determiner-led object after the gap's verb
means the head is not the missing object: not a gap, and the sentence
keeps its `determiner_as_verb` diagnosis. A BARE noun phrase after the
marker never opens a gap (legislated: `that holds locks` must keep its
round-7 verb + object reading — no syntactic rule could tell it from a
gap's subject + verb). The body consumes exactly its own
material, stopping at the next stop word of the enclosing position. That
containment is what makes pivot detection structural
([§3.1](#31-pivot-detection-is-structural-and-leftmost)) and lets
relatives nest through their objects: `the queue of requests that carry a
token that is stale` hangs `that is stale` off `token`, inside the first
relative's object. Each relative body counts one level against the depth
bound ([§3.8](#38-the-depth-bound)), and a clausal role
(`before`/`after`/`until`) inside a relative consumes the rest of its
sentence part exactly as it does in a verb phrase.

### 3.7 Coordination grouping

A coordination is a **flat list**, parsed iteratively: first item, then
`conj item` repeated. There is no nesting and no precedence to resolve,
because the grammar refuses every input that would need one:

- One conjunction throughout — `and` and `or` in the same group is
  `MixedCoordination`, as are two conjunctions in a row (`and or`).
- `both` pairs with `and`, `either` with `or`, each over exactly two items;
  a wrong pairing, a third item, or a marker with no conjunction at all is
  `MixedCoordination`.

A group may appear in any noun-phrase slot except two places that need a
single phrase: a definition's **term** (a coordinated term has no single
definition; the conjunction is rejected as `UnexpectedTokens`) and the
**lower bound of `between`** (`measure-single`), where a coordinated phrase
would swallow the comparison's own `and` — in `between 5 and 30 seconds`,
the `and` must remain the comparison's.

### 3.8 The depth bound

`of`-links, relative clauses, and `before`/`after` clauses are the only
recursion in the grammar; the first two enter `parse_np` a level deeper, a
`before`/`after` role enters `parse_clause` a level deeper, and every entry
checks the depth. At **64 levels** the input is rejected with
`PhraseTooDeep`. The bound is a
totality guarantee, not a stylistic limit: recursion depth is otherwise
proportional to input length, and an adversarial chain thousands of levels
deep would overflow the stack — an abort, not an error. Everything unbounded
in honest input — coordination width, role-phrase count, frame count,
sentence count — is iterative and unaffected. See
[phrases.md](./phrases.md#the-phrase-depth-bound).

## 4. The recognizer, step by step

The parser is a hand-written recursive descent over a flat token list. Each
function recognizes one production:

| `parse.rs` function | Production |
| --- | --- |
| `parse` | `specification` |
| `split_sentences`, `tokenize` | the lexical layer ([lexical.md](./lexical.md)) |
| `parse_sentence` | `sentence` |
| `parse_frames` | `frames`, `trigger` |
| `parse_core` | `core` (subject + pivot dispatch) |
| `parse_deontic`, `parse_description`, `parse_definition` | the three core shapes |
| `parse_definiens` | `definiens` |
| `parse_clause` | `clause` |
| `parse_vp`, `parse_roles` | `vp`, `role-pp` |
| `parse_np_group`, `parse_np`, `parse_relative_body` | `np-group`, `np`, `relative` |
| `parse_predicate`, `parse_comparison` | `predicate`, `comparison` |
| `parse_measure`, `parse_quantity`, `parse_det` | `measure`, `number`, `det` |

For one sentence, in order:

1. **Split and tokenize.** The input is split into per-sentence slices at
   terminating periods, each slice kept verbatim as `Sentence::source`, then
   tokenized into words, commas, and terminators. A trailing terminator
   token is dropped; a terminator anywhere else is `UnexpectedTokens` (a `.`
   can sit mid-sentence only when the sentence splitter did not see it as
   word-final, e.g. `pump.,`); no tokens at all is `Empty`.
2. **Frames.** `parse_frames` loops while the next token is `where`,
   `while`, `when`, or `if`, taking each clause up to its mandatory comma
   (`UnterminatedFrame` / `EmptyFrame` otherwise) and enforcing canonical
   order as it goes: a `where` after any `while` is `FrameOrder`; any frame
   after the trigger is `FrameOrder`, or `MultipleTriggers` if it is a
   second trigger. A `then` directly after a frame's comma is consumed for
   `if` and rejected as `ThenWithoutIf` for the rest.
3. **Comma segmentation.** The remaining tokens are split at every comma.
   The first segment is the core; each later segment must begin a complete
   adjunct: `unless <clause>` (at most once, and only before any purpose),
   then `so that <clause>` or `in order to <vp>` (at most once). Any other
   segment opener — including a second exception, an exception after the
   purpose, or a bare continuation — is `UnexpectedTokens`. An `in order to`
   purpose ends through the same end-check as a core, so a frame keyword
   inside it is `MidSentenceFrame`.
4. **The core.** `parse_core` parses the subject, dispatches on the pivot
   ([§3.1](#31-pivot-detection-is-structural-and-leftmost)), and requires
   the segment to be consumed exactly.
5. **The definition post-check.** After the whole sentence is assembled, a
   definition core with any `While` frame or trigger is rejected as
   `FrameOnDefinition` — a definition is timeless; only `Where` may scope
   it.

A compact trace of
`While the engine runs, the pump shall stop, unless the override is active.`:

| Step | State |
| --- | --- |
| split, tokenize | one sentence; trailing terminator dropped |
| frames | `While` opens a frame; clause tokens `the engine runs` up to the comma; verbal reading (no copula): no determiner after position 0, final word `runs` is the verb, subject `the engine` |
| segmentation | segments: `the pump shall stop` · `unless the override is active` |
| core | subject `the pump` halts at pivot `shall`; deontic, not negated; vp verb `stop`, no object, no roles; segment exhausted |
| adjunct | `unless` + clause: copula split at `is`, left side `the override` parses exactly; predicate `active` consumes the rest |
| post-check | not a definition; no check fires |

## 5. Totality

The recognizer is total and never panics, on any `&str`:

- **Everything is tokens.** The input is split on ASCII whitespace and
  trailing punctuation is peeled per word; the grammar walks whole tokens
  and never slices at fixed byte offsets, so multibyte input (`café`,
  `中文`, emoji, lone combining marks) flows through as opaque open-class
  words.
- **Every path returns.** Each grammar function either advances or returns
  an error; delimited slices are checked for exact consumption; the one
  source of unbounded recursion is cut off by the depth bound
  ([§3.8](#38-the-depth-bound)).
- **Rejection is exact.** Every failure is one `ParseError` variant with a
  message naming the surface material and, where one exists, the canonical
  rewrite — `may not` → `shall not`, `can` → `shall`, a trailing condition →
  a leading frame, mixed `and`/`or` → one conjunction or two sentences. The
  full taxonomy is [errors.md](./errors.md).

These properties are enforced by the test suite:
[`corpus.rs`](../../so_reason/tests/corpus.rs) pins the acceptance corpus and
render round-trips, [`attack_conformance.rs`](../../so_reason/tests/attack_conformance.rs)
pins the deterministic-reading rules and every rejection, and
[`attack_totality.rs`](../../so_lang/tests/attack_totality.rs) attacks the
recognizer with multibyte boundaries, punctuation floods, deep nesting, wide
coordination, and seeded word soup — every input must yield `Ok` or `Err`,
never a panic.

## See also

- [sentences.md](./sentences.md) — the sentence layer in prose: cores,
  frames, exceptions, purposes.
- [phrases.md](./phrases.md) — the phrase grammar in prose: noun phrases,
  verb phrases, predicates, measures, negation sites.
- [lexical.md](./lexical.md) — sentence splitting, tokenization, casing,
  multibyte safety.
- [errors.md](./errors.md) — every `ParseError` variant with triggers and
  rewrites.
- [cookbook.md](./cookbook.md) — accepted and rejected specifications, each
  traced to its structure or error.
