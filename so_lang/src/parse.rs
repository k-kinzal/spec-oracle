//! The total recognizer for the constrained specification language.
//!
//! [`parse`] maps any input string to exactly one [`crate::ast::Specification`]
//! or exactly one [`ParseError`] — never a panic, never a partial tree, never a
//! guess. The recognizer is a hand-written recursive descent over a flat token
//! list: closed-class keywords are recognized case-insensitively and only in
//! the positions where they are closed (e.g. `of` is special inside a noun
//! phrase, `to` at a thematic-role position), while open-class words — nouns,
//! verbs, adjectives, URLs, identifiers — pass through as opaque tokens.
//!
//! Errors speak the surface vocabulary: sentences, frames, cores, subjects,
//! predicates. The assume-guarantee reading lives in [`crate::semantics`] and
//! has no place in a syntax diagnostic.

use crate::ast::*;
use thiserror::Error;

// ---- tokens ---------------------------------------------------------------------

/// One token of the surface string. Words keep their surface casing; the
/// closed-class test is always case-insensitive and positional.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Token {
    /// Any whitespace-delimited word (after punctuation splitting).
    Word(String),
    /// A trailing comma split off a word.
    Comma,
    /// A sentence-final period split off a word.
    Terminator,
}

impl Token {
    /// The word, if this token is one.
    fn word(&self) -> Option<&str> {
        match self {
            Token::Word(w) => Some(w.as_str()),
            _ => None,
        }
    }

    /// Case-insensitive keyword test; false for punctuation tokens.
    fn is_kw(&self, kw: &str) -> bool {
        self.word().is_some_and(|w| w.eq_ignore_ascii_case(kw))
    }

    /// How the token reads in an error message.
    fn display(&self) -> String {
        match self {
            Token::Word(w) => w.clone(),
            Token::Comma => ",".to_string(),
            Token::Terminator => ".".to_string(),
        }
    }
}

/// Split the input into tokens. A `.` is a terminator only when it ends a
/// whitespace-delimited word and is followed by whitespace or end of input, so
/// decimals (`5.5`) and URLs (`http://host:4318`) stay glued. A `,` at the end
/// of a word is always its own token.
///
/// Backtick escape hatch: a token wrapped in backticks (`` `will` ``, length
/// ≥ 3) is always an open-class word. The backticks are part of the token
/// text and are preserved into the tree and the canonical render
/// (losslessness), and every closed-class test in this recognizer compares
/// the full token text, so a backticked token never matches a keyword — not
/// as a modal, frame keyword, pivot, preposition, conjunction, or
/// determiner. An unmatched single backtick is an ordinary word character.
pub(crate) fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    for raw in input.split_ascii_whitespace() {
        let mut word = raw;
        let mut trailing: Vec<Token> = Vec::new();
        // Peel trailing punctuation (a word may end `total.,` in pathological
        // input; peel repeatedly so every mark is its own token).
        loop {
            if let Some(stripped) = word.strip_suffix(',') {
                trailing.push(Token::Comma);
                word = stripped;
            } else if let Some(stripped) = word.strip_suffix('.') {
                // Word-final `.` — the whitespace split already guarantees it
                // is followed by whitespace or end of input.
                trailing.push(Token::Terminator);
                word = stripped;
            } else {
                break;
            }
        }
        if !word.is_empty() {
            tokens.push(Token::Word(word.to_string()));
        }
        tokens.extend(trailing.into_iter().rev());
    }
    tokens
}

// ---- errors ---------------------------------------------------------------------

/// One precise, actionable rejection. Every variant names the surface material
/// it is about; none speak of assumptions or guarantees.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseError {
    /// The input contains no sentence at all.
    #[error("the specification is empty: write at least one sentence")]
    Empty,
    /// A frame clause ran to the end of the sentence without its comma.
    #[error("the `{keyword}` frame is missing the comma that ends its clause")]
    UnterminatedFrame { keyword: String },
    /// A frame keyword immediately followed by its comma.
    #[error("the `{keyword}` frame has an empty clause")]
    EmptyFrame { keyword: String },
    /// Frames out of canonical order (`Where`, then `While`, then the trigger).
    #[error(
        "the `{keyword}` frame must come before {after}: frames read Where, While, then When/If"
    )]
    FrameOrder { keyword: String, after: String },
    /// Two trigger frames; a sentence has at most one `When`/`If`.
    #[error("a sentence takes one trigger frame: `{second}` cannot follow `{first}`")]
    MultipleTriggers { first: String, second: String },
    /// `then` after a frame that is not an `if` clause.
    #[error("`then` belongs only after an `If …,` clause")]
    ThenWithoutIf,
    /// A `While`/`When`/`If` frame on a definition, which is timeless.
    #[error("a definition is timeless: only `Where` frames may scope it, not `{keyword}`")]
    FrameOnDefinition { keyword: String },
    /// A frame keyword in the middle of the core: conditions lead the sentence.
    #[error("`{keyword}` appears mid-sentence: conditions lead the sentence, as in `{keyword} …, <subject> shall …`")]
    MidSentenceFrame { keyword: String },
    /// No `shall`/`must`/`should`/`may`/`is`/`are`/`means` found.
    #[error("the sentence has no pivot: expected shall, must, should, may, is, are, or means after the subject")]
    MissingPivot,
    /// A modal outside the supported four.
    #[error("`{word}` is not a supported modal: use shall, must, should, or may — or write capability as `is able to <response>`")]
    UnsupportedModal { word: String },
    /// `may not` — permission-denial vs. prohibition is ambiguous.
    #[error("`may not` is ambiguous: write `shall not` for a prohibition")]
    AmbiguousModal,
    /// A `no` subject under `may` — `No client may retry.` is a prohibition
    /// wearing a permission's modal, the same legislated-ambiguity family as
    /// `may not`.
    #[error("`no` with `may` is a denial of permission: write `<subject> shall not <response>` for a prohibition")]
    NoWithMay,
    /// `is not` / `are not` in a description.
    #[error(
        "a description is not negated with `not`: write `never`, or `shall not` for an obligation"
    )]
    NegatedDescription,
    /// A pivot with no subject before it.
    #[error("the sentence has no subject before its pivot")]
    EmptySubject,
    /// A modal with nothing after it.
    #[error("the modal needs a response: write what the subject shall do")]
    EmptyVp,
    /// A copula or comparison site with nothing after it.
    #[error("the predicate is empty: write what is asserted of the subject")]
    EmptyPredicate,
    /// `means` with nothing after it.
    #[error("`means` needs a definiens: write what the term stands for")]
    EmptyDefiniens,
    /// `and` and `or` mixed in one coordination, or a `both`/`either` marker
    /// that does not match its conjunction and item count.
    #[error("a coordination uses one conjunction throughout: `both … and …` or `either … or …`, never mixed")]
    MixedCoordination,
    /// Well-formed material followed by tokens the grammar cannot place.
    #[error("unexpected `{token}`: the sentence was complete before it")]
    UnexpectedTokens { token: String },
    /// A phrase nested beyond the recognizer's depth budget: `of` links,
    /// relative clauses, and `before`/`after` clauses recurse, and a bound
    /// keeps the recognizer total on adversarially deep input.
    #[error("the phrase nests too deeply: more than {limit} levels of `of` phrases, relative clauses, or `before`/`after` clauses")]
    PhraseTooDeep { limit: usize },
    /// Two or more event (verbal) conjuncts under `and` in one trigger: the
    /// conjunction of occurrences is simultaneity, which has no single
    /// reading — the same ambiguity the one-trigger rule legislates away.
    #[error("a trigger's `and` group takes one event: keep one verbal conjunct and write the others as states (`is/are/remains …`), or move them to a `While` frame")]
    MultipleEventConjuncts,
    /// `unless` opening a sentence: an exception trails the core.
    #[error("`unless` cannot open a sentence: the exception follows the core, as in `The pump shall stop, unless the override is active`")]
    LeadingException,
    /// A quantifier (`at least`/`at most`/`exactly`) whose number is a decimal
    /// or too large to count: falling through silently would erase the
    /// quantifier's meaning from the tree.
    #[error("a quantifier counts whole things: `{word}` is not a usable whole number")]
    QuantifierNotWhole { word: String },
    /// A word-shaped token in a position that requires a number, outside
    /// the number-word table (round 12): `at least eleventy nodes` used to
    /// silently degrade the quantifier into open-class modifier words, and
    /// `within eleventy seconds` into a noun-phrase measure that never
    /// grounds an interval. The table is `zero`–`twenty`, the tens
    /// `thirty`–`ninety`, and `hundred` — single words only; compounds
    /// (`twenty-one`) are deliberately out and land here too.
    #[error("`{word}` is not a recognized number word (`zero`–`twenty`, tens to `ninety`, `hundred`; no compounds): write the number in digits")]
    UnknownNumberWord { word: String },
    /// `for` in role position without a quantity: a duration needs a
    /// measure, and `listen for requests` silently misread as a duration
    /// over a noun phrase was an accepted-but-wrong tree (round 5).
    #[error("`for` opens a duration and needs a quantity, as in `for 5 seconds`: write `about <topic>` for a topic, `until <clause>` to wait on an event, or reword")]
    ForRequiresMeasure,
    /// `with` where a thematic role could start, or — round 6 — inside ANY
    /// noun phrase (subject positions included): instrument vs
    /// accompaniment vs attachment has no single reading, so the grammar
    /// legislates it away everywhere instead of silently folding it into
    /// modifiers.
    #[error("`with` is ambiguous between instrument, accompaniment, and attachment: write `using <means>` for an instrument, coordinate the phrases with `and`, restrict with a relative clause (`the file that carries the flag`), or backtick the word (`` `with` ``) to use it as a noun")]
    WithIsAmbiguous,
    /// `by` in role position outside a passive site (`be <predicate>` or a
    /// description/copular predicate): the passive agent is the only `by`
    /// role the grammar admits (round 5).
    #[error("`by` marks a passive agent and belongs after `be <predicate>` or a description's predicate: write `within <measure>` for a deadline, `until <clause>` to wait on an event, or reword the active sentence")]
    ByOutsidePassive,
    /// `not` over `either … or …` verb-phrase alternatives (round 6,
    /// legislated): the De Morgan reading (`neither`) would surprise at
    /// ingest, so negated alternatives are rejected — write the two
    /// prohibitions separately.
    #[error("`not` does not combine with `either … or …` alternatives: write two prohibitions, one per alternative")]
    NegatedAlternatives,
    /// A determiner at verb position (round 6 follow-up): `The pump shall
    /// the valve.` — and the determiner-led tail of an `either … or …`
    /// alternative (`shall either notify the admin or the owner`) — used
    /// to parse with the determiner as an open-class VERB, an
    /// accepted-but-wrong tree. A response is a verb phrase; a determiner
    /// can only open a noun phrase.
    #[error("`{word}` opens a noun phrase where a verb is required: each response — and each `either … or …` alternative — is a verb phrase, as in `either notify the admin or notify the owner` (for a choice of objects, write `notify either the admin or the owner`)")]
    DeterminerAsVerb { word: String },
    /// A `between` whose two numeric bounds DESCEND (round 9): `between 6
    /// and 4 seconds` denotes the empty interval — a claim that can never
    /// hold and (per the interval rules) contradicts everything, itself
    /// included. Nobody writes an empty interval on purpose; the shape is
    /// a typo, so the recognizer rejects it instead of freezing an
    /// unsatisfiable claim. Numeric literals and number words only: a
    /// noun-phrase bound (`between the floor and the ceiling`) is a value
    /// name and stays unchecked, and EQUAL bounds are a point interval —
    /// fine. Applies to comparison predicates and bounded `for` measures
    /// alike. Hand-built trees can still hold an empty interval; the
    /// satisfiability machinery keeps covering those.
    #[error("`between {lower} and {upper}` is a descending, empty interval: swap the bounds and write `between {upper} and {lower}`")]
    DescendingBetween { lower: String, upper: String },
    /// A bound opener (`at least`/`at most`/`greater than`/`less than`/
    /// `between`) after `within` (round 6 follow-up): a deadline is already
    /// an upper bound, and `within at least 5 seconds` used to be silently
    /// consumed as a counted noun-phrase measure (`at least 5` of
    /// `seconds`) that never grounds an interval — accepted-but-misleading.
    /// Bounded measures belong to `for` durations only (legislated).
    #[error("`within` already means an upper bound and takes a plain measure, as in `within 5 seconds`: bounded measures belong to `for` durations (`for at least 30 days`)")]
    WithinTakesPlainMeasure,
    /// The residual verb-boundary ambiguity (round 11, FAIL-CLOSED —
    /// supersedes the round-10 SVO acceptance AND the round-3 final-word
    /// acceptance for this class): a verbal clause whose subject region has
    /// no boundary (no determiner-led object, no role or locative
    /// preposition, no of-chain or relative structure) and whose trailing
    /// bare-word run admits BOTH the minimal-subject SVO reading (`the
    /// client | sends | telemetry`) and the long-subject final-word reading
    /// (`the client sends | telemetry`). Accepted-but-wrong is worse than
    /// rejection — the same discipline as `with`/`for`/`by` — so the class
    /// is rejected with rewrites instead of legislating either reading.
    #[error("the verb boundary is ambiguous: the clause reads both subject-verb-object from the minimal subject (`the client | sends | telemetry`) and verb-last from the long subject (`the client sends | telemetry`): put a determiner on the object (`sends the telemetry`), use an of-chain or a relative clause for a long subject (`the sensor of the temperature fails`), or add a role boundary (`fails at the depot`)")]
    AmbiguousVerbBoundary,
}

impl ParseError {
    /// A stable snake_case name for telemetry.
    pub fn kind(&self) -> &'static str {
        match self {
            ParseError::Empty => "empty",
            ParseError::UnterminatedFrame { .. } => "unterminated_frame",
            ParseError::EmptyFrame { .. } => "empty_frame",
            ParseError::FrameOrder { .. } => "frame_order",
            ParseError::MultipleTriggers { .. } => "multiple_triggers",
            ParseError::ThenWithoutIf => "then_without_if",
            ParseError::FrameOnDefinition { .. } => "frame_on_definition",
            ParseError::MidSentenceFrame { .. } => "mid_sentence_frame",
            ParseError::MissingPivot => "missing_pivot",
            ParseError::UnsupportedModal { .. } => "unsupported_modal",
            ParseError::AmbiguousModal => "ambiguous_modal",
            ParseError::NoWithMay => "no_with_may",
            ParseError::NegatedDescription => "negated_description",
            ParseError::EmptySubject => "empty_subject",
            ParseError::EmptyVp => "empty_vp",
            ParseError::EmptyPredicate => "empty_predicate",
            ParseError::EmptyDefiniens => "empty_definiens",
            ParseError::MixedCoordination => "mixed_coordination",
            ParseError::UnexpectedTokens { .. } => "unexpected_tokens",
            ParseError::PhraseTooDeep { .. } => "phrase_too_deep",
            ParseError::MultipleEventConjuncts => "multiple_event_conjuncts",
            ParseError::LeadingException => "leading_exception",
            ParseError::QuantifierNotWhole { .. } => "quantifier_not_whole",
            ParseError::UnknownNumberWord { .. } => "unknown_number_word",
            ParseError::ForRequiresMeasure => "for_requires_measure",
            ParseError::WithIsAmbiguous => "with_is_ambiguous",
            ParseError::ByOutsidePassive => "by_outside_passive",
            ParseError::NegatedAlternatives => "negated_alternatives",
            ParseError::DeterminerAsVerb { .. } => "determiner_as_verb",
            ParseError::DescendingBetween { .. } => "descending_between",
            ParseError::WithinTakesPlainMeasure => "within_takes_plain_measure",
            ParseError::AmbiguousVerbBoundary => "ambiguous_verb_boundary",
        }
    }
}

// ---- closed-class vocabulary ------------------------------------------------------

/// The pivot keywords that end a subject and open a core.
const PIVOTS: &[&str] = &["shall", "must", "should", "may", "is", "are", "means"];
/// Modals the language deliberately excludes.
const UNSUPPORTED_MODALS: &[&str] = &["can", "will", "would", "could", "might", "ought"];
/// Keywords that open (or carve out of) a circumstance frame.
const FRAME_KEYWORDS: &[&str] = &["where", "while", "when", "if", "unless"];
/// Prepositions that open a thematic-role phrase inside a verb phrase.
/// `with` and `by` are RESERVED at role positions since round 5 — `with`
/// only to be rejected (instrument vs accompaniment is ambiguous), `by`
/// admitted solely as the passive agent — so neither is ever silently
/// swallowed into an object noun phrase again. In plain (subject/predicate)
/// noun phrases both remain open-class words.
const ROLE_PREPS: &[&str] = &[
    "to", "via", "using", "about", "within", "for", "per", "before", "after", "until", "from",
    "into", "with", "by",
];
/// The number words admitted in quantifier and measure positions, with
/// their values (round 12, change 4 — extends the round-1 `zero`–`ten`
/// run): `zero` through `twenty`, then the tens `thirty`–`ninety`, then
/// `hundred`. SINGLE WORDS ONLY, documented: compounds (`twenty-one`,
/// `one hundred`) are not recognized — a compound in a number position is
/// rejected fail-closed as [`ParseError::UnknownNumberWord`] with the
/// rewrite hint (write digits), never silently degraded to open-class
/// words.
const NUMBER_WORDS: &[(&str, u64)] = &[
    ("zero", 0),
    ("one", 1),
    ("two", 2),
    ("three", 3),
    ("four", 4),
    ("five", 5),
    ("six", 6),
    ("seven", 7),
    ("eight", 8),
    ("nine", 9),
    ("ten", 10),
    ("eleven", 11),
    ("twelve", 12),
    ("thirteen", 13),
    ("fourteen", 14),
    ("fifteen", 15),
    ("sixteen", 16),
    ("seventeen", 17),
    ("eighteen", 18),
    ("nineteen", 19),
    ("twenty", 20),
    ("thirty", 30),
    ("forty", 40),
    ("fifty", 50),
    ("sixty", 60),
    ("seventy", 70),
    ("eighty", 80),
    ("ninety", 90),
    ("hundred", 100),
];

/// The value of a number word, if the word is one.
fn number_word_value(word: &str) -> Option<u64> {
    NUMBER_WORDS
        .iter()
        .find(|(kw, _)| word.eq_ignore_ascii_case(kw))
        .map(|(_, n)| *n)
}

fn in_list(list: &[&str], word: &str) -> bool {
    list.iter().any(|kw| word.eq_ignore_ascii_case(kw))
}

/// The prepositions that open a `Location` role in a verb phrase. `at` opens
/// a location only when it is not the comparison opener `at least`/`at most`.
const LOCATIVE_PREPS: &[&str] = &["in", "on", "at", "under", "over", "above", "below"];

/// The closed particle-verb list: one of these immediately after a verb (in a
/// verb phrase or a verbal clause body) is the verb's particle, not an object
/// head (`logs out`, `shuts down the server`), and one left trailing the
/// verb's object joins the verb the same way (`lift the beam up` — see
/// [`pop_object_particle`]). `in`/`on` are NOT particles — they open
/// Location roles; hyphenation (`logs-in`) stays the workaround. The rule is
/// deterministic: in the list AND the verb has no particle yet → particle;
/// any other occurrence is an ordinary word, and a backticked token
/// (`` `out` ``) never matches.
const PARTICLES: &[&str] = &["out", "down", "up", "off"];

/// The particle at `pos`, if the word there is one.
fn particle_at(tokens: &[Token], pos: usize) -> Option<&str> {
    word_at(tokens, pos).filter(|w| in_list(PARTICLES, w))
}

/// The manner adverb at `pos`, if the word there is one: a bare token ending
/// in ASCII `ly` (case-insensitive, length > 2) that is not reserved, not a
/// role or locative preposition, and not a number. The rule is positional —
/// callers apply it only in POST-VERBAL position, where an object or role
/// would start; inside a noun phrase (after a determiner, or as a modifier
/// before a head) `ly` words stay ordinary open-class words (`the assembly`,
/// `the nightly build`). A backticked token keeps its backticks, so it never
/// ends in `ly` and never matches (`` record `supply` `` keeps its object).
/// A determiner-led position is never manner: `exactly 7 copies` keeps its
/// quantifier (and `exactly 5.5` keeps its [`ParseError::QuantifierNotWhole`]
/// diagnosis).
fn manner_at(tokens: &[Token], pos: usize) -> Option<&str> {
    if parse_det(tokens, pos).is_some() || broken_quantifier(tokens, pos).is_some() {
        return None;
    }
    word_at(tokens, pos).filter(|w| {
        w.len() > 2
            && w.is_ascii()
            && w[w.len() - 2..].eq_ignore_ascii_case("ly")
            && !is_np_stop(w, NpCtx::Vp)
            && !in_list(LOCATIVE_PREPS, w)
            && !is_number(w)
    })
}

/// Consume a run of juxtaposed manner adverbs at `pos`. Only juxtaposition
/// extends the run (`stop immediately` — legislated): a conjunction after a
/// manner word ends the run, so `quickly and safely` is not supported and
/// the leftover `and …` is diagnosed as unexpected material.
fn manner_run(tokens: &[Token], pos: usize) -> (Vec<String>, usize) {
    let mut manner = Vec::new();
    let mut at = pos;
    while let Some(word) = manner_at(tokens, at) {
        manner.push(word.to_string());
        at += 1;
    }
    (manner, at)
}

/// The syntactic context a noun phrase is collected in. It decides which
/// prepositions are closed-class (and therefore end open-class collection).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum NpCtx {
    /// Subject positions outside verb phrases: role and locative
    /// prepositions stay open-class.
    Plain,
    /// Inside a verb phrase or a verbal clause body: role prepositions and
    /// locative prepositions are closed — they end the phrase and open a
    /// thematic role. (Verbal clause bodies carry the same role phrases as
    /// verb phrases since round 3.)
    Vp,
    /// Inside a description's or a copular clause's predicate: open-class
    /// like `Plain`, except `by` is closed — it opens the passive Agent
    /// phrase after the predicate (round 5), so it must end collection in a
    /// `Predicate::Pp` noun phrase or a comparison's noun-phrase measure
    /// exactly as it ends open-word collection, never folding into the
    /// phrase.
    Predicate,
}

impl NpCtx {
    /// Role prepositions end collection only inside a verb phrase.
    fn stops_roles(self) -> bool {
        self == NpCtx::Vp
    }

    /// Locative prepositions end collection in verb phrases.
    fn stops_locatives(self) -> bool {
        self == NpCtx::Vp
    }

    /// `by` ends collection wherever a passive Agent phrase may follow: in
    /// predicate positions (descriptions and copular clauses) — in verb
    /// phrases it is already closed as a role preposition.
    fn stops_agent_by(self) -> bool {
        self == NpCtx::Predicate
    }
}

/// The locative preposition opening at `pos`, if one does: a word from
/// [`LOCATIVE_PREPS`], except `at` immediately followed by `least`/`most`,
/// which stays the comparison path.
fn locative_at(tokens: &[Token], pos: usize) -> Option<&str> {
    let word = word_at(tokens, pos).filter(|w| in_list(LOCATIVE_PREPS, w))?;
    if word.eq_ignore_ascii_case("at")
        && (kw_at(tokens, pos + 1, "least") || kw_at(tokens, pos + 1, "most"))
    {
        return None;
    }
    Some(word)
}

/// Words that always end open-class collection: pivots, frame keywords,
/// noun-phrase structure (`of`, `that`, `who`), coordination, clause copulas,
/// and the excluded modals (so they can be diagnosed at pivot position).
fn is_reserved(word: &str) -> bool {
    in_list(PIVOTS, word)
        || in_list(UNSUPPORTED_MODALS, word)
        || in_list(FRAME_KEYWORDS, word)
        || in_list(
            &[
                "of", "that", "who", "and", "or", "both", "either", "remains", "then", "not",
            ],
            word,
        )
}

/// Where open-class collection stops. Role prepositions are closed only inside
/// a verb phrase; elsewhere they are ordinary words.
fn is_np_stop(word: &str, ctx: NpCtx) -> bool {
    is_reserved(word)
        || (ctx.stops_roles() && in_list(ROLE_PREPS, word))
        || (ctx.stops_agent_by() && word.eq_ignore_ascii_case("by"))
}

/// Whether the token at `pos` is a coordination group marker (`both`/`either`).
/// Markers are reserved words, so positions that accept a noun-phrase group
/// must admit them explicitly.
fn group_marker_at(tokens: &[Token], pos: usize) -> bool {
    word_at(tokens, pos)
        .is_some_and(|w| w.eq_ignore_ascii_case("both") || w.eq_ignore_ascii_case("either"))
}

/// A numeral token (`5`, `5.5`) — full-token match only.
fn is_numeral(word: &str) -> bool {
    let mut parts = word.splitn(2, '.');
    let int = parts.next().unwrap_or("");
    let frac = parts.next();
    !int.is_empty()
        && int.bytes().all(|b| b.is_ascii_digit())
        && frac.is_none_or(|f| !f.is_empty() && f.bytes().all(|b| b.is_ascii_digit()))
}

/// A number in quantifier/measure position: a numeral or a number word.
fn is_number(word: &str) -> bool {
    is_numeral(word) || number_word_value(word).is_some()
}

/// The numeric value of a quantifier number, for `Det::AtLeast`-style
/// determiners (which store a value, not a surface string).
fn number_value(word: &str) -> Option<u64> {
    if let Ok(n) = word.parse::<u64>() {
        return Some(n);
    }
    number_word_value(word)
}

/// The numeric value of a MEASURE number lexeme (round 9): numerals —
/// decimals included — and the grammar's number words. Only the
/// descending-`between` typo shield reads numbers at parse time; interval
/// semantics downstream keeps its own copy of this reading.
fn measure_value(word: &str) -> Option<f64> {
    if let Ok(n) = word.parse::<f64>() {
        return n.is_finite().then_some(n);
    }
    number_word_value(word).map(|n| n as f64)
}

/// FAIL CLOSED on an unknown number word (round 12, change 4): the token
/// at `pos` sits in a position that requires a number, is made of ASCII
/// letters and hyphens (a word-shaped token — hyphens admit compounds
/// like `twenty-one`, which are deliberately unsupported), is NOT a
/// recognized number (numeral or table word), and does not open other
/// grammar structure (a determiner or a reserved word — `at least the
/// limit` stays whatever its position makes of it; LEGISLATED carve-out,
/// see the callers). Without this, `at least eleventy nodes` silently
/// degraded the quantifier into open-class modifier words.
fn unknown_number_word_at(tokens: &[Token], pos: usize) -> Option<ParseError> {
    let word = word_at(tokens, pos)?;
    (!is_number(word)
        && !word.is_empty()
        && word.bytes().all(|b| b.is_ascii_alphabetic() || b == b'-')
        && word.bytes().any(|b| b.is_ascii_alphabetic())
        && !is_reserved(word)
        && parse_det(tokens, pos).is_none())
    .then(|| ParseError::UnknownNumberWord {
        word: word.to_string(),
    })
}

/// The unknown-number-word check behind a QUANTIFIER OPENER (round 12,
/// change 4): locates the number position of `at least` / `at most` /
/// `exactly` exactly as [`broken_quantifier`] does, then applies
/// [`unknown_number_word_at`] there. Kept separate from
/// [`broken_quantifier`], which several sites use as a boolean probe
/// (manner adverbs, the object-gap scan) whose meaning must not widen.
fn unknown_quantifier_number(tokens: &[Token], pos: usize) -> Option<ParseError> {
    let word = word_at(tokens, pos)?;
    let number_at = if word.eq_ignore_ascii_case("exactly") {
        pos + 1
    } else if word.eq_ignore_ascii_case("at")
        && (kw_at(tokens, pos + 1, "least") || kw_at(tokens, pos + 1, "most"))
    {
        pos + 2
    } else {
        return None;
    };
    unknown_number_word_at(tokens, number_at)
}

/// Reject a provably DESCENDING `between` (round 9): both bounds are
/// numeric and the lower parses strictly greater than the upper — the
/// silently-empty interval is a typo, not a claim. Equal bounds (a point)
/// and noun-phrase bounds pass through.
fn check_between_order(lower: &str, upper: &str) -> Result<(), ParseError> {
    if let (Some(lo), Some(hi)) = (measure_value(lower), measure_value(upper)) {
        if lo > hi {
            return Err(ParseError::DescendingBetween {
                lower: lower.to_string(),
                upper: upper.to_string(),
            });
        }
    }
    Ok(())
}

/// The word at `pos`, if the token there is a word.
fn word_at(tokens: &[Token], pos: usize) -> Option<&str> {
    tokens.get(pos).and_then(Token::word)
}

/// Case-insensitive keyword test at a position.
fn kw_at(tokens: &[Token], pos: usize, kw: &str) -> bool {
    tokens.get(pos).is_some_and(|t| t.is_kw(kw))
}

/// How the token at `pos` reads in an error message. When `pos` is past the
/// end of the material (a phrase truncated where more was required), the
/// "token" reads `end of sentence`.
fn unexpected(tokens: &[Token], pos: usize) -> ParseError {
    ParseError::UnexpectedTokens {
        token: tokens
            .get(pos)
            .map(Token::display)
            .unwrap_or_else(|| "end of sentence".to_string()),
    }
}

// ---- noun-phrase layer ------------------------------------------------------------

/// How deep noun phrases may nest through `of` links and relative clauses.
/// Recursion depth is otherwise proportional to input length, and a chain a
/// few thousand levels deep overflows the stack — an abort, not an error. No
/// sentence a person writes nests anywhere near this bound.
const MAX_NP_DEPTH: usize = 64;

/// Parse a determiner or quantifier at `pos`, if one is present. `at least` /
/// `at most` / `exactly` only count when a number follows; otherwise the words
/// stay open-class.
fn parse_det(tokens: &[Token], pos: usize) -> Option<(Det, usize)> {
    let word = word_at(tokens, pos)?;
    let simple = match word.to_ascii_lowercase().as_str() {
        "the" => Some(Det::The),
        "a" => Some(Det::A),
        "an" => Some(Det::An),
        "each" => Some(Det::Each),
        "every" => Some(Det::Every),
        "all" => Some(Det::All),
        "any" => Some(Det::Any),
        "no" => Some(Det::No),
        _ => None,
    };
    if let Some(det) = simple {
        return Some((det, pos + 1));
    }
    if word.eq_ignore_ascii_case("exactly") {
        let n = number_value(word_at(tokens, pos + 1)?)?;
        return Some((Det::Exactly { n }, pos + 2));
    }
    if word.eq_ignore_ascii_case("at") {
        let bound = word_at(tokens, pos + 1)?;
        let n = number_value(word_at(tokens, pos + 2)?)?;
        if bound.eq_ignore_ascii_case("least") {
            return Some((Det::AtLeast { n }, pos + 3));
        }
        if bound.eq_ignore_ascii_case("most") {
            return Some((Det::AtMost { n }, pos + 3));
        }
    }
    None
}

/// A quantifier opener (`at least` / `at most` / `exactly`) whose number token
/// is numeric but not countable — a decimal, or an integer beyond 64 bits.
/// Letting the words fall through to open-class collection would silently
/// erase the quantifier from the tree, so the phrase is an error instead.
fn broken_quantifier(tokens: &[Token], pos: usize) -> Option<ParseError> {
    let word = word_at(tokens, pos)?;
    let number_at = if word.eq_ignore_ascii_case("exactly") {
        pos + 1
    } else if word.eq_ignore_ascii_case("at")
        && (kw_at(tokens, pos + 1, "least") || kw_at(tokens, pos + 1, "most"))
    {
        pos + 2
    } else {
        return None;
    };
    let number = word_at(tokens, number_at)?;
    (is_number(number) && number_value(number).is_none()).then(|| ParseError::QuantifierNotWhole {
        word: number.to_string(),
    })
}

/// Parse a measure: a number (kept as written) with an optional unit word, or
/// a noun phrase standing for a value.
fn parse_measure(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    depth: usize,
) -> Result<(Measure, usize), ParseError> {
    if let Some((measure, next)) = parse_quantity(tokens, pos, ctx) {
        return Ok((measure, next));
    }
    let (np, next) = parse_np_group(tokens, pos, ctx, ParseError::EmptyPredicate, depth)?;
    Ok((Measure::Np { np: Box::new(np) }, next))
}

/// Parse a single-phrase measure: like [`parse_measure`], but the noun-phrase
/// form is one [`Np`], never a coordination. `between`'s lower bound uses
/// this so the comparison's own `and` stays visible.
fn parse_measure_single(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    depth: usize,
) -> Result<(Measure, usize), ParseError> {
    if let Some((measure, next)) = parse_quantity(tokens, pos, ctx) {
        return Ok((measure, next));
    }
    let (np, next) = parse_np(tokens, pos, ctx, ParseError::EmptyPredicate, depth)?;
    Ok((
        Measure::Np {
            np: Box::new(NpGroup::Single(np)),
        },
        next,
    ))
}

/// A BOUNDED quantity (round 6), admitted in the `for` (Duration) role:
/// `at least 30 days`, `at most 5 seconds`, `greater than 3 days`, `less
/// than 2 hours`, `between 5 and 10 seconds`. `None` when no bound opener
/// starts here (the caller falls through to the plain quantity);
/// `Some(Err(ForRequiresMeasure))` when a bound opener is not followed by a
/// usable number (`for at least the limit` — bounded noun-phrase measures
/// stay unsupported, like plain ones). `equal to` is NOT an opener
/// (legislated: `for 5 seconds` already says exactly that). For `between`,
/// a unit may be written after either number; two written units must agree
/// (case-insensitively) or the second is rejected as unexpected.
fn parse_bounded_quantity(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
) -> Option<Result<(Measure, usize), ParseError>> {
    let word = word_at(tokens, pos)?;
    let simple =
        |op: ComparisonOp, number_at: usize| -> Result<(Measure, usize), ParseError> {
            match parse_quantity(tokens, number_at, ctx) {
                Some((Measure::Quantity { number, unit }, next)) => Ok((
                    Measure::Bounded {
                        op,
                        number,
                        unit,
                        upper: None,
                    },
                    next,
                )),
                // Round 12 (change 4): a bound opener demands a number, so an
                // unknown number word there names itself (`for at least
                // eleventy days`); anything else keeps the round-6 rewrite
                // (`for at least the limit` stays ForRequiresMeasure).
                _ => Err(unknown_number_word_at(tokens, number_at)
                    .unwrap_or(ParseError::ForRequiresMeasure)),
            }
        };
    if word.eq_ignore_ascii_case("at") {
        if kw_at(tokens, pos + 1, "least") {
            return Some(simple(ComparisonOp::AtLeast, pos + 2));
        }
        if kw_at(tokens, pos + 1, "most") {
            return Some(simple(ComparisonOp::AtMost, pos + 2));
        }
        return None;
    }
    if word.eq_ignore_ascii_case("greater") && kw_at(tokens, pos + 1, "than") {
        return Some(simple(ComparisonOp::GreaterThan, pos + 2));
    }
    if word.eq_ignore_ascii_case("less") && kw_at(tokens, pos + 1, "than") {
        return Some(simple(ComparisonOp::LessThan, pos + 2));
    }
    if word.eq_ignore_ascii_case("between") {
        let between = || -> Result<(Measure, usize), ParseError> {
            // `and` is reserved, so the lower quantity's unit scan never
            // swallows the separator (`between 5 and 10 seconds`).
            let Some((
                Measure::Quantity {
                    number,
                    unit: lower_unit,
                },
                at,
            )) = parse_quantity(tokens, pos + 1, ctx)
            else {
                // Round 12 (change 4): an unknown number word in a bound
                // names itself; anything else keeps the round-6 rewrite.
                return Err(unknown_number_word_at(tokens, pos + 1)
                    .unwrap_or(ParseError::ForRequiresMeasure));
            };
            if !kw_at(tokens, at, "and") {
                return Err(unexpected(tokens, at));
            }
            let Some((
                Measure::Quantity {
                    number: upper,
                    unit: upper_unit,
                },
                next,
            )) = parse_quantity(tokens, at + 1, ctx)
            else {
                return Err(unknown_number_word_at(tokens, at + 1)
                    .unwrap_or(ParseError::ForRequiresMeasure));
            };
            let unit = match (lower_unit, upper_unit) {
                (Some(lower), Some(upper_u)) => {
                    if !lower.eq_ignore_ascii_case(&upper_u) {
                        // Two written units that disagree: the second one
                        // is the stray material.
                        return Err(unexpected(tokens, next - 1));
                    }
                    Some(lower)
                }
                (Some(unit), None) | (None, Some(unit)) => Some(unit),
                (None, None) => None,
            };
            // Round 9: a descending pair is a typo, not an empty interval.
            check_between_order(&number, &upper)?;
            Ok((
                Measure::Bounded {
                    op: ComparisonOp::Between,
                    number,
                    unit,
                    upper: Some(upper),
                },
                next,
            ))
        };
        return Some(between());
    }
    None
}

/// The numeric form of a measure: a number kept as written, with an optional
/// unit word.
fn parse_quantity(tokens: &[Token], pos: usize, ctx: NpCtx) -> Option<(Measure, usize)> {
    let word = word_at(tokens, pos)?;
    if !is_number(word) {
        return None;
    }
    let number = word.to_string();
    let unit = word_at(tokens, pos + 1)
        .filter(|w| {
            !(is_np_stop(w, ctx)
                || is_number(w)
                || (ctx.stops_locatives() && locative_at(tokens, pos + 1).is_some()))
        })
        .map(str::to_string);
    let next = if unit.is_some() { pos + 2 } else { pos + 1 };
    Some((Measure::Quantity { number, unit }, next))
}

/// Parse one noun phrase: `[det] modifiers head [of np] [relative]`.
/// `on_empty` is the error for a phrase with no head — the caller knows
/// whether that hole is a missing subject or stray material.
///
/// Relative attachment after an `of`-chain (round 5, legislated): a
/// `who`-relative attaches to the ROOT of the chain (`the user of the
/// workspace who is active` restricts the USER — `who` is animate, and the
/// chain root is the phrase's referent), while a `that`-relative attaches
/// to the NEAREST head (`the user of the workspace that is active`
/// restricts the WORKSPACE — the pre-round-5 behavior, kept). The rule is
/// deterministic marker-by-marker; there is no ambiguity to resolve at read
/// time.
fn parse_np(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    on_empty: ParseError,
    depth: usize,
) -> Result<(Np, usize), ParseError> {
    parse_np_at(tokens, pos, ctx, on_empty, depth, false)
}

/// The working recursion behind [`parse_np`]. `of_link` is true when this
/// noun phrase is an `of`-chain link rather than the chain root: a link
/// consumes a `that`-relative (nearest attachment) but LEAVES a
/// `who`-relative for the chain root to claim (root attachment) — the
/// parsing-order care the round-5 rule needs, since the chain is nested.
fn parse_np_at(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    on_empty: ParseError,
    depth: usize,
    of_link: bool,
) -> Result<(Np, usize), ParseError> {
    if depth >= MAX_NP_DEPTH {
        return Err(ParseError::PhraseTooDeep {
            limit: MAX_NP_DEPTH,
        });
    }
    let (det, mut at) = match parse_det(tokens, pos) {
        Some((det, next)) => (Some(det), next),
        None => {
            if let Some(error) = broken_quantifier(tokens, pos) {
                return Err(error);
            }
            // Round 12 (change 4): a quantifier opener whose "number" is
            // an unknown word fails closed instead of degrading into
            // open-class modifiers (`at least eleventy nodes`).
            if let Some(error) = unknown_quantifier_number(tokens, pos) {
                return Err(error);
            }
            (None, pos)
        }
    };
    let mut words: Vec<String> = Vec::new();
    while let Some(word) = word_at(tokens, at) {
        if is_np_stop(word, ctx) || (ctx.stops_locatives() && locative_at(tokens, at).is_some()) {
            break;
        }
        // Round 6 (supersedes the round-5 leave-alone): bare `with` is
        // closed in EVERY noun-phrase collection context, Plain included.
        // Folding it into the modifiers pinned `the file with the flag` to
        // head `flag` — accepted-but-wrong. The same ambiguity discipline
        // as at role positions applies; a backticked `` `with` `` stays an
        // ordinary word.
        if word.eq_ignore_ascii_case("with") {
            return Err(ParseError::WithIsAmbiguous);
        }
        words.push(word.to_string());
        at += 1;
    }
    let Some(head) = words.pop() else {
        return Err(on_empty);
    };
    let of = if kw_at(tokens, at, "of") {
        let (of_np, next) = parse_np_at(
            tokens,
            at + 1,
            ctx,
            unexpected(tokens, at + 1),
            depth + 1,
            true,
        )?;
        at = next;
        Some(Box::new(of_np))
    } else {
        None
    };
    let relative = match word_at(tokens, at) {
        // `that`: nearest attachment — any link takes it. `who`: root
        // attachment — an of-chain link leaves it for the root.
        Some(w)
            if w.eq_ignore_ascii_case("that") || (w.eq_ignore_ascii_case("who") && !of_link) =>
        {
            let marker = if w.eq_ignore_ascii_case("that") {
                RelMarker::That
            } else {
                RelMarker::Who
            };
            let (body, next) = parse_relative_body(tokens, at + 1, depth + 1)?;
            at = next;
            Some(Box::new(Relative { marker, body }))
        }
        _ => None,
    };
    Ok((
        Np {
            det,
            modifiers: words,
            head,
            of,
            relative,
        },
        at,
    ))
}

/// The body of a restrictive relative clause: its own copula and predicate
/// (round 8: with an optional passive agent and a thematic-role tail,
/// mirroring the copular clause body), or a verb with the full verbal tail.
/// It stops at the next pivot-level keyword, so keywords inside it never
/// end the enclosing subject.
fn parse_relative_body(
    tokens: &[Token],
    pos: usize,
    depth: usize,
) -> Result<(RelativeBody, usize), ParseError> {
    if let Some((copula, at)) = parse_clause_copula(tokens, pos) {
        // Capability in relative position (round 8, change 5): `able to`
        // exactly after the copula — BARE only, legislated: relatives have
        // no adverb slot. The verb phrase carries its own roles.
        if kw_at(tokens, at, "able") && kw_at(tokens, at + 1, "to") {
            let (vp, next) = parse_vp(tokens, at + 2, depth + 1)?;
            return Ok((
                RelativeBody::Copular {
                    copula,
                    predicate: Predicate::AbleTo { vp: Box::new(vp) },
                    agent: None,
                    roles: Vec::new(),
                },
                next,
            ));
        }
        // Round 8, change 4: the predicate stops where a thematic role
        // would open (verb-phrase stopping), then the round-5 passive
        // agent shape and the role tail follow. Roles attach to the
        // RELATIVE's predicate (innermost attachment, as for verbal
        // relatives); the tail stops where its roles stop.
        let (mut predicate, mut next) = parse_predicate(tokens, at, NpCtx::Vp, depth)?;
        resume_flat_able_predicate(tokens, &mut predicate, &mut next);
        let (agent, next) = parse_optional_agent(tokens, next)?;
        let (roles, next) = parse_roles(tokens, next, depth, true)?;
        return Ok((
            RelativeBody::Copular {
                copula,
                predicate,
                agent,
                roles,
            },
            next,
        ));
    }
    // Round 9: the OBJECT-GAP reading — `that the gateway forwards` — is
    // tried before the verbal tail whenever a determiner/quantifier-led
    // noun phrase opens here (a determiner can never open a verbal tail,
    // so the gap can only turn rejections into parses, never re-read an
    // accepted tree). A bare noun phrase after `that`/`who` deliberately
    // does NOT trigger the gap (LEGISLATED: `that holds locks` must keep
    // its round-7 verb + object reading, and no syntactic rule could tell
    // it from a gap's subject + verb).
    if let Some(result) = parse_object_gap(tokens, pos, depth) {
        return result;
    }
    // Round 7: the verbal body is the FULL shared verbal tail — verb,
    // particle, manner, object, roles — always in verb-phrase context, so
    // role and locative prepositions inside the relative are closed and
    // open the RELATIVE's own roles (innermost attachment, legislated:
    // `the session that holds the lock in the vault` locates the holding).
    // The tail stops where its roles stop; the caller places what follows.
    let (verb, particle, manner, object, roles, next) =
        parse_verbal_tail_parts(tokens, pos, depth)?;
    Ok((
        RelativeBody::Verbal {
            verb,
            particle,
            manner,
            object,
            roles,
        },
        next,
    ))
}

/// The object-gap relative reading (round 9): a determiner/quantifier-led
/// SUBJECT noun phrase, then the relative's verb with the shared tail
/// minus the object — the restricted head is the missing object. `None`
/// falls back to the existing readings and their diagnostics: when no
/// determiner opens here, when no subject split leaves a clean tail, or
/// when an EXPLICIT object (determiner/quantifier-led, group-marked, or
/// a bare number) follows any candidate verb — a saturated relative is
/// not a gap, and the round-6 `DeterminerAsVerb` diagnosis stands. The subject
/// split is the SHORTEST prefix that (a) spans at least the whole
/// determiner or quantifier, (b) parses exactly as a noun-phrase group
/// with a verb-position word after it, and (c) leaves NO object material
/// after that verb, its particle, and its manner run (deterministic; an
/// `of`-chain extends the prefix because its `of` is never
/// verb-position). Condition (c) — a round-9 attack fix — makes trailing
/// bare words EXTEND the subject instead of aborting the gap: `that the
/// backup daemon raises` is subject `the backup daemon` + verb `raises`,
/// not subject `the backup` + "verb" `daemon` + stray material.
/// LEGISLATED collision, the det-led mirror of the bare-NP rule above: a
/// det-led body ending in two open words — `that the session holds
/// locks` — reads as the longer subject (`the session holds`) with the
/// last word as the gap's verb. The grammar has no verb lexicon to
/// prefer the saturated `holds` + object `locks` reading, and unlike the
/// bare-NP case that reading never parsed here (a determiner cannot open
/// a verbal tail), so the gap only turns a rejection into a parse. Once
/// the split is found the gap is COMMITTED: errors in its role tail are
/// the sentence's errors, not a reason to fall back.
fn parse_object_gap(
    tokens: &[Token],
    pos: usize,
    depth: usize,
) -> Option<Result<(RelativeBody, usize), ParseError>> {
    // The subject spans at least the determiner/quantifier plus a head, so
    // the verb scan starts past the determiner: split candidates INSIDE a
    // multi-word quantifier (`at least 3` misread as head `at` + verb
    // `least`) were never legitimate (round-9 attack fix).
    let after_det = match parse_det(tokens, pos) {
        Some((_, next)) => next,
        None if broken_quantifier(tokens, pos).is_some() => pos + 1,
        None => return None,
    };
    // The shortest subject split whose next token can be a verb AND whose
    // tail after the verb is clean.
    let mut split = None;
    for k in after_det + 1..tokens.len() {
        let Some(word) = word_at(tokens, k).filter(|w| {
            !is_reserved(w) && !in_list(ROLE_PREPS, w) && parse_det(tokens, k).is_none()
        }) else {
            continue;
        };
        if locative_at(tokens, k).is_some() || manner_at(tokens, k).is_some() {
            continue;
        }
        let Ok(subject) = parse_np_group_exact(&tokens[pos..k], NpCtx::Plain, depth) else {
            continue;
        };
        let mut at = k + 1;
        let mut particle = particle_at(tokens, at).map(str::to_string);
        if particle.is_some() {
            at += 1;
        }
        let (mut manner, after_manner) = manner_run(tokens, at);
        at = after_manner;
        join_particle_after_manner(tokens, &mut at, &mut particle, &mut manner);
        // Object material after this candidate's verb decides the scan:
        // an EXPLICIT object — determiner/quantifier-led, a group marker,
        // or a bare number — means the relative is saturated and no gap
        // exists at any split (the round-6 diagnosis stands); a bare
        // non-numeric word merely means the split is wrong — a LONGER
        // subject may absorb it (`the backup daemon | raises`), so the
        // scan continues.
        if group_marker_at(tokens, at) {
            return None;
        }
        if word_at(tokens, at).is_some_and(|w| !is_np_stop(w, NpCtx::Vp))
            && locative_at(tokens, at).is_none()
        {
            if parse_det(tokens, at).is_some()
                || broken_quantifier(tokens, at).is_some()
                || word_at(tokens, at).is_some_and(is_number)
            {
                return None;
            }
            continue;
        }
        split = Some((subject, word.to_string(), particle, manner, at));
        break;
    }
    let (subject, verb, particle, manner, at) = split?;
    // Committed: the gap's role tail parses like any verbal tail's.
    Some(parse_roles(tokens, at, depth, false).map(|(roles, next)| {
        (
            RelativeBody::ObjectGap {
                subject,
                verb,
                particle,
                manner,
                roles,
            },
            next,
        )
    }))
}

/// The clause copulas: `is`, `are`, `remains`.
fn parse_clause_copula(tokens: &[Token], pos: usize) -> Option<(ClauseCopula, usize)> {
    let word = word_at(tokens, pos)?;
    let copula = match word.to_ascii_lowercase().as_str() {
        "is" => ClauseCopula::Is,
        "are" => ClauseCopula::Are,
        "remains" => ClauseCopula::Remains,
        _ => return None,
    };
    Some((copula, pos + 1))
}

/// Parse a noun phrase or a coordination: `[both|either] np { and|or np }`.
/// One conjunction throughout; `both` pairs with `and`, `either` with `or`,
/// each over exactly two items.
fn parse_np_group(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    on_empty: ParseError,
    depth: usize,
) -> Result<(NpGroup, usize), ParseError> {
    let (marker, mut at) = match word_at(tokens, pos) {
        Some(w) if w.eq_ignore_ascii_case("both") => (Some(GroupMarker::Both), pos + 1),
        Some(w) if w.eq_ignore_ascii_case("either") => (Some(GroupMarker::Either), pos + 1),
        _ => (None, pos),
    };
    let (first, next) = parse_np(tokens, at, ctx, on_empty, depth)?;
    at = next;
    let mut items = vec![first];
    let mut conj: Option<Conj> = None;
    loop {
        let this = match word_at(tokens, at) {
            Some(w) if w.eq_ignore_ascii_case("and") => Conj::And,
            Some(w) if w.eq_ignore_ascii_case("or") => Conj::Or,
            _ => break,
        };
        if conj.is_some_and(|c| c != this) {
            return Err(ParseError::MixedCoordination);
        }
        conj = Some(this);
        // `and or` / `or and` — two conjunctions in a row is a mixed group,
        // not merely a missing item.
        if word_at(tokens, at + 1)
            .is_some_and(|w| w.eq_ignore_ascii_case("and") || w.eq_ignore_ascii_case("or"))
        {
            return Err(ParseError::MixedCoordination);
        }
        let (np, next) = parse_np(tokens, at + 1, ctx, unexpected(tokens, at + 1), depth)?;
        items.push(np);
        at = next;
    }
    match (marker, conj) {
        (None, None) => match items.pop() {
            Some(single) => Ok((NpGroup::Single(single), at)),
            None => Err(unexpected(tokens, at)),
        },
        (marker, Some(conj)) => {
            let marker_ok = match marker {
                None => true,
                Some(GroupMarker::Both) => conj == Conj::And && items.len() == 2,
                Some(GroupMarker::Either) => conj == Conj::Or && items.len() == 2,
            };
            if !marker_ok {
                return Err(ParseError::MixedCoordination);
            }
            Ok((
                NpGroup::Coordinated {
                    conj,
                    marker,
                    items,
                },
                at,
            ))
        }
        (Some(_), None) => Err(ParseError::MixedCoordination),
    }
}

// ---- clauses --------------------------------------------------------------------

/// Parse a clause over a delimited slice, consuming all of it. The copular
/// reading is tried first: the split lands on the first `is`/`are`/`remains`
/// whose left side parses exactly as the subject, so a copula belonging to a
/// relative clause inside the subject (`the user who is authenticated is
/// active`) never ends the subject early. When that left side contains a
/// bare clausal role preposition (`before`/`after`/`until`), the verbal
/// reading is preferred wherever it parses, so a copula inside a clause
/// nested under such a role (`the pump runs until the tank is full`) keeps
/// its role instead of being swallowed into a flat subject noun phrase.
/// Otherwise the clause is verbal:
/// the verb sits immediately before the first determiner-led phrase (`the
/// temperature exceeds the limit`) or role-opening preposition (`the pump
/// runs at the depot`), or before a final bare number (`the counter reaches
/// zero`) or final particle (`the user logs out`); a boundary-less trailing
/// run of two or more bare words after the MINIMAL subject is the
/// AMBIGUOUS CLASS and is rejected fail-closed (`the client sends
/// telemetry` — [`ParseError::AmbiguousVerbBoundary`]; round 11,
/// [`svo_verb_at`]), and a one-word run keeps the final word as the
/// verb (`a session expires`). After the verb the body reads
/// like a verb phrase: optional particle, optional object, then thematic
/// roles.
fn parse_clause(tokens: &[Token], depth: usize) -> Result<Clause, ParseError> {
    // `before`/`after` roles nest clauses inside clauses; the shared depth
    // budget bounds that recursion the same way it bounds `of` chains.
    if depth >= MAX_NP_DEPTH {
        return Err(ParseError::PhraseTooDeep {
            limit: MAX_NP_DEPTH,
        });
    }
    let mut first_subject_err: Option<ParseError> = None;
    for i in (0..tokens.len()).filter(|&i| parse_clause_copula(tokens, i).is_some()) {
        if i == 0 {
            return Err(ParseError::EmptySubject);
        }
        let subject = match parse_np_group_exact(&tokens[..i], NpCtx::Plain, depth) {
            Ok(subject) => subject,
            Err(error) => {
                // This copula may belong to a relative clause inside the
                // subject; remember the error and try the next split.
                first_subject_err.get_or_insert(error);
                continue;
            }
        };
        // A clausal role preposition inside the would-be subject slice means
        // this copula may belong to a clause NESTED under a
        // `before`/`after`/`until` role (`the pump runs until the tank is
        // full`): role prepositions are open-class in plain noun phrases, so
        // the copular split would silently swallow the whole guard — verb,
        // preposition, and inner determiner — into one flat subject. Prefer
        // the verbal reading, which gives the preposition its role; fall
        // back to the copular split only when no verbal reading exists
        // (`the after image is ready` stays copular).
        if tokens[..i].iter().any(|t| {
            t.word()
                .is_some_and(|w| in_list(&["before", "after", "until"], w))
        }) {
            if let Ok(clause) = parse_verbal_clause(tokens, depth) {
                return Ok(clause);
            }
        }
        let Some((copula, at)) = parse_clause_copula(tokens, i) else {
            return Err(unexpected(tokens, i));
        };
        // Capability in clause position (round 8, change 5): `able to`
        // exactly after the copula — BARE only, legislated: clause bodies
        // have no adverb slot, so `is always able to` stays a description
        // form. The verb phrase carries its own roles.
        if kw_at(tokens, at, "able") && kw_at(tokens, at + 1, "to") {
            let (vp, next) = parse_vp(tokens, at + 2, depth + 1)?;
            if next < tokens.len() {
                return Err(unexpected(tokens, next));
            }
            return Ok(Clause {
                subject,
                body: ClauseBody::Copular {
                    copula,
                    predicate: Predicate::AbleTo { vp: Box::new(vp) },
                    agent: None,
                    roles: Vec::new(),
                },
            });
        }
        // Round 8, change 4: the predicate stops where a thematic role
        // would open (verb-phrase stopping), then the round-5 passive
        // agent shape (`is submitted by the user`), then the role tail —
        // `while the pump is active at the depot` carries a structured
        // Location role instead of flat predicate words. A `by` later in
        // the tail is the Agent role (a copular body is a passive site).
        let (mut predicate, mut next) = parse_predicate(tokens, at, NpCtx::Vp, depth)?;
        resume_flat_able_predicate(tokens, &mut predicate, &mut next);
        let (agent, next) = parse_optional_agent(tokens, next)?;
        let (roles, next) = parse_roles(tokens, next, depth, true)?;
        if next < tokens.len() {
            return Err(unexpected(tokens, next));
        }
        return Ok(Clause {
            subject,
            body: ClauseBody::Copular {
                copula,
                predicate,
                agent,
                roles,
            },
        });
    }
    if let Some(error) = first_subject_err {
        // A copula was present but no split yields a well-formed subject: the
        // copula may sit inside a copular relative of a verbal clause's
        // subject (`the user who is authenticated logs out`) — possibly one
        // nested under a `before`/`after` role (`the pump runs after the
        // user who is authenticated logs out`) — so try the verbal readings
        // before reporting the leftmost split's diagnosis. A depth-bound
        // error is NEVER replaced by that speculative diagnosis (round 9):
        // the bound is a resource fact about the input, not a reading that
        // lost to another.
        return parse_verbal_clause(tokens, depth).map_err(|e| match e {
            ParseError::PhraseTooDeep { .. } => e,
            _ => error,
        });
    }
    parse_verbal_clause(tokens, depth)
}

/// The verbal reading of a clause: two candidate splits, kept in agreement by
/// preferring the shorter subject.
///
/// - The **boundary heuristic** puts the verb just before the first
///   determiner, locative, or role-opening preposition (`the temperature
///   exceeds the limit`, `the pump runs at the depot`).
/// - The **noun-phrase-first** reading takes the shortest prefix that parses
///   as a subject with `of`-chain or relative structure (`the owner of the
///   file logs out`) — a shape the heuristic misreads (it would take `of`
///   for the verb).
///
/// When both readings succeed the shorter subject wins: `the payment clears
/// after the owner of the file approves` must keep its `After` role (the
/// heuristic's split at `clears`) rather than swallow the whole guard into
/// one flat subject noun phrase, while `the owner of files opens valves`
/// (no determiner anywhere after the subject) still belongs to the
/// noun-phrase-first reading. On a tie the two splits are the same split.
fn parse_verbal_clause(tokens: &[Token], depth: usize) -> Result<Clause, ParseError> {
    let boundary = boundary_verbal(tokens, depth);
    // Round 11 fail-closed follow-up: an ambiguity found by the boundary
    // reading is a fact about the input, not a reading that lost to
    // another — letting the noun-phrase-first fallback re-read the same
    // words (e.g. re-attaching a content `that`-clause as an object-gap
    // relative of a longer subject) would silently convert the legislated
    // rejection into exactly the accepted-but-wrong tree the rule exists
    // to forbid. `boundary_verbal` only reports the ambiguity when its
    // own reading is otherwise viable (its subject region parses), so a
    // shape whose boundary split never existed still reaches np-first.
    if matches!(boundary, Err(ParseError::AmbiguousVerbBoundary)) {
        return Err(ParseError::AmbiguousVerbBoundary);
    }
    let np_first = np_first_verbal(tokens, depth);
    match (boundary, np_first) {
        (Ok((clause, verb_at)), Some((np_clause, k))) => {
            Ok(if verb_at <= k { clause } else { np_clause })
        }
        (Ok((clause, _)), None) => Ok(clause),
        (Err(_), Some((clause, _))) => Ok(clause),
        (Err(error), None) => Err(error),
    }
}

/// The boundary-heuristic verbal reading of a clause: locate the position
/// just after the verb — the object's determiner (scanning past the
/// subject's own position-0 determiner) or the first role-opening
/// preposition. With neither, a final bare number is still an object (`the
/// counter reaches zero`) and a final particle joins the verb (`the user
/// logs out`); otherwise — round 11, superseding the round-10 SVO
/// acceptance and the round-3 final-word rule for runs of two or more —
/// the trailing bare-word run after the MINIMAL subject is the AMBIGUOUS
/// CLASS and fails closed ([`svo_verb_at`]): `the client sends telemetry`
/// is [`ParseError::AmbiguousVerbBoundary`], while a length-1 run keeps
/// the final word as the verb (`a session expires`). Returns the clause
/// with its verb position (the subject's length) for the caller's split
/// preference.
fn boundary_verbal(tokens: &[Token], depth: usize) -> Result<(Clause, usize), ParseError> {
    // `that` joined the boundary set in round 9: a content complement puts
    // the verb IMMEDIATELY before its `that` (`the monitor ensures that
    // …`), which no other boundary token would find. A `that` that is
    // really a subject relative makes this split fail (the one-word prefix
    // is no subject), and the noun-phrase-first reading — whose subject
    // carries the relative — wins in [`parse_verbal_clause`], exactly as
    // before.
    let boundary = (1..tokens.len()).find(|&i| {
        parse_det(tokens, i).is_some()
            || locative_at(tokens, i).is_some()
            || word_at(tokens, i).is_some_and(|w| in_list(ROLE_PREPS, w))
            || kw_at(tokens, i, "that")
    });
    let verb_at = match boundary {
        Some(j) => {
            // A marked coordination (`both the A and the B`) puts its marker
            // one position before the determiner the scan lands on; the
            // object group starts at the marker. Only when there is room for
            // a subject and a verb before it — a sentence-initial marker
            // belongs to the subject.
            let j = if j >= 3 && group_marker_at(tokens, j - 1) {
                j - 1
            } else {
                j
            };
            j.saturating_sub(1)
        }
        None => {
            // The final-word-verb rule never picks a manner adverb as the
            // verb: trailing `ly` words are stripped (they are re-consumed
            // as manner by [`parse_verbal_tail`]) while a subject token and
            // a verb candidate remain, and the nearest preceding word plays
            // by the old rules (`the export completes successfully` → verb
            // `completes`, manner `[successfully]`).
            let mut end = tokens.len();
            while end >= 3 && manner_at(tokens, end - 1).is_some() {
                end -= 1;
            }
            let last = end.saturating_sub(1);
            let final_object_or_particle = end >= 3
                && (word_at(tokens, last).is_some_and(|w| is_number(w) && !is_reserved(w))
                    || particle_at(tokens, last).is_some());
            if final_object_or_particle {
                // Round 11 fail-closed follow-up: popping the final
                // particle/number must not REOPEN the frontier. At the
                // two-word run the readings coincide (`the user logs
                // out`, `the counter reaches zero` — round 3/4,
                // unchanged), but when the run BEFORE the popped token is
                // itself in the ambiguous class (`the client sends
                // telemetry out`, `the counter reaches stage zero`) both
                // readings survive the pop, and the clause fails closed
                // exactly like its particle-less twin.
                if svo_verb_at(tokens, last).is_some() {
                    return Err(ParseError::AmbiguousVerbBoundary);
                }
                last - 1
            } else if svo_verb_at(tokens, end).is_some() {
                // ROUND 11 (LEGISLATED, FAIL-CLOSED — superseding the
                // round-10 SVO acceptance and, for this class, the round-3
                // final-word acceptance): a boundary-less trailing run of
                // two or more bare words after the MINIMAL subject admits
                // BOTH readings — minimal-subject SVO (`the client | sends
                // | telemetry`) and long-subject final-word (`the client
                // sends | telemetry`) — and no lexicon-free rule can pick
                // the intended one (`the backup daemon sends telemetry`
                // scrambled under SVO; `the client sends telemetry`
                // scrambled under final-word). Accepted-but-wrong is worse
                // than rejection, so the whole class fails closed with
                // rewrites. Class membership is decided by SHAPE (the run
                // length and a verb-capable first run word, see
                // [`svo_verb_at`]), never by attempting both parses: a
                // shape in the class is rejected even when one of the two
                // readings would not parse. Length-1 runs keep the
                // verb-only reading (`a session expires`) — the two
                // readings coincide there — and the particle and
                // bare-number checks above run FIRST, so `the user logs
                // out` and `the counter reaches zero` keep their round-3/4
                // readings.
                return Err(ParseError::AmbiguousVerbBoundary);
            } else {
                last
            }
        }
    };
    // The boundary scan lands after the object's opener; manner adverbs
    // between the verb and that opener belong to the manner slot (`completes
    // successfully before …`), and a particle between the verb and the
    // opener joins the verb (`shuts down the server`).
    let mut verb_at = verb_at;
    while verb_at >= 2 && manner_at(tokens, verb_at).is_some() {
        verb_at -= 1;
    }
    let verb_at = if verb_at >= 2 && particle_at(tokens, verb_at).is_some() {
        verb_at - 1
    } else {
        verb_at
    };
    let attempt = |verb_at: usize| -> Result<(Clause, usize), ParseError> {
        if verb_at == 0 {
            return Err(ParseError::EmptySubject);
        }
        let body = match parse_verbal_tail(tokens, verb_at, depth) {
            Ok(body) => body,
            // A NESTED ambiguity (a content `that`-clause whose own clause
            // is in the ambiguous class) only condemns THIS reading when
            // the reading otherwise exists — its subject region must
            // parse. `the request that the gateway forwards fails` puts
            // the boundary split's subject at the bare determiner `the`
            // (no reading), so the noun-phrase-first alternative (the
            // object-gap relative) rightfully proceeds; `the monitor
            // confirms that the client sends telemetry` has a well-formed
            // split (`the monitor | confirms | that …`), so the nested
            // rejection is FINAL ([`parse_verbal_clause`] keeps it).
            Err(ParseError::AmbiguousVerbBoundary) => {
                return match parse_np_group_exact(&tokens[..verb_at], NpCtx::Plain, depth) {
                    Ok(_) => Err(ParseError::AmbiguousVerbBoundary),
                    Err(subject_error) => Err(subject_error),
                };
            }
            Err(error) => return Err(error),
        };
        let subject = parse_np_group_exact(&tokens[..verb_at], NpCtx::Plain, depth)?;
        Ok((Clause { subject, body }, verb_at))
    };
    let primary = attempt(verb_at);
    if primary.is_ok() || boundary.is_some() {
        return primary;
    }
    // Back-off for the final-word-verb rule: stripping ALL trailing `ly`
    // words can strip the verb itself (`the peers reply` has nothing but
    // `the` left of the pivot). An `ly`-final word is a legitimate English
    // verb (`reply`, `apply`, `fly` under plural subjects), so when the
    // fully stripped reading fails, re-admit the trailing words one at a
    // time — innermost first, so the non-`ly` verb preference of the strip
    // is kept wherever it parses (`the peers reply quickly` keeps verb
    // `reply`, manner `[quickly]`) — and report the original diagnosis only
    // when no reading exists.
    // One shared attempt call site: the fallback chain lives in deep
    // recursion (nested `after`/`before` clauses), so it must not widen
    // the frame.
    let error = primary.unwrap_err();
    let mut end = tokens.len();
    while end >= 3 && manner_at(tokens, end - 1).is_some() {
        end -= 1;
    }
    let candidates: Vec<usize> = ((end + 1)..=tokens.len()).map(|e| e - 1).collect();
    for candidate in candidates {
        if let Ok(ok) = attempt(candidate) {
            return Ok(ok);
        }
    }
    Err(error)
}

/// The AMBIGUOUS-CLASS detector of a boundary-less clause (round 11,
/// repurposing the round-10 SVO verb position): the subject is the MINIMAL
/// noun phrase — the position-0 determiner (multi-token count determiners
/// included) plus one word, or a single bare word — and a run of TWO OR
/// MORE bare words after it admits both the minimal-subject SVO reading
/// and the long-subject final-word reading, so the caller REJECTS the
/// clause ([`ParseError::AmbiguousVerbBoundary`]) instead of legislating
/// either. `None` — the clause is NOT in the ambiguous class, keep the
/// final-word-verb reading — when the run is shorter than two, or when
/// the run's first word cannot be a verb (the SVO reading is not
/// admitted, so only one reading exists): a reserved word (`the owner of
/// files logs` keeps verb `logs`) or a particle (`when the power up
/// fails` keeps its round-3 reading — a particle word never opens an SVO
/// run). Pre-verbal MANNER adverbs (round 11 fail-closed follow-up) do
/// not close the frontier: an `ly` word is never the verb itself, but it
/// does not disambiguate the split either — `the client quickly sends
/// telemetry` still admits both readings — so the manner prefix is
/// SKIPPED and the run after it is measured (`quickly sends telemetry`
/// is ambiguous; a lone word after the manner prefix keeps the
/// final-word reading — only one candidate verb remains). `end` is the
/// (trailing-)manner-stripped length.
fn svo_verb_at(tokens: &[Token], end: usize) -> Option<usize> {
    let subject_end = match parse_det(tokens, 0) {
        Some((_, next)) => next + 1,
        None => 1,
    };
    let mut verb_at = subject_end;
    while verb_at < end && manner_at(tokens, verb_at).is_some() {
        verb_at += 1;
    }
    if end < verb_at + 2 {
        return None;
    }
    let verb = word_at(tokens, verb_at)?;
    if is_reserved(verb) || particle_at(tokens, verb_at).is_some() {
        return None;
    }
    Some(verb_at)
}

/// Parse a verbal clause body from its verb position to the end of the
/// slice: `verb [particle] [object] [role-pp…]` — the same shape a verb
/// phrase reads after its verb (minus the `be`-complement, which is the
/// copular reading's territory).
fn parse_verbal_tail(
    tokens: &[Token],
    verb_at: usize,
    depth: usize,
) -> Result<ClauseBody, ParseError> {
    let (verb, particle, manner, object, roles, next) =
        parse_verbal_tail_parts(tokens, verb_at, depth)?;
    // The CONTENT complement (round 9): a final `that <clause>` where a
    // relative cannot attach — after the verb (its particle/manner run
    // included) or after the roles. A `that` after a NOUN never reaches
    // here (the noun phrase claimed it as a relative during the object or
    // role parse). The clause consumes the rest of the slice, so content
    // is final; the depth increment shares the recognizer's one budget.
    // Clause bodies only — relative verbal tails stop where their roles
    // stop and stay content-free in v0.2 (legislated).
    if kw_at(tokens, next, "that") {
        let rest = &tokens[next + 1..];
        if rest.is_empty() {
            return Err(unexpected(tokens, next + 1));
        }
        let content = Some(Box::new(parse_clause(rest, depth + 1)?));
        return Ok(ClauseBody::Verbal {
            verb,
            particle,
            manner,
            object,
            roles,
            content,
        });
    }
    if next < tokens.len() {
        return Err(unexpected(tokens, next));
    }
    Ok(ClauseBody::Verbal {
        verb,
        particle,
        manner,
        object,
        roles,
        content: None,
    })
}

/// The SHARED verbal tail after a verb — `verb [particle] [manner…]
/// [object] [role-pp…]` — used by verbal clause bodies and (round 7) by
/// verbal relative bodies. Returns the parts with the next position: a
/// clause body demands the tail consume its whole slice
/// ([`parse_verbal_tail`]); a relative stops where the tail stops.
#[allow(clippy::type_complexity)]
fn parse_verbal_tail_parts(
    tokens: &[Token],
    verb_at: usize,
    depth: usize,
) -> Result<
    (
        String,
        Option<String>,
        Vec<String>,
        Option<NpGroup>,
        Vec<RolePp>,
        usize,
    ),
    ParseError,
> {
    if locative_at(tokens, verb_at).is_some() {
        return Err(unexpected(tokens, verb_at));
    }
    let Some(verb) = word_at(tokens, verb_at).filter(|w| !is_reserved(w)) else {
        return Err(unexpected(tokens, verb_at));
    };
    // A determiner can only open a noun phrase, never a behavior — the
    // round-6 verb-position rule, applied to EVERY verbal tail (round 7
    // attack fix): without it, an object-gap relative (`each request that
    // the gateway forwards`) silently parsed into a nonsense tree with
    // verb `the` and object head `forwards`. Object-gap relatives are not
    // supported; the precise rejection replaces the wrong reading.
    if parse_det(tokens, verb_at).is_some() {
        return Err(ParseError::DeterminerAsVerb {
            word: verb.to_string(),
        });
    }
    let verb = verb.to_string();
    let mut at = verb_at + 1;
    let mut particle = particle_at(tokens, at).map(str::to_string);
    if particle.is_some() {
        at += 1;
    }
    // The controlled manner slot, shared with verb phrases: bare `ly`
    // adverbs where the object or roles would start (`completes
    // successfully`).
    let (mut manner, after_manner) = manner_run(tokens, at);
    at = after_manner;
    join_particle_after_manner(tokens, &mut at, &mut particle, &mut manner);
    let mut object = None;
    if word_at(tokens, at).is_some_and(|w| !is_np_stop(w, NpCtx::Vp))
        && locative_at(tokens, at).is_none()
        || group_marker_at(tokens, at)
    {
        let (group, next) = parse_np_group(tokens, at, NpCtx::Vp, unexpected(tokens, at), depth)?;
        object = Some(group);
        at = next;
    }
    pop_object_particle(&mut object, &mut particle);
    // A verbal tail is active voice: no Agent role here — the passive
    // reading is the copular body's territory.
    let (roles, next) = parse_roles(tokens, at, depth, false)?;
    Ok((verb, particle, manner, object, roles, next))
}

/// A particle word reached across the manner run still joins the verb:
/// `shut gracefully down` is the particle verb `shut down` with manner
/// `gracefully` (canonical render `shut down gracefully`), not the verb
/// `shut` with a bare object `down`. Skipped when the verb already carries
/// a particle; manner words after the joined particle extend the run
/// (`shut gracefully down quickly`). Shared by verb phrases and verbal
/// clause bodies.
fn join_particle_after_manner(
    tokens: &[Token],
    at: &mut usize,
    particle: &mut Option<String>,
    manner: &mut Vec<String>,
) {
    if particle.is_some() || manner.is_empty() {
        return;
    }
    if let Some(word) = particle_at(tokens, *at) {
        *particle = Some(word.to_string());
        *at += 1;
        let (more, next) = manner_run(tokens, *at);
        manner.extend(more);
        *at = next;
    }
}

/// A particle word trailing the object belongs to the verb: `lift the beam
/// up` is the particle verb `lift up` applied to `the beam`, so both
/// spellings share one atom and one object head. The word was collected as
/// the final open-class word of the object — its head — so it is popped back
/// off. The pop is skipped when the verb already carries a particle, when
/// the noun phrase has `of`-chain or relative structure (`the power up of
/// the system` stays a noun phrase), or when no other noun material is left
/// to serve as head (`log the up`). In a coordination only the last item is
/// adjacent to the phrase end, so only its head can be a trailing particle
/// (`shut the power and the relay down`). Backticked tokens keep their
/// backticks and never match the particle list, and hyphenation (`the
/// warm-up`) keeps a noun spelled like a particle out of the pop.
fn pop_object_particle(object: &mut Option<NpGroup>, particle: &mut Option<String>) {
    if particle.is_some() {
        return;
    }
    let np = match object {
        Some(NpGroup::Single(np)) => np,
        Some(NpGroup::Coordinated { items, .. }) => match items.last_mut() {
            Some(np) => np,
            None => return,
        },
        None => return,
    };
    if np.of.is_some() || np.relative.is_some() || !in_list(PARTICLES, &np.head) {
        return;
    }
    let Some(new_head) = np.modifiers.pop() else {
        return;
    };
    *particle = Some(std::mem::replace(&mut np.head, new_head));
}

/// The greedy noun-phrase-first verbal reading of a clause: the shortest
/// prefix that parses exactly as a noun-phrase group carrying `of`-chain or
/// relative structure, followed by `verb [particle] [object] [role-pp…]`
/// consuming the rest. `None` when no such reading exists. Returns the
/// clause with its verb position (the subject's length) so
/// [`parse_verbal_clause`] can prefer the shorter subject.
fn np_first_verbal(tokens: &[Token], depth: usize) -> Option<(Clause, usize)> {
    for k in 1..tokens.len() {
        let Ok(subject) = parse_np_group_exact(&tokens[..k], NpCtx::Plain, depth) else {
            continue;
        };
        if !np_group_has_structure(&subject) {
            continue;
        }
        // The verb: an open-class word — never a reserved word, a locative
        // (which opens a role, not a verb), a determiner opener, or a
        // manner adverb (an `ly` word is never the verb).
        if locative_at(tokens, k).is_some()
            || parse_det(tokens, k).is_some()
            || manner_at(tokens, k).is_some()
        {
            continue;
        }
        let Ok(body) = parse_verbal_tail(tokens, k, depth) else {
            continue;
        };
        return Some((Clause { subject, body }, k));
    }
    None
}

/// Whether a noun phrase carries `of`-chain or relative structure.
fn np_has_structure(np: &Np) -> bool {
    np.of.is_some() || np.relative.is_some()
}

fn np_group_has_structure(group: &NpGroup) -> bool {
    match group {
        NpGroup::Single(np) => np_has_structure(np),
        NpGroup::Coordinated { items, .. } => items.iter().any(np_has_structure),
    }
}

/// Parse the clause group of one frame: one clause, or clauses coordinated
/// under a single conjunction (`and` = joint guard, `or` = alternative
/// guard) — one frame either way. The coordinated reading is tried first:
/// the shortest prefix ending at a conjunction that parses as a complete
/// clause opens a split, and the remainder is read the same way. Where no
/// prefix is a complete clause the group is one clause, so noun-phrase
/// coordination inside a subject (`the pump and the valve are open`) stays a
/// single clause with a coordinated subject. All conjunctions in one frame
/// must match; mixing is [`ParseError::MixedCoordination`].
fn parse_clause_group(tokens: &[Token], depth: usize) -> Result<ClauseGroup, ParseError> {
    if let Some(result) = parse_coordinated_clauses(tokens, depth) {
        return result;
    }
    Ok(ClauseGroup::single(parse_clause(tokens, depth)?))
}

/// The coordinated reading of a frame slice, if one exists. `None` means no
/// coordinated reading (the caller falls back to the single-clause reading
/// and its diagnosis); `Some(Err(MixedCoordination))` means a coordinated
/// reading exists but mixes `and` with `or`.
///
/// The split backtracks: each conjunction whose prefix parses as a clause is
/// tried in order, and a split is kept only if the remainder itself reads as
/// clauses under the same conjunction. So `the order ships the report and the
/// invoice and the payment clears` skips the first `and` (its remainder is no
/// clause sequence) and splits at the second, keeping the coordinated object
/// inside the first clause.
fn parse_coordinated_clauses(
    tokens: &[Token],
    depth: usize,
) -> Option<Result<ClauseGroup, ParseError>> {
    for i in 1..tokens.len() {
        let Some(conj) = conj_at(tokens, i) else {
            continue;
        };
        let Ok(first) = parse_clause(&tokens[..i], depth) else {
            continue;
        };
        match coordinated_tail(&tokens[i + 1..], depth, conj) {
            Some(Ok(tail)) => {
                let mut items = vec![first];
                items.extend(tail);
                return Some(Ok(ClauseGroup {
                    conj: Some(conj),
                    items,
                }));
            }
            Some(Err(error)) => return Some(Err(error)),
            // The remainder is not a clause sequence: try a later split.
            None => continue,
        }
    }
    None
}

/// The rest of a coordinated clause group: one clause consuming the whole
/// slice, or a clause up to a conjunction followed (recursively) by more.
/// `None` when no such reading exists at any split point;
/// `Some(Err(MixedCoordination))` when a split is found under the wrong
/// conjunction.
fn coordinated_tail(
    tokens: &[Token],
    depth: usize,
    conj: Conj,
) -> Option<Result<Vec<Clause>, ParseError>> {
    for i in 1..tokens.len() {
        let Some(this) = conj_at(tokens, i) else {
            continue;
        };
        let Ok(clause) = parse_clause(&tokens[..i], depth) else {
            continue;
        };
        if this != conj {
            return Some(Err(ParseError::MixedCoordination));
        }
        match coordinated_tail(&tokens[i + 1..], depth, conj) {
            Some(Ok(tail)) => {
                let mut items = vec![clause];
                items.extend(tail);
                return Some(Ok(items));
            }
            Some(Err(error)) => return Some(Err(error)),
            None => continue,
        }
    }
    match parse_clause(tokens, depth) {
        Ok(last) => Some(Ok(vec![last])),
        Err(_) => None,
    }
}

/// The conjunction at `pos`, if any.
fn conj_at(tokens: &[Token], pos: usize) -> Option<Conj> {
    match word_at(tokens, pos) {
        Some(w) if w.eq_ignore_ascii_case("and") => Some(Conj::And),
        Some(w) if w.eq_ignore_ascii_case("or") => Some(Conj::Or),
        _ => None,
    }
}

/// Parse a noun-phrase group that must consume its whole slice.
///
/// MEMOIZED (round-9 attack fix): exact-prefix parsing is the one place
/// the recognizer backtracks over the same material — the object-gap
/// subject scan and the clause copular-split scan both re-parse nested
/// prefixes at every split point, and with object-gap relatives nesting
/// inside those prefixes the naive recursion is exponential (a ~60-token
/// nest of `the nodeN that … monitors` effectively hung the parser, the
/// depth bound unreachable). Identical sub-spans recur across split
/// points, so a per-sentence packrat table keyed by the span's identity
/// (all slices borrow one token buffer, so the pointer plus length IS
/// the span), the collection context, and the depth budget makes the
/// scan polynomial. The table is thread-local, lives exactly as long as
/// one sentence's parse ([`MemoScope`] — a freed buffer's address could
/// otherwise be reused by a later buffer), and is capped as a memory
/// backstop; semantics are untouched — the parser stays a pure function
/// of its input.
fn parse_np_group_exact(tokens: &[Token], ctx: NpCtx, depth: usize) -> Result<NpGroup, ParseError> {
    let key = (tokens.as_ptr() as usize, tokens.len(), ctx, depth);
    let hit = NP_EXACT_MEMO.with(|memo| {
        memo.borrow()
            .as_ref()
            .and_then(|table| table.get(&key).cloned())
    });
    if let Some(hit) = hit {
        return hit;
    }
    let result = (|| {
        let (group, next) = parse_np_group(tokens, 0, ctx, ParseError::EmptySubject, depth)?;
        if next < tokens.len() {
            return Err(unexpected(tokens, next));
        }
        Ok(group)
    })();
    NP_EXACT_MEMO.with(|memo| {
        if let Some(table) = memo.borrow_mut().as_mut() {
            if table.len() < NP_EXACT_MEMO_CAP {
                table.insert(key, result.clone());
            }
        }
    });
    result
}

/// The exact-prefix packrat table: see [`parse_np_group_exact`]. `None`
/// means no [`MemoScope`] is live — sub-parsers invoked outside
/// [`parse_sentence`] (unit tests) run uncached, so a key can never
/// outlive the token buffer whose address it names.
type NpExactKey = (usize, usize, NpCtx, usize);
type NpExactTable = std::collections::HashMap<NpExactKey, Result<NpGroup, ParseError>>;
thread_local! {
    static NP_EXACT_MEMO: std::cell::RefCell<Option<NpExactTable>> =
        const { std::cell::RefCell::new(None) };
}
/// Entry cap for the packrat table — a memory backstop, never reached by
/// human-written sentences; beyond it the parser just stops caching.
const NP_EXACT_MEMO_CAP: usize = 1 << 16;

/// Arms the packrat table for exactly one sentence's parse: fresh on
/// creation, dropped (disarmed and freed) with the sentence's stack
/// frame, so entries never survive the token buffer they describe.
struct MemoScope;

impl MemoScope {
    fn arm() -> MemoScope {
        NP_EXACT_MEMO.with(|memo| *memo.borrow_mut() = Some(NpExactTable::new()));
        MemoScope
    }
}

impl Drop for MemoScope {
    fn drop(&mut self) {
        NP_EXACT_MEMO.with(|memo| *memo.borrow_mut() = None);
    }
}

// ---- verb phrases -----------------------------------------------------------------

/// Parse a verb phrase starting at `pos`. Consumes as much as it can; the
/// caller decides what any leftover means.
fn parse_vp(tokens: &[Token], pos: usize, depth: usize) -> Result<(Vp, usize), ParseError> {
    let Some(verb) = word_at(tokens, pos) else {
        return Err(ParseError::EmptyVp);
    };
    if in_list(FRAME_KEYWORDS, verb) {
        return Err(ParseError::MidSentenceFrame {
            keyword: verb.to_string(),
        });
    }
    if is_reserved(verb) {
        return Err(unexpected(tokens, pos));
    }
    // A determiner can only open a noun phrase, never a behavior (round 6
    // follow-up): without this, `shall the valve` — and a determiner-led
    // TAIL of an `either … or …` alternative — accepted the determiner as
    // an open-class verb, freezing an accepted-but-wrong tree.
    if parse_det(tokens, pos).is_some() {
        return Err(ParseError::DeterminerAsVerb {
            word: verb.to_string(),
        });
    }
    let verb = verb.to_string();
    let mut at = pos + 1;
    let mut particle = None;
    let mut manner: Vec<String> = Vec::new();
    let mut complement = None;
    let mut object = None;
    if verb.eq_ignore_ascii_case("be") {
        // A complement predicate, unless a role phrase follows immediately.
        // `be` takes no particle: its complement path claims the word
        // (`shall be off` is the state `off`, not a particle verb).
        if !word_at(tokens, at).is_some_and(|w| in_list(ROLE_PREPS, w)) {
            let (predicate, next) = parse_predicate(tokens, at, NpCtx::Vp, depth)?;
            complement = Some(predicate);
            at = next;
        }
    } else {
        if let Some(p) = particle_at(tokens, at) {
            particle = Some(p.to_string());
            at += 1;
        }
        // The controlled manner slot: bare `ly` adverbs where the object or
        // roles would start (`stop immediately within 5 seconds`).
        let (run, after_manner) = manner_run(tokens, at);
        manner = run;
        at = after_manner;
        join_particle_after_manner(tokens, &mut at, &mut particle, &mut manner);
        if word_at(tokens, at).is_some_and(|w| !is_np_stop(w, NpCtx::Vp))
            && locative_at(tokens, at).is_none()
            || group_marker_at(tokens, at)
        {
            let (group, next) =
                parse_np_group(tokens, at, NpCtx::Vp, unexpected(tokens, at), depth)?;
            object = Some(group);
            at = next;
        }
        pop_object_particle(&mut object, &mut particle);
    }
    // `be <predicate>` is the passive site: only there may `by <np>` open
    // the Agent role (`shall be logged by the daemon`). A bare `be` with no
    // complement has nothing passive in it, so a locative `be by the dock`
    // is not misread as an agent — it is [`ParseError::ByOutsidePassive`]
    // like any other active `by`.
    let (roles, mut next) = parse_roles(
        tokens,
        at,
        depth,
        verb.eq_ignore_ascii_case("be") && complement.is_some(),
    )?;
    // The CONTENT complement (round 7): `that <clause>` where a relative
    // cannot attach — directly after the verb (its particle/manner run
    // included) or after the roles; the clause consumes the rest of the
    // phrase, so content is final and roles must precede it. A `that`
    // directly after a NOUN never reaches here: the noun phrase claims it
    // as a restrictive relative first (legislated — the relative wins
    // after a head). Uniform across every verb-phrase position
    // (legislated: `be`-complement phrases and `either … or …` alternative
    // items included — the slot sits after the shared role tail, so
    // excluding them would cost a rule, not save one). Verbal clause
    // bodies (frames) carry the same final slot since round 9 (see
    // [`parse_verbal_clause`]); only RELATIVE verbal tails stay
    // content-free in v0.2.
    let content = if kw_at(tokens, next, "that") {
        let rest = &tokens[next + 1..];
        if rest.is_empty() {
            return Err(unexpected(tokens, next + 1));
        }
        let clause = parse_clause(rest, depth + 1)?;
        next = tokens.len();
        Some(Box::new(clause))
    } else {
        None
    };
    Ok((
        Vp {
            verb,
            particle,
            manner,
            object,
            roles,
            complement,
            content,
        },
        next,
    ))
}

/// Parse the thematic-role phrases available after a verb (or a definiens
/// noun phrase). Order is free; duplicates keep surface order. `agent_ok`
/// is true only in a passive site — a `be` verb phrase with a complement —
/// where `by <np>` opens the Agent role; everywhere else a role-position `by` is
/// [`ParseError::ByOutsidePassive`], and `with` is always
/// [`ParseError::WithIsAmbiguous`] (round 5).
fn parse_roles(
    tokens: &[Token],
    pos: usize,
    depth: usize,
    agent_ok: bool,
) -> Result<(Vec<RolePp>, usize), ParseError> {
    let mut roles = Vec::new();
    let mut at = pos;
    loop {
        // A locative preposition opens a Location role; `at least`/`at most`
        // never reach here (they are filtered out as the comparison path).
        if let Some(preposition) = locative_at(tokens, at).map(str::to_string) {
            let (np, next) =
                parse_np_group(tokens, at + 1, NpCtx::Vp, unexpected(tokens, at + 1), depth)?;
            roles.push(RolePp::Location { preposition, np });
            at = next;
            continue;
        }
        let Some(prep) = word_at(tokens, at).filter(|w| in_list(ROLE_PREPS, w)) else {
            break;
        };
        let np_role = |ctor: fn(NpGroup) -> RolePp| -> Result<(RolePp, usize), ParseError> {
            let (np, next) =
                parse_np_group(tokens, at + 1, NpCtx::Vp, unexpected(tokens, at + 1), depth)?;
            Ok((ctor(np), next))
        };
        let (role, next) = match prep.to_ascii_lowercase().as_str() {
            "to" => np_role(RolePp::Recipient)?,
            "about" => np_role(RolePp::Topic)?,
            "from" => np_role(RolePp::Source)?,
            "into" => np_role(RolePp::Goal)?,
            "via" | "using" => {
                let marker = if prep.eq_ignore_ascii_case("via") {
                    MeansMarker::Via
                } else {
                    MeansMarker::Using
                };
                let (np, next) =
                    parse_np_group(tokens, at + 1, NpCtx::Vp, unexpected(tokens, at + 1), depth)?;
                (RolePp::Means { marker, np }, next)
            }
            "within" => {
                // A bound opener after `within` is rejected (round 6
                // follow-up, legislated): it used to be silently consumed
                // as a counted noun-phrase measure (`at least 5` of
                // `seconds`) that never grounds an interval. Bounds belong
                // to `for` durations; a deadline is already an upper bound.
                if parse_bounded_quantity(tokens, at + 1, NpCtx::Vp).is_some() {
                    return Err(ParseError::WithinTakesPlainMeasure);
                }
                // Round 12 (change 4): an unknown number word after
                // `within` fails closed instead of degrading into a
                // noun-phrase measure that never grounds an interval
                // (`within eleventy seconds`). Determiner-led measures
                // (`within the timeout`) are untouched — the carve-out on
                // [`unknown_number_word_at`].
                if let Some(error) = unknown_number_word_at(tokens, at + 1) {
                    return Err(error);
                }
                let (measure, next) = parse_measure(tokens, at + 1, NpCtx::Vp, depth)?;
                (RolePp::Deadline(measure), next)
            }
            // A duration REQUIRES a quantity (round 5, legislated):
            // `for 5 seconds` is a duration; `listen for requests` used to
            // be silently misread as a duration over a noun phrase, so a
            // non-quantity `for` is now a rejection with rewrites. Round 6:
            // the quantity may be BOUNDED — `for at least 30 days`, `for
            // between 5 and 10 seconds` (Duration only; `within` already
            // means an upper bound and keeps its plain quantity).
            "for" => {
                if let Some(result) = parse_bounded_quantity(tokens, at + 1, NpCtx::Vp) {
                    let (measure, next) = result?;
                    (RolePp::Duration(measure), next)
                } else if let Some((measure, next)) = parse_quantity(tokens, at + 1, NpCtx::Vp) {
                    (RolePp::Duration(measure), next)
                } else {
                    return Err(ParseError::ForRequiresMeasure);
                }
            }
            // Instrument vs accompaniment has no single reading: rejected,
            // with `using`/coordination as the rewrites (round 5).
            "with" => return Err(ParseError::WithIsAmbiguous),
            // The passive agent — only in a passive site.
            "by" => {
                if !agent_ok {
                    return Err(ParseError::ByOutsidePassive);
                }
                np_role(RolePp::Agent)?
            }
            "per" => match word_at(tokens, at + 1).filter(|w| !is_np_stop(w, NpCtx::Vp)) {
                Some(unit) => (
                    RolePp::Rate {
                        unit: unit.to_string(),
                    },
                    at + 2,
                ),
                None => return Err(unexpected(tokens, at + 1)),
            },
            "before" | "after" | "until" => {
                // The clause runs to the end of the phrase material: a
                // temporal boundary reads to the end of its sentence part —
                // but never across a deontic modal (round 7 attack fix): a
                // modal is a reserved word that can never be clause
                // material, and inside a SUBJECT relative the enclosing
                // sentence's own pivot follows the role clause (`each
                // packet that arrives before the window closes shall be
                // inspected`), so the first modal ends the clause slice.
                // Verbal clause bodies carry roles of their own, so
                // `before`/`after`/`until` can nest through clauses; the
                // depth increment keeps that recursion under
                // [`MAX_NP_DEPTH`].
                let end = (at + 1..tokens.len())
                    .find(|&i| {
                        word_at(tokens, i)
                            .is_some_and(|w| in_list(&["shall", "must", "should", "may"], w))
                    })
                    .unwrap_or(tokens.len());
                let clause = parse_clause(&tokens[at + 1..end], depth + 1)?;
                let clause = Box::new(clause);
                let role = if prep.eq_ignore_ascii_case("before") {
                    RolePp::Before(clause)
                } else if prep.eq_ignore_ascii_case("after") {
                    RolePp::After(clause)
                } else {
                    RolePp::Until(clause)
                };
                (role, end)
            }
            _ => return Err(unexpected(tokens, at)),
        };
        roles.push(role);
        at = next;
    }
    Ok((roles, at))
}

// ---- predicates ---------------------------------------------------------------

/// The prepositions that open a `Predicate::Pp`. `at` is claimed by the
/// comparison `at least`/`at most` first.
const PREDICATE_PREPS: &[&str] = &["in", "on", "at", "below", "above", "under", "over"];

/// Parse a predicate: a comparison, a prepositional predicate, or open-class
/// words up to the next stop.
fn parse_predicate(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    depth: usize,
) -> Result<(Predicate, usize), ParseError> {
    if let Some((comparison, next)) = parse_comparison(tokens, pos, ctx, depth)? {
        return Ok((Predicate::Comparison(comparison), next));
    }
    if let Some(word) = word_at(tokens, pos) {
        if in_list(PREDICATE_PREPS, word) {
            // A preposition with nothing after it is an empty predicate, not
            // stray material.
            let (np, next) =
                parse_np_group(tokens, pos + 1, ctx, ParseError::EmptyPredicate, depth)?;
            return Ok((
                Predicate::Pp {
                    preposition: word.to_string(),
                    np,
                },
                next,
            ));
        }
    }
    let mut words: Vec<String> = Vec::new();
    let mut at = pos;
    while let Some(word) = word_at(tokens, at) {
        // `by` ends predicate collection in EVERY context (round 5): a
        // description's or copular clause's predicate may be followed by
        // its passive agent, and the agent must never be swallowed into
        // the predicate words.
        if is_np_stop(word, ctx)
            || (ctx.stops_locatives() && locative_at(tokens, at).is_some())
            || word.eq_ignore_ascii_case("by")
        {
            break;
        }
        words.push(word.to_string());
        at += 1;
    }
    if words.is_empty() {
        return Err(ParseError::EmptyPredicate);
    }
    Ok((Predicate::Words { words }, at))
}

/// Round-8 legislation (change 5): in copular CLAUSE and RELATIVE bodies,
/// `able to` is capability only BARE — exactly after the copula. With an
/// adverb (`while the client is always able to retry`) the words stay
/// ORDINARY PREDICATE MATERIAL, never a capability. Verb-phrase collection
/// stops at `to` (a role preposition), which would hand the capability's
/// `to <verb>` tail to the role grammar as a Recipient over a verb — an
/// accepted-but-wrong tree — so when collection stopped with `able` before
/// `to`, it resumes in the description-predicate context (role and
/// locative prepositions open again; `by` still ends collection): the
/// whole tail stays flat words, exactly as the legislation reads.
fn resume_flat_able_predicate(tokens: &[Token], predicate: &mut Predicate, at: &mut usize) {
    let Predicate::Words { words } = predicate else {
        return;
    };
    if !words.last().is_some_and(|w| w.eq_ignore_ascii_case("able")) || !kw_at(tokens, *at, "to") {
        return;
    }
    while let Some(word) = word_at(tokens, *at) {
        if is_np_stop(word, NpCtx::Predicate) || word.eq_ignore_ascii_case("by") {
            break;
        }
        words.push(word.to_string());
        *at += 1;
    }
}

/// Parse a comparison if one starts here; `Ok(None)` when the tokens do not
/// open one (so the caller can fall through to the other predicate forms).
fn parse_comparison(
    tokens: &[Token],
    pos: usize,
    ctx: NpCtx,
    depth: usize,
) -> Result<Option<(Comparison, usize)>, ParseError> {
    let Some(word) = word_at(tokens, pos) else {
        return Ok(None);
    };
    let simple = |op: ComparisonOp, measure_pos: usize| -> Result<_, ParseError> {
        let (value, next) = parse_measure(tokens, measure_pos, ctx, depth)?;
        Ok(Some((
            Comparison {
                op,
                value,
                upper: None,
            },
            next,
        )))
    };
    if (word.eq_ignore_ascii_case("greater") || word.eq_ignore_ascii_case("less"))
        && kw_at(tokens, pos + 1, "than")
    {
        let op = if word.eq_ignore_ascii_case("greater") {
            ComparisonOp::GreaterThan
        } else {
            ComparisonOp::LessThan
        };
        return simple(op, pos + 2);
    }
    if word.eq_ignore_ascii_case("at") {
        if kw_at(tokens, pos + 1, "least") {
            return simple(ComparisonOp::AtLeast, pos + 2);
        }
        if kw_at(tokens, pos + 1, "most") {
            return simple(ComparisonOp::AtMost, pos + 2);
        }
        return Ok(None); // plain `at` — a prepositional predicate
    }
    if word.eq_ignore_ascii_case("equal") && kw_at(tokens, pos + 1, "to") {
        return simple(ComparisonOp::EqualTo, pos + 2);
    }
    if word.eq_ignore_ascii_case("between") {
        // The lower bound is a single measure: a coordinated noun phrase here
        // would swallow the comparison's own `and`.
        let (value, at) = parse_measure_single(tokens, pos + 1, ctx, depth)?;
        if !kw_at(tokens, at, "and") {
            return Err(unexpected(tokens, at));
        }
        let (upper, next) = parse_measure(tokens, at + 1, ctx, depth)?;
        // Round 9: a descending numeric pair is a typo, not an empty
        // interval; noun-phrase bounds are value names and stay unchecked.
        if let (Measure::Quantity { number: lo, .. }, Measure::Quantity { number: hi, .. }) =
            (&value, &upper)
        {
            check_between_order(lo, hi)?;
        }
        return Ok(Some((
            Comparison {
                op: ComparisonOp::Between,
                value,
                upper: Some(upper),
            },
            next,
        )));
    }
    Ok(None)
}

// ---- the core ---------------------------------------------------------------------

/// Parse the speech-act core over a delimited slice, consuming all of it.
/// The subject noun phrase is parsed left-to-right and stops at the first
/// top-level pivot; what that pivot is decides the core's kind.
fn parse_core(tokens: &[Token]) -> Result<Core, ParseError> {
    if tokens.is_empty() {
        return Err(ParseError::MissingPivot);
    }
    if word_at(tokens, 0).is_some_and(|w| in_list(PIVOTS, w) || in_list(UNSUPPORTED_MODALS, w)) {
        return Err(ParseError::EmptySubject);
    }
    // A leading `unless` is not a missing subject: the exception trails the
    // core, and the diagnosis should say so.
    if kw_at(tokens, 0, "unless") {
        return Err(ParseError::LeadingException);
    }
    let (subject, at) = parse_np_group(tokens, 0, NpCtx::Plain, ParseError::EmptySubject, 0)?;
    let Some(pivot) = word_at(tokens, at) else {
        return Err(ParseError::MissingPivot);
    };
    match pivot.to_ascii_lowercase().as_str() {
        "shall" | "must" | "should" | "may" => parse_deontic(tokens, at, subject),
        "is" | "are" => parse_description(tokens, at, subject),
        "means" => parse_definition(tokens, at, subject),
        w if in_list(UNSUPPORTED_MODALS, w) => Err(ParseError::UnsupportedModal {
            word: pivot.to_string(),
        }),
        w if in_list(FRAME_KEYWORDS, w) => Err(ParseError::MidSentenceFrame {
            keyword: pivot.to_string(),
        }),
        _ => Err(unexpected(tokens, at)),
    }
}

/// `<subject> shall/must/should [not] <vp>` / `<subject> may <vp>`.
fn parse_deontic(tokens: &[Token], at: usize, subject: NpGroup) -> Result<Core, ParseError> {
    let modal = match word_at(tokens, at).map(str::to_ascii_lowercase).as_deref() {
        Some("shall") => Modal::Shall,
        Some("must") => Modal::Must,
        Some("should") => Modal::Should,
        _ => Modal::May,
    };
    // A `no` subject under `may` is a denial of permission — a prohibition in
    // permission's clothing (`No client may retry.`). Like `may not`, the
    // grammar legislates the ambiguity away: write `shall not`. Any item of a
    // coordinated subject with `no` triggers it.
    if modal == Modal::May && subject.has_no_item() {
        return Err(ParseError::NoWithMay);
    }
    let mut pos = at + 1;
    let negated = kw_at(tokens, pos, "not");
    if negated {
        if modal == Modal::May {
            return Err(ParseError::AmbiguousModal);
        }
        pos += 1;
    }
    // VP alternatives (round 6): `either <vp> or <vp> [or <vp>]…` directly
    // after the modal. Deterministic lookahead, pinned both ways: `either`
    // followed by a word in VERB position (anything but a determiner)
    // opens the alternatives; followed by a determiner it stays the NP
    // group marker, which the verb position then rejects as before (a
    // noun-phrase group is no verb phrase).
    if kw_at(tokens, pos, "either")
        && word_at(tokens, pos + 1).is_some()
        && parse_det(tokens, pos + 1).is_none()
    {
        if negated {
            // Legislated: no De Morgan at ingest — write two prohibitions.
            return Err(ParseError::NegatedAlternatives);
        }
        let items = parse_vp_alternatives(&tokens[pos + 1..])?;
        return Ok(Core::Deontic {
            subject,
            modal,
            negated,
            vp: VpGroup::Alternatives { items },
        });
    }
    let (vp, next) = parse_vp(tokens, pos, 0)?;
    expect_core_end(tokens, next)?;
    Ok(Core::Deontic {
        subject,
        modal,
        negated,
        vp: VpGroup::Single(vp),
    })
}

/// The verb phrases of an `either … or …` alternation (round 6): the slice
/// after `either`, split at top-level `or` tokens into TWO OR MORE full
/// verb phrases, each consuming its whole segment. The split backtracks
/// exactly like coordinated clause groups: every `or` whose prefix parses
/// as a complete verb phrase is tried, and kept only when the remainder
/// itself reads as more alternatives — so an `or` inside an item's own
/// noun-phrase coordination (`accept either the copy or the original or
/// reject the request`) stays inside the item. `be <predicate>` is a valid
/// item (legislated); `and`-coordination of verb phrases stays unsupported
/// (two sentences already mean both-required).
fn parse_vp_alternatives(tokens: &[Token]) -> Result<Vec<Vp>, ParseError> {
    // The first `or` whose prefix IS a complete verb phrase but whose
    // remainder is not more alternatives: the honest diagnosis lives in
    // that remainder (round 6 follow-up — `either notify the admin or the
    // owner` must say the tail is no verb phrase, not fall through to the
    // one-vp reading where the object coordination absorbs the `or`).
    let mut failed_split: Option<usize> = None;
    for i in 1..tokens.len() {
        if !kw_at(tokens, i, "or") {
            continue;
        }
        let Ok((first, next)) = parse_vp(&tokens[..i], 0, 0) else {
            continue;
        };
        if next != i {
            continue;
        }
        if let Some(mut tail) = vp_alternatives_tail(&tokens[i + 1..]) {
            let mut items = vec![first];
            items.append(&mut tail);
            return Ok(items);
        }
        if failed_split.is_none() {
            failed_split = Some(i);
        }
    }
    if let Some(i) = failed_split {
        let rest = &tokens[i + 1..];
        return match parse_vp(rest, 0, 0) {
            Err(error) => Err(error),
            Ok((_, next)) if next < rest.len() => Err(unexpected(rest, next)),
            // The remainder is one whole verb phrase — then the tail would
            // have accepted it; unreachable, kept total.
            Ok(_) => Err(ParseError::MixedCoordination),
        };
    }
    // No split point at all: diagnose the whole slice as one verb phrase —
    // either it stops early (the leftover token is the problem) or it IS
    // one verb phrase, which makes the `either` a marker without its `or`
    // (MixedCoordination, exactly as in noun-phrase groups).
    match parse_vp(tokens, 0, 0) {
        Ok((_, next)) if next < tokens.len() => Err(unexpected(tokens, next)),
        Ok(_) => Err(ParseError::MixedCoordination),
        Err(error) => Err(error),
    }
}

/// The remaining alternatives after a split: one verb phrase consuming the
/// whole slice, or a verb phrase up to a further top-level `or` followed
/// (recursively) by more. `None` when no such reading exists.
fn vp_alternatives_tail(tokens: &[Token]) -> Option<Vec<Vp>> {
    for i in 1..tokens.len() {
        if !kw_at(tokens, i, "or") {
            continue;
        }
        let Ok((first, next)) = parse_vp(&tokens[..i], 0, 0) else {
            continue;
        };
        if next != i {
            continue;
        }
        if let Some(mut tail) = vp_alternatives_tail(&tokens[i + 1..]) {
            let mut items = vec![first];
            items.append(&mut tail);
            return Some(items);
        }
    }
    match parse_vp(tokens, 0, 0) {
        Ok((vp, next)) if next == tokens.len() => Some(vec![vp]),
        _ => None,
    }
}

/// `<subject> is/are [always|never] <predicate>`.
fn parse_description(tokens: &[Token], at: usize, subject: NpGroup) -> Result<Core, ParseError> {
    let copula = if kw_at(tokens, at, "is") {
        Copula::Is
    } else {
        Copula::Are
    };
    let mut pos = at + 1;
    let adverb = match word_at(tokens, pos).map(str::to_ascii_lowercase).as_deref() {
        Some("always") => Some(DescriptionAdverb::Always),
        Some("never") => Some(DescriptionAdverb::Never),
        _ => None,
    };
    if adverb.is_some() {
        pos += 1;
    }
    // Capability: the token sequence `able to` right after the copula OR
    // after the description adverb (round 5: `is always able to <vp>` and
    // `is never able to <vp>` are capability, with the adverb kept — a
    // negative capability composes `never` with a subject `no` exactly like
    // a description's `never` does).
    if kw_at(tokens, pos, "able") && kw_at(tokens, pos + 1, "to") {
        let (vp, next) = parse_vp(tokens, pos + 2, 0)?;
        expect_core_end(tokens, next)?;
        return Ok(Core::Description {
            subject,
            copula,
            adverb,
            predicate: Predicate::AbleTo { vp: Box::new(vp) },
            agent: None,
            roles: Vec::new(),
        });
    }
    if kw_at(tokens, pos, "not") {
        return Err(ParseError::NegatedDescription);
    }
    let (predicate, next) = parse_predicate(tokens, pos, NpCtx::Predicate, 0)?;
    // The passive agent (round 5): `The request is logged by the daemon.`
    // — predicate collection stopped at `by`, so the agent phrase is here.
    // Round 8 follow-up: the agent phrase is collected in verb-phrase
    // context and a thematic-role tail follows it, so `is logged by the
    // daemon within 5 seconds` keeps its Deadline structured — the
    // described passive meets the deontic passive at one atom (round 5's
    // promise) instead of the agent noun phrase swallowing the tail. An
    // agentless description keeps the plain predicate reading: without a
    // `by`, predicate collection already absorbed the tail as words.
    let (agent, next) = parse_optional_agent(tokens, next)?;
    let (roles, next) = if agent.is_some() {
        // A passive site, like a `be` verb phrase: a later `by` in the
        // tail is the Agent role.
        parse_roles(tokens, next, 0, true)?
    } else {
        (Vec::new(), next)
    };
    expect_core_end(tokens, next)?;
    Ok(Core::Description {
        subject,
        copula,
        adverb,
        predicate,
        agent,
        roles,
    })
}

/// The optional passive-agent phrase after a description's or a copular
/// clause's predicate: `by <np-group>`. The agent phrase is always
/// collected in verb-phrase context so a role tail after the agent is
/// never swallowed into the agent's noun phrase — descriptions included
/// (round 8 follow-up; before it, descriptions kept the plain reading and
/// the tail was silently folded into the agent).
fn parse_optional_agent(
    tokens: &[Token],
    pos: usize,
) -> Result<(Option<NpGroup>, usize), ParseError> {
    if !kw_at(tokens, pos, "by") {
        return Ok((None, pos));
    }
    let (np, next) = parse_np_group(tokens, pos + 1, NpCtx::Vp, unexpected(tokens, pos + 1), 0)?;
    Ok((Some(np), next))
}

/// `<term> means <definiens>`. The term is one noun phrase — a coordinated
/// term has no single definition, so the conjunction is rejected.
fn parse_definition(tokens: &[Token], at: usize, subject: NpGroup) -> Result<Core, ParseError> {
    let term = match subject {
        NpGroup::Single(np) => np,
        NpGroup::Coordinated { conj, .. } => {
            return Err(ParseError::UnexpectedTokens {
                token: conj.as_str().to_string(),
            });
        }
    };
    let rest = &tokens[at + 1..];
    if rest.is_empty() {
        return Err(ParseError::EmptyDefiniens);
    }
    let definiens = parse_definiens(rest)?;
    Ok(Core::Definition { term, definiens })
}

/// The definiens consumes everything after `means`: an explicit `that` forces
/// a full clause; otherwise a copular clause when a clause copula is present,
/// then a noun phrase with optional role phrases, falling back to a verbal
/// clause. The noun-phrase reading is tried
/// before the verbal one because a bare phrase like `a shared folder` must not
/// be misread as subject `a shared` + verb `folder` — with open-class words
/// opaque, `the request expires` and `a shared folder` are the same shape, so
/// one deterministic reading has to win and the noun-phrase one does.
fn parse_definiens(tokens: &[Token]) -> Result<Definiens, ParseError> {
    // `means that <clause>`: the explicit marker forces the clause reading
    // (verbal or copular) over the rest of the core. Canonical render always
    // re-emits the marker.
    if kw_at(tokens, 0, "that") {
        let rest = &tokens[1..];
        if rest.is_empty() {
            return Err(ParseError::EmptyDefiniens);
        }
        return Ok(Definiens::Clause(parse_clause(rest, 0)?));
    }
    let np_reading = || -> Result<Definiens, ParseError> {
        let (np, at) = parse_np_group(tokens, 0, NpCtx::Vp, ParseError::EmptyDefiniens, 0)?;
        let (roles, next) = parse_roles(tokens, at, 0, false)?;
        if next < tokens.len() {
            return Err(unexpected(tokens, next));
        }
        Ok(Definiens::Np { np, roles })
    };
    if (0..tokens.len()).any(|i| parse_clause_copula(tokens, i).is_some()) {
        // A clause copula commits to the clause reading — unless no clause
        // exists because the copula belongs to a relative inside a noun
        // phrase (`a part that is small`), in which case the noun-phrase
        // reading is the only one left.
        return match parse_clause(tokens, 0) {
            Ok(clause) => Ok(Definiens::Clause(clause)),
            Err(clause_err) => np_reading().map_err(|_| clause_err),
        };
    }
    let np_reading = np_reading();
    match np_reading {
        Ok(definiens) => Ok(definiens),
        Err(np_err) => parse_clause(tokens, 0)
            .map(Definiens::Clause)
            .map_err(|_| np_err),
    }
}

/// After the core's phrases, nothing may remain: a frame keyword here means
/// the condition was written trailing, anything else is stray material.
fn expect_core_end(tokens: &[Token], pos: usize) -> Result<(), ParseError> {
    match word_at(tokens, pos) {
        None if pos >= tokens.len() => Ok(()),
        Some(w) if in_list(FRAME_KEYWORDS, w) => Err(ParseError::MidSentenceFrame {
            keyword: w.to_string(),
        }),
        _ => Err(unexpected(tokens, pos)),
    }
}

// ---- frames and sentences -----------------------------------------------------------

/// Parse the leading circumstance frames, enforcing canonical order:
/// `Where` scopes, then `While` states, then at most one `When`/`If` trigger.
/// Returns the frames and the position of the first core token.
fn parse_frames(tokens: &[Token]) -> Result<(Frames, usize), ParseError> {
    let mut frames = Frames::default();
    let mut at = 0;
    loop {
        let Some(keyword) =
            word_at(tokens, at).filter(|w| in_list(&["where", "while", "when", "if"], w))
        else {
            return Ok((frames, at));
        };
        let keyword = keyword.to_string();
        let lower = keyword.to_ascii_lowercase();
        // Canonical-order violations name what the frame illegally follows.
        if let Some(trigger) = &frames.trigger {
            if lower == "when" || lower == "if" {
                return Err(ParseError::MultipleTriggers {
                    first: trigger.keyword.clone(),
                    second: keyword,
                });
            }
            return Err(ParseError::FrameOrder {
                keyword,
                after: trigger.keyword.clone(),
            });
        }
        if lower == "where" {
            if let Some(state) = frames.states.last() {
                return Err(ParseError::FrameOrder {
                    keyword,
                    after: state.keyword.clone(),
                });
            }
        }
        // The clause runs to the frame's comma.
        let Some(comma_at) = (at + 1..tokens.len()).find(|&i| tokens.get(i) == Some(&Token::Comma))
        else {
            return Err(ParseError::UnterminatedFrame { keyword });
        };
        if comma_at == at + 1 {
            return Err(ParseError::EmptyFrame { keyword });
        }
        let clause = parse_clause_group(&tokens[at + 1..comma_at], 0)?;
        // A trigger's `and` group takes at most ONE event (verbal) conjunct:
        // `and` over occurrences is simultaneity, which has no single
        // reading; every other conjunct must be a state (copular), read at
        // the trigger instant. `or` groups are EXEMPT — a disjunction of
        // events is alternation (either occurrence triggers), which is
        // well-defined. While/Where frames are unrestricted: their clauses
        // are states either way.
        if (lower == "when" || lower == "if")
            && clause.conj == Some(Conj::And)
            && clause
                .items
                .iter()
                .filter(|c| matches!(c.body, ClauseBody::Verbal { .. }))
                .count()
                > 1
        {
            return Err(ParseError::MultipleEventConjuncts);
        }
        at = comma_at + 1;
        let is_if = lower == "if";
        if kw_at(tokens, at, "then") {
            if is_if {
                at += 1; // consumed; render always re-emits it
            } else {
                return Err(ParseError::ThenWithoutIf);
            }
        }
        match lower.as_str() {
            "where" => frames.scopes.push(Frame { keyword, clause }),
            "while" => frames.states.push(Frame { keyword, clause }),
            "when" => {
                frames.trigger = Some(Trigger {
                    kind: TriggerKind::Event,
                    keyword,
                    clause,
                });
            }
            _ => {
                frames.trigger = Some(Trigger {
                    kind: TriggerKind::Contingency,
                    keyword,
                    clause,
                });
            }
        }
    }
}

/// Parse one sentence from its tokens (trailing terminator, if any, already
/// meaningful only as an end marker) and its exact source slice.
fn parse_sentence(tokens: &[Token], source: &str) -> Result<Sentence, ParseError> {
    // Fresh packrat table for this sentence, dropped with it: spans are
    // keyed by buffer address (see [`parse_np_group_exact`]), and another
    // sentence's buffer may later sit where this one's did.
    let _memo_scope = MemoScope::arm();
    let tokens = match tokens.last() {
        Some(Token::Terminator) => &tokens[..tokens.len() - 1],
        _ => tokens,
    };
    if tokens.is_empty() {
        return Err(ParseError::Empty);
    }
    if let Some(stray) = tokens.iter().position(|t| *t == Token::Terminator) {
        return Err(unexpected(tokens, stray));
    }
    let (frames, core_at) = parse_frames(tokens)?;
    let rest = &tokens[core_at..];
    // Split the remainder at its top-level commas: core, then exception and
    // purpose adjuncts, in that order.
    let mut segments: Vec<&[Token]> = Vec::new();
    let mut start = 0;
    for (i, token) in rest.iter().enumerate() {
        if *token == Token::Comma {
            segments.push(&rest[start..i]);
            start = i + 1;
        }
    }
    segments.push(&rest[start..]);
    let mut iter = segments.into_iter();
    let core_tokens = iter.next().unwrap_or_default();
    let core = parse_core(core_tokens)?;
    let mut exception: Option<Clause> = None;
    let mut purpose: Option<Purpose> = None;
    for segment in iter {
        match word_at(segment, 0).map(str::to_ascii_lowercase).as_deref() {
            Some("unless") if exception.is_none() && purpose.is_none() => {
                exception = Some(parse_clause(&segment[1..], 0)?);
            }
            Some("so") if kw_at(segment, 1, "that") && purpose.is_none() => {
                purpose = Some(Purpose::SoThat(parse_clause(&segment[2..], 0)?));
            }
            Some("in")
                if kw_at(segment, 1, "order") && kw_at(segment, 2, "to") && purpose.is_none() =>
            {
                let (vp, next) = parse_vp(segment, 3, 0)?;
                expect_core_end(segment, next)?;
                purpose = Some(Purpose::InOrderTo(vp));
            }
            _ => return Err(unexpected(segment, 0)),
        }
    }
    // A definition is timeless: only `Where` frames may scope it.
    if matches!(core, Core::Definition { .. }) {
        let offending = frames
            .states
            .first()
            .map(|f| f.keyword.clone())
            .or_else(|| frames.trigger.as_ref().map(|t| t.keyword.clone()));
        if let Some(keyword) = offending {
            return Err(ParseError::FrameOnDefinition { keyword });
        }
    }
    Ok(Sentence {
        source: source.to_string(),
        frames,
        core,
        exception,
        purpose,
    })
}

/// Split the input into per-sentence slices: a sentence ends at a word whose
/// final character is `.` (followed by whitespace or end of input). Slices are
/// trimmed to their first and last word, terminator included.
fn split_sentences(input: &str) -> Vec<&str> {
    let mut sentences = Vec::new();
    let mut sentence_start: Option<usize> = None;
    let mut word_ends_sentence = false;
    let mut last_end = 0;
    for (i, ch) in input.char_indices() {
        if ch.is_ascii_whitespace() {
            if let Some(start) = sentence_start {
                if word_ends_sentence {
                    sentences.push(&input[start..last_end]);
                    sentence_start = None;
                }
            }
            word_ends_sentence = false;
        } else {
            if sentence_start.is_none() {
                sentence_start = Some(i);
            }
            word_ends_sentence = ch == '.';
            last_end = i + ch.len_utf8();
        }
    }
    if let Some(start) = sentence_start {
        sentences.push(&input[start..last_end]);
    }
    sentences
}

/// Parse a specification: one or more sentences, each yielding exactly one
/// tree, the whole input yielding exactly one [`Specification`] or one
/// [`ParseError`].
pub fn parse(input: &str) -> Result<Specification, ParseError> {
    let sources = split_sentences(input);
    if sources.is_empty() {
        return Err(ParseError::Empty);
    }
    let mut sentences = Vec::with_capacity(sources.len());
    for source in sources {
        let tokens = tokenize(source);
        sentences.push(parse_sentence(&tokens, source)?);
    }
    Ok(Specification { sentences })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Token> {
        tokenize(s)
    }

    #[test]
    fn tokenizer_splits_terminator_and_comma() {
        assert_eq!(
            toks("stop, now."),
            vec![
                Token::Word("stop".into()),
                Token::Comma,
                Token::Word("now".into()),
                Token::Terminator,
            ]
        );
    }

    #[test]
    fn tokenizer_keeps_decimals_and_urls_glued() {
        assert_eq!(toks("5.5"), vec![Token::Word("5.5".into())]);
        assert_eq!(
            toks("to http://192.168.10.4:4318."),
            vec![
                Token::Word("to".into()),
                Token::Word("http://192.168.10.4:4318".into()),
                Token::Terminator,
            ]
        );
    }

    #[test]
    fn tokenizer_handles_multibyte_and_lone_punctuation() {
        assert_eq!(
            toks("café."),
            vec![Token::Word("café".into()), Token::Terminator]
        );
        assert_eq!(toks("."), vec![Token::Terminator]);
        assert_eq!(toks(","), vec![Token::Comma]);
        assert_eq!(toks("×"), vec![Token::Word("×".into())]);
    }

    #[test]
    fn det_forms() {
        assert_eq!(parse_det(&toks("the pump"), 0), Some((Det::The, 1)));
        assert_eq!(
            parse_det(&toks("at least 3 nodes"), 0),
            Some((Det::AtLeast { n: 3 }, 3))
        );
        assert_eq!(
            parse_det(&toks("at most two"), 0),
            Some((Det::AtMost { n: 2 }, 3))
        );
        assert_eq!(
            parse_det(&toks("exactly 7"), 0),
            Some((Det::Exactly { n: 7 }, 2))
        );
        // `at` without a bound+number stays open-class.
        assert_eq!(parse_det(&toks("at the door"), 0), None);
        assert_eq!(parse_det(&toks("pump"), 0), None);
    }

    #[test]
    fn np_with_of_chain() {
        let t = toks("a sequence of requests");
        let (np, next) = parse_np(&t, 0, NpCtx::Plain, ParseError::EmptySubject, 0).unwrap();
        assert_eq!(next, 4);
        assert_eq!(np.det, Some(Det::A));
        assert_eq!(np.head, "sequence");
        assert_eq!(np.of.as_ref().unwrap().head, "requests");
    }

    #[test]
    fn np_group_coordination() {
        let t = toks("TraceContext and Baggage propagators");
        let (group, next) = parse_np_group(&t, 0, NpCtx::Vp, ParseError::EmptySubject, 0).unwrap();
        assert_eq!(next, 4);
        match group {
            NpGroup::Coordinated {
                conj: Conj::And,
                marker: None,
                items,
            } => {
                assert_eq!(items[0].head, "TraceContext");
                assert_eq!(items[1].head, "propagators");
                assert_eq!(items[1].modifiers, vec!["Baggage".to_string()]);
            }
            other => panic!("expected coordination, got {other:?}"),
        }
    }

    #[test]
    fn np_group_rejects_mixed_conjunctions() {
        let t = toks("the total and or the tax");
        let t2 = toks("x and y or z");
        assert_eq!(
            parse_np_group(&t, 0, NpCtx::Plain, ParseError::EmptySubject, 0),
            Err(ParseError::MixedCoordination)
        );
        assert_eq!(
            parse_np_group(&t2, 0, NpCtx::Plain, ParseError::EmptySubject, 0),
            Err(ParseError::MixedCoordination)
        );
    }

    #[test]
    fn comparison_forms() {
        let t = toks("greater than zero");
        let (p, next) = parse_predicate(&t, 0, NpCtx::Plain, 0).unwrap();
        assert_eq!(next, 3);
        assert_eq!(
            p,
            Predicate::Comparison(Comparison {
                op: ComparisonOp::GreaterThan,
                value: Measure::Quantity {
                    number: "zero".into(),
                    unit: None
                },
                upper: None,
            })
        );
        let t = toks("between 5 and 30 seconds");
        let (p, _) = parse_predicate(&t, 0, NpCtx::Plain, 0).unwrap();
        assert_eq!(
            p,
            Predicate::Comparison(Comparison {
                op: ComparisonOp::Between,
                value: Measure::Quantity {
                    number: "5".into(),
                    unit: None
                },
                upper: Some(Measure::Quantity {
                    number: "30".into(),
                    unit: Some("seconds".into())
                }),
            })
        );
    }

    fn one(input: &str) -> Sentence {
        let spec = parse(input).unwrap();
        assert_eq!(
            spec.sentences.len(),
            1,
            "expected one sentence in {input:?}"
        );
        spec.sentences.into_iter().next().unwrap()
    }

    #[test]
    fn simple_obligation() {
        let s = one("The pump shall stop.");
        assert_eq!(s.source, "The pump shall stop.");
        assert!(s.frames.is_empty());
        match &s.core {
            Core::Deontic {
                subject,
                modal: Modal::Shall,
                negated: false,
                vp,
            } => {
                assert_eq!(subject.heads(), vec!["pump"]);
                assert_eq!(vp.single().unwrap().verb, "stop");
                assert!(vp.single().unwrap().object.is_none());
            }
            other => panic!("expected deontic, got {other:?}"),
        }
    }

    #[test]
    fn trigger_and_core() {
        let s = one("When the order is submitted, the system shall record the total.");
        let trigger = s.frames.trigger.as_ref().unwrap();
        assert_eq!(trigger.kind, TriggerKind::Event);
        assert_eq!(trigger.keyword, "When");
        assert_eq!(trigger.clause.items[0].subject.heads(), vec!["order"]);
        assert!(matches!(
            &trigger.clause.items[0].body,
            ClauseBody::Copular {
                copula: ClauseCopula::Is,
                ..
            }
        ));
    }

    #[test]
    fn verbal_frame_clause() {
        let s = one("When the temperature exceeds the limit, the controller shall open the valve.");
        let trigger = s.frames.trigger.as_ref().unwrap();
        match &trigger.clause.items[0].body {
            ClauseBody::Verbal { verb, object, .. } => {
                assert_eq!(verb, "exceeds");
                assert_eq!(object.as_ref().unwrap().heads(), vec!["limit"]);
            }
            other => panic!("expected verbal clause, got {other:?}"),
        }
    }

    #[test]
    fn frame_errors() {
        assert_eq!(
            parse("When the order is submitted the system shall record the total."),
            Err(ParseError::UnterminatedFrame {
                keyword: "When".into()
            })
        );
        assert_eq!(
            parse("When , the pump shall stop."),
            Err(ParseError::EmptyFrame {
                keyword: "When".into()
            })
        );
        assert_eq!(
            parse("When the order ships, while the engine runs, the pump shall stop."),
            Err(ParseError::FrameOrder {
                keyword: "while".into(),
                after: "When".into()
            })
        );
        assert_eq!(
            parse("When x occurs, if y occurs, the pump shall stop."),
            Err(ParseError::MultipleTriggers {
                first: "When".into(),
                second: "if".into()
            })
        );
        assert_eq!(
            parse("While the engine is running, then the pump shall stop."),
            Err(ParseError::ThenWithoutIf)
        );
    }

    #[test]
    fn exception_and_purpose() {
        // Round 11: `retains control` (a boundary-less bare run) is the
        // ambiguous verb-boundary class; the determiner on the object is
        // the honest form.
        let s = one("The pump shall stop, unless the override is active, so that the operator retains the control.");
        assert!(s.exception.is_some());
        assert!(matches!(s.purpose, Some(Purpose::SoThat(_))));
        let s = one("The system shall log each request, in order to preserve the audit trail.");
        match &s.purpose {
            Some(Purpose::InOrderTo(vp)) => assert_eq!(vp.verb, "preserve"),
            other => panic!("expected in-order-to, got {other:?}"),
        }
    }

    #[test]
    fn definition_and_its_frames() {
        let s = one("where the premium plan is enabled, a workspace means a shared folder.");
        assert_eq!(s.frames.scopes[0].keyword, "where");
        match &s.core {
            Core::Definition { term, definiens } => {
                assert_eq!(term.head, "workspace");
                match definiens {
                    Definiens::Np { np, roles } => {
                        assert_eq!(np.heads(), vec!["folder"]);
                        assert!(roles.is_empty());
                    }
                    other => panic!("expected np definiens, got {other:?}"),
                }
            }
            other => panic!("expected definition, got {other:?}"),
        }
        assert_eq!(
            parse("While the engine is running, a workspace means a shared folder."),
            Err(ParseError::FrameOnDefinition {
                keyword: "While".into()
            })
        );
    }

    #[test]
    fn core_errors() {
        assert_eq!(parse(""), Err(ParseError::Empty));
        assert_eq!(parse("   "), Err(ParseError::Empty));
        assert_eq!(parse("."), Err(ParseError::Empty));
        assert_eq!(parse("The pump quickly."), Err(ParseError::MissingPivot));
        assert_eq!(parse("The shall run."), Err(ParseError::EmptySubject));
        assert_eq!(parse("The pump shall."), Err(ParseError::EmptyVp));
        assert_eq!(
            parse("The client may not retry."),
            Err(ParseError::AmbiguousModal)
        );
        assert_eq!(
            parse("The client can retry."),
            Err(ParseError::UnsupportedModal { word: "can".into() })
        );
        assert_eq!(
            parse("The sales amount is not greater than zero."),
            Err(ParseError::NegatedDescription)
        );
        assert_eq!(
            parse("The tracing library should default export to X when no endpoint is configured."),
            Err(ParseError::MidSentenceFrame {
                keyword: "when".into()
            })
        );
    }

    #[test]
    fn predicate_pp_and_words() {
        let t = toks("below the limit");
        let (p, _) = parse_predicate(&t, 0, NpCtx::Plain, 0).unwrap();
        match p {
            Predicate::Pp { preposition, .. } => assert_eq!(preposition, "below"),
            other => panic!("expected pp, got {other:?}"),
        }
        let t = toks("frozen");
        let (p, _) = parse_predicate(&t, 0, NpCtx::Plain, 0).unwrap();
        assert_eq!(
            p,
            Predicate::Words {
                words: vec!["frozen".into()]
            }
        );
        assert_eq!(
            parse_predicate(&toks(""), 0, NpCtx::Plain, 0),
            Err(ParseError::EmptyPredicate)
        );
    }
}
