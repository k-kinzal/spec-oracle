//! Adversarial totality attack on the recognizer.
//!
//! [`so_lang::parse::parse`] claims to be a *total* recognizer: every input —
//! however hostile — yields exactly one `Ok(Specification)` or exactly one
//! precise `Err(ParseError)`, and never a panic, a hang, or unbounded memory.
//! This suite exists to break that claim. Every test asserts only totality
//! (returns, does not panic); none of them care whether the answer is Ok or
//! Err. Inputs cover multibyte boundaries, lone combining marks, mixed
//! CJK/emoji, pathological punctuation, deep `of`-chains and wide
//! coordinations, reserved words in wrong positions, whitespace variants,
//! extremely long single tokens, permutations of every corpus reject string,
//! and a deterministic seeded word-soup generator.

use so_lang::parse::parse;
use std::panic::{catch_unwind, AssertUnwindSafe};

/// Truncate an input for a failure message without splitting a char.
fn preview(input: &str) -> String {
    const MAX: usize = 160;
    if input.chars().count() <= MAX {
        return format!("{input:?}");
    }
    let head: String = input.chars().take(MAX).collect();
    format!("{head:?}… ({} bytes total)", input.len())
}

/// Assert that `parse` returns — Ok or Err, either is fine — without panicking.
fn total(input: &str) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let _ = parse(input);
    }));
    assert!(
        outcome.is_ok(),
        "parse panicked on input: {}",
        preview(input)
    );
}

fn total_all<'a, I: IntoIterator<Item = &'a str>>(inputs: I) {
    for input in inputs {
        total(input);
    }
}

// ---- multibyte boundaries, combining marks, CJK/emoji ------------------------------

#[test]
fn attack_multibyte_boundaries() {
    total_all([
        "€",
        "中",
        "中文",
        "南南 shall stop.",
        "éé shall stop.",
        "The café shall serve crêpes.",
        "th×foo shall bar",
        "When x, the×foo the pump shall stop",
        "When x, 日本 the pump shall stop.",
        "×",
        "ß shall ss.",
        "ﬃ shall ligature.",      // U+FB03, expands under case mapping
        "İstanbul shall İ.",      // dotted capital I, lowercases to two chars
        "𝕊𝕡𝕖𝕔 shall 𝕡𝕒𝕣𝕤𝕖.",      // 4-byte mathematical alphanumerics
        "\u{10FFFF} shall stop.", // highest scalar value
        "a\u{0000}b shall stop.", // embedded NUL
        "\u{0000}",
    ]);
}

#[test]
fn attack_lone_combining_marks() {
    total_all([
        "\u{0301}",                                              // lone combining acute accent
        "\u{0301} shall stop.",                                  // combining mark as subject word
        "e\u{0301} shall stop.",                                 // decomposed é
        "The pump shall sto\u{0308}p.",                          // combining diaeresis mid-word
        "\u{0301}\u{0302}\u{0303}",                              // stacked lone marks
        "the \u{0301} shall stop.", // mark as sole head after determiner
        "\u{200D}",                 // lone zero-width joiner
        "\u{200B} shall stop.",     // zero-width space is NOT ascii whitespace
        "\u{FEFF}The pump shall stop.", // BOM glued to the first word
        "\u{202E}The pump shall stop.", // RTL override prefix
        "a\u{0301}\u{0302}\u{0303}\u{0304}\u{0305} shall stop.", // Zalgo-lite
    ]);
}

#[test]
fn attack_mixed_cjk_and_emoji() {
    total_all([
        "🔥 shall stop",
        "🇯🇵 shall 発送 the 荷物.",
        "中文🔥emoji混在 shall parse.",
        "👨‍👩‍👧‍👦 shall stop.", // ZWJ family sequence
        "🏳️‍🌈 means 旗.",
        "🍣 of 🍜 of 🍙 shall be 美味しい.",
        "when 温度 exceeds 限界, ロボット🤖 shall 停止.",
        "🏽",     // lone skin-tone modifier
        "中。文", // ideographic full stop is not ASCII '.'
        "、",     // ideographic comma is not ASCII ','
        "エラー、 shall 、stop。",
    ]);
}

// ---- pathological punctuation -------------------------------------------------------

#[test]
fn attack_pathological_punctuation() {
    total_all([
        ",",
        ".",
        "..",
        "...",
        ",,,",
        ".,",
        ",.",
        ",.,.,.,.",
        ", ,",
        ". .",
        ". . .",
        "a , b",
        ",a",
        "a,",
        "a,,,,b",
        "a.,",
        "a,.",
        ", the pump shall stop.",
        "The pump shall stop ,",
        "The pump shall stop..",
        "The pump shall stop...",
        "The pump, shall, stop.",
        "The, pump, shall, stop,",
        "The pump shall stop, unless",
        "The pump shall stop, ,",
        "The pump shall stop, , so that x is y.",
        "When , the pump shall stop.",
        "When ,, the pump shall stop.",
        "unless, unless, unless.",
        "so that, in order to,",
        "5.5",
        "5.5.",
        "5..5",
        ".5",
        "5.",
        "http://192.168.10.4:4318",
        "http://192.168.10.4:4318.",
        "a.b.c.d.e shall stop.",
    ]);
}

#[test]
fn attack_punctuation_floods() {
    total(&",".repeat(10_000));
    total(&".".repeat(10_000));
    total(&",.".repeat(5_000));
    total(&", ".repeat(5_000));
    total(&". ".repeat(5_000));
    total(&"a,".repeat(5_000));
    total(&"a. ".repeat(5_000));
    total(&"a , ".repeat(5_000));
    // A single word trailed by thousands of peelable marks.
    total(&format!("pump{}", ".".repeat(10_000)));
    total(&format!("pump{}", ",".repeat(10_000)));
    total(&format!("pump{}", ",.".repeat(5_000)));
    // Commas everywhere inside an otherwise plausible sentence.
    total(&format!(
        "When x is y, the pump shall stop{}",
        ", unless a is b".repeat(2_000)
    ));
}

// ---- deep nesting and wide coordination ----------------------------------------------

// FIXED DEFECT — deep structural nesting used to overflow the stack.
//
// `parse_np` recurses once per `of` link and once per nesting level of a
// relative clause (np -> relative -> predicate -> np -> …). Before the
// recognizer gained its `MAX_NP_DEPTH` bound, recursion depth was limited
// only by input length and a few thousand repetitions aborted the process
// with SIGABRT (first crash at 205 reps of "the a that is in " on a 2 MiB
// debug thread; 864 reps of "x of "). The parser now rejects nesting beyond
// the bound with `ParseError::PhraseTooDeep`, so the payload tests below run
// in the default suite and the pinned-stack tests keep guarding the stack
// cost of the depths that remain reachable under the bound.

/// Run an attack on a thread with a pinned 16 MiB stack, so depth budgets are
/// stable regardless of the test harness's thread stack size.
fn on_pinned_stack(attack: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(attack)
        .expect("failed to spawn attack thread")
        .join()
        .expect("attack thread panicked");
}

#[test]
fn attack_deep_of_chain_within_current_stack_budget() {
    on_pinned_stack(|| {
        // Dangling `of` tail: recursion up to the depth bound, then a
        // precise error.
        total(&"x of ".repeat(1_500));
        // The same chain closed off, so the deep tree is built AND dropped.
        total(&format!("{}x", "x of ".repeat(1_500)));
        // As a subject of a real sentence.
        total(&format!("{}x shall stop.", "the a of ".repeat(1_500)));
        // As an object and inside a frame clause. (`a of` has no head noun,
        // so these reject before recursing — kept to pin that behavior.)
        total(&format!("The s shall v {}x.", "a of ".repeat(3_000)));
        total(&format!(
            "When {}x is hot, the pump shall stop.",
            "a of ".repeat(3_000)
        ));
    });
}

#[test]
fn attack_deep_relative_nesting_within_current_stack_budget() {
    on_pinned_stack(|| {
        // Each level recurses np -> relative -> copular predicate -> np …
        total(&format!(
            "{}the end shall stop.",
            "the a that is in ".repeat(300)
        ));
        // … or np -> relative -> verbal object -> np …
        total(&format!("{}the end", "the a that contains ".repeat(300)));
        total(&format!(
            "a x means {}the end.",
            "the a that is in ".repeat(300)
        ));
    });
}

#[test]
fn attack_deep_of_chain_5000_stack_overflow() {
    // 5000 repetitions of "x of " — 10_000 tokens. Used to overflow the
    // parser's recursion in debug builds (first crash at 3468 repetitions);
    // now rejected by the depth bound.
    total(&"x of ".repeat(5_000));
    total(&format!("{}x", "x of ".repeat(5_000)));
    total(&format!("{}x shall stop.", "the a of ".repeat(5_000)));
}

#[test]
fn attack_deep_relative_nesting_stack_overflow() {
    // Used to crash at 821 repetitions in debug builds; now rejected by the
    // depth bound.
    total(&format!(
        "{}the end shall stop.",
        "the a that is in ".repeat(1_000)
    ));
}

#[test]
fn attack_wide_coordination() {
    // Thousands of coordinated items (iterative in the grammar, but prove it).
    total(&format!("{}b shall stop.", "a and ".repeat(4_000)));
    total(&format!("{}b shall stop.", "a or ".repeat(4_000)));
    total(&format!("The s shall v {}b.", "a and ".repeat(4_000)));
    total(&format!("both {}b shall stop.", "a and ".repeat(4_000)));
    total(&format!("either {}b shall stop.", "a or ".repeat(4_000)));
    // Alternating conjunctions at scale must reject, not wedge.
    total(&format!("{}b shall stop.", "a and b or ".repeat(2_000)));
    // Dangling conjunction tails.
    total(&"a and ".repeat(4_000));
    total("both and");
    total("either or");
    total("both a and b and c shall stop.");
}

#[test]
fn attack_many_frames_roles_and_sentences() {
    total(&format!(
        "{}the pump shall stop.",
        "where a is b, ".repeat(2_000)
    ));
    total(&format!(
        "{}the pump shall stop.",
        "while a is b, ".repeat(2_000)
    ));
    total(&format!("The s shall v{}.", " to x".repeat(3_000)));
    total(&format!(
        "The s shall v{}.",
        " within 5 seconds".repeat(2_000)
    ));
    total(&"The pump shall stop. ".repeat(2_000));
    total(&format!(
        "The pump shall stop{}",
        ", so that a is b".repeat(2_000)
    ));
}

// ---- reserved words in wrong positions ------------------------------------------------

/// Every closed-class word the grammar owns anywhere.
const RESERVED: &[&str] = &[
    "shall", "must", "should", "may", "is", "are", "means", "can", "will", "would", "could",
    "might", "ought", "where", "while", "when", "if", "unless", "of", "that", "who", "and", "or",
    "both", "either", "remains", "then", "not", "to", "via", "using", "about", "within", "for",
    "per", "before", "after", "from", "into", "the", "a", "an", "each", "every", "all", "any",
    "no", "at", "least", "most", "exactly", "greater", "less", "than", "equal", "between", "so",
    "in", "order", "always", "never", "be", "zero", "one", "ten", "on", "below", "above", "under",
    "over",
];

#[test]
fn attack_reserved_words_in_wrong_positions() {
    for w in RESERVED {
        total(w);
        total(&format!("{w}."));
        total(&format!("{w} {w}"));
        total(&format!("{w} {w} {w}."));
        total(&format!("{w},"));
        total(&format!(", {w}"));
        total(&format!("the {w} shall stop."));
        total(&format!("The pump {w} stop."));
        total(&format!("The pump shall {w}."));
        total(&format!("The pump shall stop {w}."));
        total(&format!("The pump shall stop, {w}."));
        total(&format!("when {w}, the pump shall stop."));
        total(&format!("{w} the pump shall stop."));
        total(&format!("The pump shall stop, unless {w}."));
        total(&format!("a x means {w}."));
        total(&format!("{w} means {w}."));
        total(&format!("The x is {w}."));
        total(&format!("The s shall v to {w}."));
        total(&format!("The s shall be {w}."));
    }
    // Full reserved word soup in one line, forwards and backwards.
    let all = RESERVED.join(" ");
    total(&all);
    let mut rev: Vec<&str> = RESERVED.to_vec();
    rev.reverse();
    total(&rev.join(" "));
}

// ---- empty and whitespace variants ---------------------------------------------------

#[test]
fn attack_empty_and_whitespace() {
    total_all([
        "",
        " ",
        "  ",
        "\t",
        "\n",
        "\r",
        "\r\n",
        " \t \n \r ",
        "\u{000B}\u{000C}", // vertical tab, form feed
        "\u{00A0}",         // NBSP: not ASCII whitespace, becomes a word
        "\u{3000}",         // ideographic space: likewise
        "\u{00A0}\u{3000}\u{2009}",
        " . ",
        " , ",
        " .",
        ". ",
        "\n.\n",
        "\t,\t",
        " \u{FEFF} ",
    ]);
    total(&" ".repeat(100_000));
    total(&"\n".repeat(100_000));
}

// ---- extremely long single tokens -----------------------------------------------------

#[test]
fn attack_extremely_long_tokens() {
    let giant = "a".repeat(1_000_000);
    total(&giant);
    total(&format!("{giant} shall stop."));
    total(&format!("The pump shall {giant}."));
    let digits = "9".repeat(100_000);
    total(&digits);
    total(&format!("The delay is at most {digits} seconds."));
    total(&format!("at least {digits} pumps shall stop."));
    total(&format!("{d}.{d}", d = "9".repeat(50_000))); // giant decimal
    total(&format!("http://{}x shall route.", "a.".repeat(20_000))); // giant dotted URL
    total(&"é".repeat(200_000)); // giant multibyte token
    total(&"🔥".repeat(100_000)); // giant emoji token
    total(&format!("x{}", "?".repeat(500_000)));
}

// ---- every corpus reject string, permuted ----------------------------------------------

/// The reject strings from the language spec's acceptance corpus.
const REJECTS: &[&str] = &[
    ".",
    "The sales amount is not greater than zero.",
    "The client may not retry.",
    "The client can retry.",
    "When the order is submitted the system shall record the total.",
    "When , the pump shall stop.",
    "When the order ships, while the engine runs, the pump shall stop.",
    "When x occurs, if y occurs, the pump shall stop.",
    "While the engine is running, then the pump shall stop.",
    "While the engine is running, a workspace means a shared folder.",
    "The pump quickly.",
    "The shall run.",
    "The pump shall.",
    "The system shall record the total and or the tax.",
    "The tracing library should default export to X when no endpoint is configured.",
    "The pump shall stop, unless",
    "both and",
];

#[test]
fn attack_corpus_rejects_permuted() {
    let mut rng = XorShift::new(0x5EED_0DDB_A5E5_0001);
    for reject in REJECTS {
        let words: Vec<&str> = reject.split_ascii_whitespace().collect();
        // Every rotation.
        for shift in 0..words.len() {
            let mut rotated = words.clone();
            rotated.rotate_left(shift);
            total(&rotated.join(" "));
        }
        // Reversal.
        let mut reversed = words.clone();
        reversed.reverse();
        total(&reversed.join(" "));
        // 100 seeded shuffles.
        for _ in 0..100 {
            let mut shuffled = words.clone();
            rng.shuffle(&mut shuffled);
            total(&shuffled.join(" "));
        }
    }
}

// ---- deterministic pseudo-random word soup ---------------------------------------------

/// xorshift64* — deterministic, dependency-free.
struct XorShift(u64);

impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(if seed == 0 {
            0x9E37_79B9_7F4A_7C15
        } else {
            seed
        })
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Uniform-enough index in `0..bound` (bound > 0).
    fn below(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            items.swap(i, self.below(i + 1));
        }
    }
}

/// The vocabulary the soup draws from: reserved words, open-class words,
/// punctuation-riddled fragments, numbers, multibyte, and emoji.
const SOUP_EXTRA: &[&str] = &[
    "pump",
    "valve",
    "system",
    "x",
    "y",
    "z",
    "stop",
    "record",
    "total",
    "temperature",
    "café",
    "中文",
    "🔥",
    "👨‍👩‍👧‍👦",
    "\u{0301}",
    "×",
    "é",
    "5",
    "5.5",
    "0",
    "42",
    "999999999999999999999999",
    "http://192.168.10.4:4318",
    "a.b.c",
    ",",
    ".",
    ",,",
    "..",
    ",.",
    ".,",
    "x,",
    "x.",
    ",x",
    "then,",
    "shall.",
    "of,",
    "and.",
    "",
    "-",
    "--",
    "_",
    "()",
    "\"quoted\"",
    "'q'",
    ";",
    ":",
    "?!",
    "\u{200B}",
    "\u{FEFF}",
    "\u{3000}",
];

#[test]
fn attack_seeded_word_soup() {
    let mut vocabulary: Vec<&str> = Vec::new();
    vocabulary.extend_from_slice(RESERVED);
    vocabulary.extend_from_slice(SOUP_EXTRA);
    let mut rng = XorShift::new(0xDEAD_BEEF_CAFE_F00D);
    for _ in 0..6_000 {
        let len = rng.below(41); // 0..=40 tokens
        let mut words = Vec::with_capacity(len);
        for _ in 0..len {
            words.push(vocabulary[rng.below(vocabulary.len())]);
        }
        let mut soup = words.join(" ");
        // A third of the soups get a random terminator treatment.
        match rng.below(3) {
            0 => soup.push('.'),
            1 => soup.push(','),
            _ => {}
        }
        total(&soup);
    }
}

/// Pure random Unicode noise, independent of the vocabulary: any scalar value
/// except the surrogates the char type already excludes.
#[test]
fn attack_seeded_unicode_noise() {
    let mut rng = XorShift::new(0x0123_4567_89AB_CDEF);
    for _ in 0..1_000 {
        let len = rng.below(120);
        let mut soup = String::new();
        for _ in 0..len {
            let c = loop {
                if let Some(c) = char::from_u32((rng.next_u64() % 0x11_0000) as u32) {
                    break c;
                }
            };
            soup.push(c);
        }
        total(&soup);
    }
}
