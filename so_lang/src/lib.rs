//! spec-oracle language: the constrained specification language.
//!
//! This crate owns exactly the constrained natural-language grammar and its
//! parser. It is pure and I/O-free. A specification is parsed into its sentence
//! structure: modal and definitional cores, circumstance frames
//! (`Where`/`While`/`When`/`If`), exceptions (`unless`), purposes (`so that`),
//! and a phrase grammar of noun phrases, verb phrases, thematic roles, and
//! comparisons. The language constrains *ambiguity*, not expressiveness: the
//! closed-class skeleton is owned by the grammar, open-class vocabulary is
//! free, and every accepted sentence has exactly one reading.
//!
//! The public modules are the boundary:
//!
//! * [`ast`] — the grammar's parsed surface structure.
//! * [`parse`] — the total recognizer: any input yields one parse or one
//!   precise [`parse::ParseError`]. There is no confidence score and no
//!   inference.
//!
//! Meaning projections, assume-guarantee formulas, and comparisons between
//! specifications are consumers of this crate and belong outside it.

pub mod ast;
pub mod parse;

/// The version of the language accepted by [`parse::parse`]. Stored alongside
/// persisted sentences so re-derivation stays auditable as the grammar evolves.
pub const LANG_VERSION: &str = "0.2.0";
