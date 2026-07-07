//! spec-oracle language: the constrained specification language.
//!
//! This crate is the *language* layer — pure and I/O-free. A specification is
//! written in an EARS-derived controlled natural language and parsed into its
//! sentence structure: speech-act cores (definition, description, obligation,
//! prohibition, recommendation, permission), circumstance frames
//! (`Where`/`While`/`When`/`If`), exceptions (`unless`), purposes (`so that`),
//! and a phrase grammar of noun phrases, verb phrases, thematic roles, and
//! comparisons. The language constrains *ambiguity*, not expressiveness: the
//! closed-class skeleton is owned by the grammar, open-class vocabulary is
//! free, and every accepted sentence has exactly one reading.
//!
//! The module split is the architecture:
//!
//! * [`ast`] — the surface syntax. Contains no assume-guarantee vocabulary;
//!   the language must be definable without it.
//! * [`parse`] — the total recognizer: any input yields one parse or one
//!   precise [`parse::ParseError`]. There is no confidence score and no
//!   inference.
//! * [`semantics`] — interpretations *derived over* the syntax: speech acts,
//!   normative force, assertions (the denotation of behavioral sentences), and
//!   the assume-guarantee ingest projection. The contract layer is one
//!   consumer of the words among several; it adapts to the language, never the
//!   reverse.
//! * [`formula`] — symbolic Boolean structure over opaque skeleton-level
//!   atoms: applicability, claim, and contract formulas. The structural
//!   precondition for graph edges; decision procedures live downstream.
//! * [`relate`] — the minimal relation engine over those formulas:
//!   conservative, syntactic `implies`/`contradicts`/`refines` judgments in
//!   a three-valued logic whose `Unknown` is honest and first-class.
//!
//! Raw sentence text remains the source of truth everywhere; parse trees,
//! assertions, and contracts are derived views, versioned by [`LANG_VERSION`].

pub mod ast;
pub mod formula;
pub mod parse;
pub mod relate;
pub mod semantics;

/// The version of the language accepted by [`parse::parse`]. Stored alongside
/// persisted sentences so re-derivation stays auditable as the grammar evolves.
pub const LANG_VERSION: &str = "0.2.0";
