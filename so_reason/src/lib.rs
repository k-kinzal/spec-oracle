//! Derived interpretations and structural reasoning over parsed specifications.
//!
//! This crate consumes [`so_lang`] parse trees. It owns every interpretation
//! that goes beyond recognizing the constrained natural-language grammar:
//! speech acts, formulas, semantic assume-guarantee contracts and their
//! formation, and cross-specification judgments. [`semantics`] derives
//! sentence denotations, [`formula`] supplies the symbolic assertion domain,
//! [`contract`] owns A/G semantics and formation, and [`relate`] owns the
//! conservative decision procedures. The crate is pure and I/O-free, but it
//! is not part of the language or parser.

pub mod contract;
pub mod formula;
pub mod operational;
pub mod relate;
pub mod semantics;
