//! Derived interpretations and structural reasoning over parsed specifications.
//!
//! This crate consumes [`so_lang`] parse trees. It owns every interpretation
//! that goes beyond recognizing the constrained natural-language grammar:
//! speech acts, assume-guarantee projections, formulas, and cross-specification
//! judgments. It is pure and I/O-free, but it is not part of the language or
//! parser.

pub mod formula;
pub mod relate;
pub mod semantics;
