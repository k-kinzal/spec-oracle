//! spec-oracle language: the constrained natural-language grammar.
//!
//! A specification statement is written in an EARS-derived controlled language
//! and projected, mechanically and unambiguously, into an assume-guarantee
//! contract. This crate is the *language* layer — pure and I/O-free: it turns
//! words into a [`grammar::Contract`] and nothing else. Capture, storage, and
//! the graph live in the crates above it.
//!
//! The assume-guarantee vocabulary ([`grammar::Assumption`],
//! [`grammar::Guarantee`], [`grammar::Condition`], [`grammar::Contract`]) is
//! defined here because it is the *output of the language*; the higher layers
//! embed these types in the persisted node and on the wire.

pub mod grammar;
