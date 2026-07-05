//! The daemon-owned domain types — the serde model persisted by the daemon.
//! The assume-guarantee vocabulary (`Assumption`,
//! `Guarantee`, `Condition`) is re-exported from the language crate, since it is
//! the output of the grammar; everything else (the node, its evidence, the
//! snapshot/origin/locator) is defined here.

pub mod locator;
pub mod node;
pub mod origin;
pub mod snapshot;

pub use locator::{Kind, Locator};
pub use node::{Evidence, Meta, Node};
pub use origin::Origin;
pub use snapshot::{Anchor, Snapshot};

pub use so_lang::grammar::{Assumption, Condition, Contract, Guarantee};
