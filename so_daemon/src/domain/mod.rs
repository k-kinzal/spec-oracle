//! The daemon-owned domain types — the serde model persisted by the daemon.
//! The node holds the raw sentence text and its grounding; everything else
//! (evidence, snapshot/origin/locator) is defined here. Derived readings of a
//! sentence (parse tree, speech act, contract view) come from the language
//! crate at response time and are never part of this model.

pub mod edge;
pub mod locator;
pub mod node;
pub mod origin;
pub mod snapshot;
pub mod term;

pub use edge::{Derivation, Edge, EdgeKind, TextAnchor, VertexKind};
pub use locator::{Kind, Locator};
pub use node::{Evidence, Meta, MetaUpdate, Node};
pub use origin::Origin;
pub use snapshot::{Anchor, Snapshot};
pub use term::TermNode;
