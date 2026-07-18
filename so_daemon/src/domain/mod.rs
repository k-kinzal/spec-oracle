//! The daemon-owned domain types — the serde model persisted by the daemon.
//! The authored node holds the raw sentence text and its grounding. Derived
//! Evidence, Assumption, and Guarantee graph nodes are content-addressed
//! projections; the lossless parse tree and speech act remain computed views.

pub mod assessment;
pub mod derived;
pub mod edge;
pub mod locator;
pub mod node;
pub mod origin;
pub mod selection;
pub mod snapshot;
pub mod term;

pub use assessment::{AssessmentVerdict, RelationAssessment};
pub use derived::DerivedNode;
pub use edge::{Derivation, Edge, EdgeFamily, EdgeKind, EndpointRole, TextAnchor, VertexKind};
pub use locator::{Kind, Locator};
pub use node::{Evidence, Meta, MetaUpdate, Node};
pub use origin::Origin;
pub use selection::{
    ExclusionKind, ScoreContribution, ScoreContributionKind, SelectionExclusion,
    SelectionPopulation, SelectionView,
};
pub use snapshot::{Anchor, Snapshot};
pub use term::TermNode;
