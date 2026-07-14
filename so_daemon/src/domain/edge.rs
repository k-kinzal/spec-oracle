//! A checked, typed binary connection in the one specification graph.
//!
//! An Edge says exactly one bounded thing. Its family separates lexical
//! incidence, semantic relationships, and versioned selection relationships.
//! Endpoint roles make the ordered arguments explicit; `source`/`target` never
//! acquire a graph-wide meaning such as "support flows this way". A candidate,
//! `Independent`, `Unknown`, or an unsearched pair is not topology, and Edge
//! absence has no negative meaning.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VertexKind {
    Specification,
    Term,
    Evidence,
    Assumption,
    Guarantee,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeFamily {
    /// Exact surface-language incidence used for discovery.
    Lexical,
    /// A graph-established relationship between specification meanings.
    Semantic,
    /// A versioned support, defeat, or replacement judgment used by selection.
    Selection,
    /// A deterministic projection from an authored sentence or its grounding.
    Projection,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EndpointRole {
    /// Backward-compatible read of an Edge written before endpoint roles.
    #[default]
    Unspecified,
    Mentioner,
    MentionedTerm,
    Refiner,
    Refined,
    EquivalentPeer,
    ConflictPeer,
    Supporter,
    Supported,
    Defeater,
    Defeated,
    Superseder,
    Superseded,
    GroundedSpecification,
    Evidence,
    ContractSpecification,
    Assumption,
    Guarantee,
    RelianceEvidence,
    ReliantContract,
    DischargingGuarantee,
    DischargedContract,
    AdmissibleEnvironment,
    BoundedContract,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeKind {
    /// A specification contains one occurrence of a normalized term form.
    MentionsTerm,
    /// The source specification is the concrete refinement of the target.
    Refines,
    /// The two endpoint specifications state one same-force claim.
    Equivalent,
    /// Two binding specifications cannot both be satisfied as written.
    HardContradiction,
    /// Following a recommendation would violate the other specification.
    AdvisoryTension,
    /// A description conflicts with the other specification.
    DescriptiveConflict,
    /// A permission admits behavior forbidden by the other specification.
    EnvelopeConflict,
    /// The target contract explicitly relies on an occurrence/state supported
    /// by the source; `relied_spec_id` names the awaited assertion.
    OccurrenceReliance,
    /// The source guarantee discharges an assumption of the target contract.
    GuaranteeDischarge,
    /// The source permission bounds environment behavior tolerated by target.
    AdmissibilityEnvelope,
    /// The source supplies a versioned positive selection reason for target.
    Supports,
    /// The source wins a versioned, explicitly resolved competition with target.
    Defeats,
    /// The source is a versioned selected replacement for target.
    Supersedes,
    /// The target Evidence vertex grounds the source specification.
    GroundedBy,
    /// The target is the assumption side of the source specification's contract.
    HasAssumption,
    /// The target is the guarantee side of the source specification's contract.
    HasGuarantee,
}

impl EdgeKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MentionsTerm => "mentions_term",
            Self::Refines => "refines",
            Self::Equivalent => "equivalent",
            Self::HardContradiction => "hard_contradiction",
            Self::AdvisoryTension => "advisory_tension",
            Self::DescriptiveConflict => "descriptive_conflict",
            Self::EnvelopeConflict => "envelope_conflict",
            Self::OccurrenceReliance => "occurrence_reliance",
            Self::GuaranteeDischarge => "guarantee_discharge",
            Self::AdmissibilityEnvelope => "admissibility_envelope",
            Self::Supports => "supports",
            Self::Defeats => "defeats",
            Self::Supersedes => "supersedes",
            Self::GroundedBy => "grounded_by",
            Self::HasAssumption => "has_assumption",
            Self::HasGuarantee => "has_guarantee",
        }
    }

    pub fn family(self) -> EdgeFamily {
        match self {
            Self::MentionsTerm => EdgeFamily::Lexical,
            Self::Refines
            | Self::Equivalent
            | Self::HardContradiction
            | Self::AdvisoryTension
            | Self::DescriptiveConflict
            | Self::EnvelopeConflict
            | Self::OccurrenceReliance
            | Self::GuaranteeDischarge
            | Self::AdmissibilityEnvelope => EdgeFamily::Semantic,
            Self::Supports | Self::Defeats | Self::Supersedes => EdgeFamily::Selection,
            Self::GroundedBy | Self::HasAssumption | Self::HasGuarantee => EdgeFamily::Projection,
        }
    }

    pub fn endpoint_roles(self) -> (EndpointRole, EndpointRole) {
        match self {
            Self::MentionsTerm => (EndpointRole::Mentioner, EndpointRole::MentionedTerm),
            Self::Refines => (EndpointRole::Refiner, EndpointRole::Refined),
            Self::Equivalent => (EndpointRole::EquivalentPeer, EndpointRole::EquivalentPeer),
            Self::HardContradiction
            | Self::AdvisoryTension
            | Self::DescriptiveConflict
            | Self::EnvelopeConflict => (EndpointRole::ConflictPeer, EndpointRole::ConflictPeer),
            Self::OccurrenceReliance => (
                EndpointRole::RelianceEvidence,
                EndpointRole::ReliantContract,
            ),
            Self::GuaranteeDischarge => (
                EndpointRole::DischargingGuarantee,
                EndpointRole::DischargedContract,
            ),
            Self::AdmissibilityEnvelope => (
                EndpointRole::AdmissibleEnvironment,
                EndpointRole::BoundedContract,
            ),
            Self::Supports => (EndpointRole::Supporter, EndpointRole::Supported),
            Self::Defeats => (EndpointRole::Defeater, EndpointRole::Defeated),
            Self::Supersedes => (EndpointRole::Superseder, EndpointRole::Superseded),
            Self::GroundedBy => (EndpointRole::GroundedSpecification, EndpointRole::Evidence),
            Self::HasAssumption => (
                EndpointRole::ContractSpecification,
                EndpointRole::Assumption,
            ),
            Self::HasGuarantee => (EndpointRole::ContractSpecification, EndpointRole::Guarantee),
        }
    }

    /// Whether source/target order is part of this relationship's meaning.
    pub fn directed(self) -> bool {
        matches!(
            self,
            Self::MentionsTerm
                | Self::Refines
                | Self::OccurrenceReliance
                | Self::GuaranteeDischarge
                | Self::AdmissibilityEnvelope
                | Self::Supports
                | Self::Defeats
                | Self::Supersedes
                | Self::GroundedBy
                | Self::HasAssumption
                | Self::HasGuarantee
        )
    }
}

/// A stable pointer into the constrained sentence structure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextAnchor {
    /// JSON-pointer-like path in the serialized sentence AST.
    pub selector: String,
    /// Canonical text at that path. Raw specification words remain authority.
    pub text: String,
    /// Grammatical role such as `subject`, `object`, or `definition_term`.
    pub role: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Derivation {
    pub method: String,
    pub version: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edge {
    pub id: String,
    pub source: String,
    pub source_kind: VertexKind,
    #[serde(default)]
    pub source_role: EndpointRole,
    pub target: String,
    pub target_kind: VertexKind,
    #[serde(default)]
    pub target_role: EndpointRole,
    pub kind: EdgeKind,
    pub source_anchor: Option<TextAnchor>,
    pub target_anchor: Option<TextAnchor>,
    /// Authored specification whose assertion is the exact formula awaited by
    /// an assume-guarantee pairing. This is deliberately distinct from
    /// `source`: the source is evidence, while the relied specification says
    /// what the target actually assumes. Present only for pairing EdgeKinds.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub relied_spec_id: Option<String>,
    /// Specifications, beyond the endpoints, that make this connection
    /// checkable. Empty when the endpoints and anchored term incidence are the
    /// complete basis.
    pub basis_spec_ids: Vec<String>,
    pub derivation: Derivation,
    pub recorded_at: String,
}

impl Edge {
    /// Build a deterministic specification-to-derived-node projection.
    pub fn projection(
        kind: EdgeKind,
        specification: &str,
        target: &str,
        derivation: Derivation,
        recorded_at: &str,
    ) -> Result<Self, String> {
        let target_kind = match kind {
            EdgeKind::GroundedBy => VertexKind::Evidence,
            EdgeKind::HasAssumption => VertexKind::Assumption,
            EdgeKind::HasGuarantee => VertexKind::Guarantee,
            _ => return Err("projection construction requires a projection EdgeKind".into()),
        };
        let (source_role, target_role) = kind.endpoint_roles();
        let mut edge = Self {
            id: String::new(),
            source: specification.to_string(),
            source_kind: VertexKind::Specification,
            source_role,
            target: target.to_string(),
            target_kind,
            target_role,
            kind,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids: Vec::new(),
            derivation,
            recorded_at: recorded_at.to_string(),
        };
        edge.id = edge.identity_key();
        edge.validate()?;
        Ok(edge)
    }

    /// Build the current paired-assumption projection. Its specification
    /// basis names every authored source/relied Node used to derive the
    /// aggregate formula; a later pairing therefore appends a new projection
    /// without deleting the previous Ledger view.
    pub fn paired_assumption_projection(
        specification: &str,
        target: &str,
        mut basis_spec_ids: Vec<String>,
        derivation: Derivation,
        recorded_at: &str,
    ) -> Result<Self, String> {
        basis_spec_ids.sort();
        basis_spec_ids.dedup();
        let mut edge = Self::projection(
            EdgeKind::HasAssumption,
            specification,
            target,
            derivation,
            recorded_at,
        )?;
        edge.basis_spec_ids = basis_spec_ids;
        edge.id = edge.identity_key();
        edge.validate()?;
        Ok(edge)
    }

    /// Build a stable specification-to-specification relationship. Semantic
    /// and selection producers share this constructor so both families obey
    /// the same endpoint-role, symmetry, identity, and append-only rules.
    pub fn specification_relation(
        kind: EdgeKind,
        source: &str,
        target: &str,
        mut basis_spec_ids: Vec<String>,
        derivation: Derivation,
        recorded_at: &str,
    ) -> Result<Self, String> {
        if kind.family() == EdgeFamily::Lexical {
            return Err("lexical incidence requires anchored term construction".to_string());
        }
        if kind.is_pairing() {
            return Err(
                "assume-guarantee pairing requires an explicit relied specification".to_string(),
            );
        }
        let (source, target) = if !kind.directed() && source > target {
            (target, source)
        } else {
            (source, target)
        };
        basis_spec_ids.sort();
        basis_spec_ids.dedup();
        let (source_role, target_role) = kind.endpoint_roles();
        let mut edge = Self {
            id: String::new(),
            source: source.to_string(),
            source_kind: VertexKind::Specification,
            source_role,
            target: target.to_string(),
            target_kind: VertexKind::Specification,
            target_role,
            kind,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids,
            derivation,
            recorded_at: recorded_at.to_string(),
        };
        edge.id = edge.identity_key();
        edge.validate()?;
        Ok(edge)
    }

    /// Build a checked specification-to-specification assume-guarantee edge.
    /// The relied specification is part of the relationship identity because
    /// changing what the target awaits changes the contract, even when source
    /// and target remain the same.
    pub fn assumption_relation(
        kind: EdgeKind,
        source: &str,
        target: &str,
        relied_spec_id: &str,
        mut basis_spec_ids: Vec<String>,
        derivation: Derivation,
        recorded_at: &str,
    ) -> Result<Self, String> {
        if !kind.is_pairing() {
            return Err("assumption relation construction requires a pairing EdgeKind".into());
        }
        basis_spec_ids.sort();
        basis_spec_ids.dedup();
        let (source_role, target_role) = kind.endpoint_roles();
        let mut edge = Self {
            id: String::new(),
            source: source.to_string(),
            source_kind: VertexKind::Specification,
            source_role,
            target: target.to_string(),
            target_kind: VertexKind::Specification,
            target_role,
            kind,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: Some(relied_spec_id.to_string()),
            basis_spec_ids,
            derivation,
            recorded_at: recorded_at.to_string(),
        };
        edge.id = edge.identity_key();
        edge.validate()?;
        Ok(edge)
    }

    pub fn family(&self) -> EdgeFamily {
        self.kind.family()
    }

    /// Content identity for duplicate prevention. Recording time and a
    /// caller-provided `id` are deliberately excluded: neither changes the
    /// typed relationship being asserted.
    pub fn identity_key(&self) -> String {
        #[derive(Serialize)]
        struct Identity<'a> {
            source: &'a str,
            source_kind: VertexKind,
            source_role: EndpointRole,
            target: &'a str,
            target_kind: VertexKind,
            target_role: EndpointRole,
            kind: EdgeKind,
            source_anchor: &'a Option<TextAnchor>,
            target_anchor: &'a Option<TextAnchor>,
            relied_spec_id: &'a Option<String>,
            basis_spec_ids: Vec<&'a str>,
            derivation: &'a Derivation,
        }

        let mut basis_spec_ids: Vec<&str> =
            self.basis_spec_ids.iter().map(String::as_str).collect();
        basis_spec_ids.sort_unstable();
        basis_spec_ids.dedup();
        let identity = Identity {
            source: &self.source,
            source_kind: self.source_kind,
            source_role: self.source_role,
            target: &self.target,
            target_kind: self.target_kind,
            target_role: self.target_role,
            kind: self.kind,
            source_anchor: &self.source_anchor,
            target_anchor: &self.target_anchor,
            relied_spec_id: &self.relied_spec_id,
            basis_spec_ids,
            derivation: &self.derivation,
        };
        let bytes = serde_json::to_vec(&identity).expect("Edge identity serializes");
        let mut hasher = Sha256::new();
        hasher.update(b"edge");
        hasher.update([0]);
        hasher.update(bytes);
        format!("edge-{:x}", hasher.finalize())
    }

    /// Reject a newly written Edge whose physical endpoint order disagrees
    /// with the typed relationship it claims. Historical rows without roles
    /// remain deserializable, but no current producer may append another one.
    pub fn validate(&self) -> Result<(), String> {
        let expected_roles = self.kind.endpoint_roles();
        let actual_roles = (self.source_role, self.target_role);
        if actual_roles != expected_roles {
            return Err(format!(
                "{} requires endpoint roles {:?}, got {:?}",
                self.kind.as_str(),
                expected_roles,
                actual_roles
            ));
        }

        let expected_vertices = match self.kind {
            EdgeKind::MentionsTerm => (VertexKind::Specification, VertexKind::Term),
            EdgeKind::GroundedBy => (VertexKind::Specification, VertexKind::Evidence),
            EdgeKind::HasAssumption => (VertexKind::Specification, VertexKind::Assumption),
            EdgeKind::HasGuarantee => (VertexKind::Specification, VertexKind::Guarantee),
            _ => (VertexKind::Specification, VertexKind::Specification),
        };
        let actual_vertices = (self.source_kind, self.target_kind);
        if actual_vertices != expected_vertices {
            return Err(format!(
                "{} requires endpoint vertex kinds {:?}, got {:?}",
                self.kind.as_str(),
                expected_vertices,
                actual_vertices
            ));
        }

        if !self.kind.directed() && self.source > self.target {
            return Err(format!(
                "symmetric {} endpoints must be canonically ordered",
                self.kind.as_str()
            ));
        }
        if self.kind.is_pairing() != self.relied_spec_id.is_some() {
            return Err(format!(
                "{} {} an explicit relied specification",
                self.kind.as_str(),
                if self.kind.is_pairing() {
                    "requires"
                } else {
                    "forbids"
                }
            ));
        }
        Ok(())
    }

    /// Specification-page owner used by the paginated current graph view.
    ///
    /// Lexical mentions belong to their mentioner. A specification-to-
    /// specification Edge belongs to the lexically smaller endpoint,
    /// independently of its typed argument order, so a complete Node-page walk
    /// returns every Edge exactly once even when endpoints span pages.
    pub fn page_owner(&self) -> &str {
        if self.target_kind != VertexKind::Specification || self.source <= self.target {
            &self.source
        } else {
            &self.target
        }
    }
}

impl EdgeKind {
    pub fn is_pairing(self) -> bool {
        matches!(
            self,
            Self::OccurrenceReliance | Self::GuaranteeDischarge | Self::AdmissibilityEnvelope
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edge(kind: EdgeKind) -> Edge {
        let (source_role, target_role) = kind.endpoint_roles();
        let (source_kind, target_kind) = if kind == EdgeKind::MentionsTerm {
            (VertexKind::Specification, VertexKind::Term)
        } else {
            (VertexKind::Specification, VertexKind::Specification)
        };
        Edge {
            id: "edge".into(),
            source: "a".into(),
            source_kind,
            source_role,
            target: "b".into(),
            target_kind,
            target_role,
            kind,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: kind.is_pairing().then(|| "relied".into()),
            basis_spec_ids: Vec::new(),
            derivation: Derivation {
                method: "test".into(),
                version: "1".into(),
            },
            recorded_at: "t".into(),
        }
    }

    #[test]
    fn every_edge_kind_has_one_family_and_endpoint_role_pair() {
        let cases = [
            (EdgeKind::MentionsTerm, EdgeFamily::Lexical),
            (EdgeKind::Refines, EdgeFamily::Semantic),
            (EdgeKind::Equivalent, EdgeFamily::Semantic),
            (EdgeKind::HardContradiction, EdgeFamily::Semantic),
            (EdgeKind::AdvisoryTension, EdgeFamily::Semantic),
            (EdgeKind::DescriptiveConflict, EdgeFamily::Semantic),
            (EdgeKind::EnvelopeConflict, EdgeFamily::Semantic),
            (EdgeKind::OccurrenceReliance, EdgeFamily::Semantic),
            (EdgeKind::GuaranteeDischarge, EdgeFamily::Semantic),
            (EdgeKind::AdmissibilityEnvelope, EdgeFamily::Semantic),
            (EdgeKind::Supports, EdgeFamily::Selection),
            (EdgeKind::Defeats, EdgeFamily::Selection),
            (EdgeKind::Supersedes, EdgeFamily::Selection),
            (EdgeKind::GroundedBy, EdgeFamily::Projection),
            (EdgeKind::HasAssumption, EdgeFamily::Projection),
            (EdgeKind::HasGuarantee, EdgeFamily::Projection),
        ];
        for (kind, family) in cases {
            let edge = if family == EdgeFamily::Projection {
                Edge::projection(
                    kind,
                    "a",
                    "b",
                    Derivation {
                        method: "test".into(),
                        version: "1".into(),
                    },
                    "t",
                )
                .unwrap()
            } else {
                edge(kind)
            };
            assert_eq!(edge.family(), family);
            edge.validate().unwrap();
        }
    }

    #[test]
    fn storage_rejects_a_direction_that_disagrees_with_endpoint_roles() {
        let mut edge = edge(EdgeKind::Refines);
        edge.source_role = EndpointRole::Refined;
        edge.target_role = EndpointRole::Refiner;
        assert!(edge.validate().unwrap_err().contains("endpoint roles"));
    }

    #[test]
    fn selection_relation_identity_is_versioned_and_role_safe() {
        let first = Edge::specification_relation(
            EdgeKind::Supports,
            "evidence-spec",
            "supported-spec",
            vec!["basis-b".into(), "basis-a".into(), "basis-a".into()],
            Derivation {
                method: "selection-policy".into(),
                version: "v1".into(),
            },
            "t1",
        )
        .unwrap();
        let next = Edge::specification_relation(
            EdgeKind::Supports,
            "evidence-spec",
            "supported-spec",
            vec!["basis-a".into(), "basis-b".into()],
            Derivation {
                method: "selection-policy".into(),
                version: "v2".into(),
            },
            "t2",
        )
        .unwrap();
        assert_eq!(first.source_role, EndpointRole::Supporter);
        assert_eq!(first.target_role, EndpointRole::Supported);
        assert_eq!(first.basis_spec_ids, ["basis-a", "basis-b"]);
        assert_ne!(first.id, next.id);
    }
}
