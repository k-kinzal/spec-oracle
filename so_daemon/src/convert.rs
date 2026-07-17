//! Conversions between the serde domain types and the generated protobuf
//! messages ([`so_protocol::pb`]).
//!
//! The two representations are kept deliberately separate: the domain types are
//! the serde model the daemon persists; the protobuf messages are the wire
//! form. This module is the single place that maps one to the other.
//!
//! Graph-read Domain → proto ([`node_to_pb`]) also *derives* the wire-only
//! [`pb::SentenceView`] — speech act, canonical rendering, contract view — by
//! re-parsing the node's raw sentence with the language crate. The view is
//! computed at response time using `so-lang` parsing plus `so-reason`
//! interpretation and never persisted; if the re-parse impossibly
//! fails (e.g. a row accepted by an older grammar), the view is simply absent —
//! degrade, never panic. The Add response uses [`accepted_node_to_pb`] and
//! returns stored facts only. Proto → domain is fallible ([`TryFrom`]) because a
//! message received off the wire may omit a required field or oneof arm; the
//! derived `sentence` view is ignored on receive.

use crate::domain;
use so_protocol::pb;
use so_reason::semantics;

/// A malformed wire message: a required field or oneof arm was absent.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum ConvertError {
    #[error("missing required field on the wire: {0}")]
    MissingField(&'static str),
    #[error("invalid JSON in wire field {field}: {message}")]
    InvalidJson {
        field: &'static str,
        message: String,
    },
}

// ---- Kind ------------------------------------------------------------------

fn kind_to_pb(k: domain::Kind) -> pb::Kind {
    match k {
        domain::Kind::Constitutive => pb::Kind::Constitutive,
        domain::Kind::Demonstrative => pb::Kind::Demonstrative,
        domain::Kind::Testimonial => pb::Kind::Testimonial,
        domain::Kind::Assertoric => pb::Kind::Assertoric,
        domain::Kind::Circumstantial => pb::Kind::Circumstantial,
        domain::Kind::Counter => pb::Kind::Counter,
        domain::Kind::Unknown => pb::Kind::Unknown,
    }
}

fn kind_from_pb(v: i32) -> domain::Kind {
    // Unspecified (the proto3 default) and any unrecognized number degrade to
    // Unknown — an absent kind is never load-bearing.
    match pb::Kind::try_from(v).unwrap_or(pb::Kind::Unspecified) {
        pb::Kind::Constitutive => domain::Kind::Constitutive,
        pb::Kind::Demonstrative => domain::Kind::Demonstrative,
        pb::Kind::Testimonial => domain::Kind::Testimonial,
        pb::Kind::Assertoric => domain::Kind::Assertoric,
        pb::Kind::Circumstantial => domain::Kind::Circumstantial,
        pb::Kind::Counter => domain::Kind::Counter,
        pb::Kind::Unknown | pb::Kind::Unspecified => domain::Kind::Unknown,
    }
}

// ---- SentenceView (derived, wire-only) ---------------------------------------

fn speech_act_to_pb(act: semantics::SpeechAct) -> pb::SpeechAct {
    match act {
        semantics::SpeechAct::Definition => pb::SpeechAct::Definition,
        semantics::SpeechAct::Description => pb::SpeechAct::Description,
        semantics::SpeechAct::Obligation => pb::SpeechAct::Obligation,
        semantics::SpeechAct::Prohibition => pb::SpeechAct::Prohibition,
        semantics::SpeechAct::Recommendation => pb::SpeechAct::Recommendation,
        semantics::SpeechAct::Permission => pb::SpeechAct::Permission,
    }
}

/// Derive the wire-only sentence view from a node's raw sentence text.
/// `None` when the text does not (re-)parse as exactly one sentence — a row
/// from an older grammar degrades to a view-less node rather than an error.
fn sentence_view(statement: &str) -> Option<pb::SentenceView> {
    let specification = so_lang::parse::parse(statement).ok()?;
    let sentence = match specification.sentences.as_slice() {
        [sentence] => sentence,
        _ => return None,
    };
    let contract = semantics::ingest_contract(sentence).map(|ic| {
        // The guarantee is the assertion: the canonical sentence without its
        // purpose adjunct (a purpose is intent, not behavior).
        let mut assertion = sentence.clone();
        assertion.purpose = None;
        pb::ContractView {
            assumption: ic.assumption.render().to_string(),
            guarantee: assertion.render(),
            force: match ic.force {
                Some(semantics::Force::Binding) => "binding".to_string(),
                Some(semantics::Force::Recommended) => "recommended".to_string(),
                None => String::new(),
            },
        }
    });
    Some(pb::SentenceView {
        speech_act: speech_act_to_pb(semantics::speech_act(sentence)) as i32,
        canonical: sentence.render(),
        contract,
    })
}

// ---- Edge ------------------------------------------------------------------

fn edge_kind_to_pb(k: domain::EdgeKind) -> pb::EdgeKind {
    match k {
        domain::EdgeKind::MentionsTerm => pb::EdgeKind::MentionsTerm,
        domain::EdgeKind::Refines => pb::EdgeKind::Refines,
        domain::EdgeKind::Equivalent => pb::EdgeKind::Equivalent,
        domain::EdgeKind::HardContradiction => pb::EdgeKind::HardContradiction,
        domain::EdgeKind::AdvisoryTension => pb::EdgeKind::AdvisoryTension,
        domain::EdgeKind::DescriptiveConflict => pb::EdgeKind::DescriptiveConflict,
        domain::EdgeKind::EnvelopeConflict => pb::EdgeKind::EnvelopeConflict,
        domain::EdgeKind::OccurrenceReliance => pb::EdgeKind::OccurrenceReliance,
        domain::EdgeKind::GuaranteeDischarge => pb::EdgeKind::GuaranteeDischarge,
        domain::EdgeKind::AdmissibilityEnvelope => pb::EdgeKind::AdmissibilityEnvelope,
        domain::EdgeKind::Supports => pb::EdgeKind::Supports,
        domain::EdgeKind::Defeats => pb::EdgeKind::Defeats,
        domain::EdgeKind::Supersedes => pb::EdgeKind::Supersedes,
        domain::EdgeKind::GroundedBy => pb::EdgeKind::GroundedBy,
        domain::EdgeKind::HasAssumption => pb::EdgeKind::HasAssumption,
        domain::EdgeKind::HasGuarantee => pb::EdgeKind::HasGuarantee,
        domain::EdgeKind::HasContract => pb::EdgeKind::HasContract,
        domain::EdgeKind::ContractRefines => pb::EdgeKind::ContractRefines,
        domain::EdgeKind::ContractEquivalent => pb::EdgeKind::ContractEquivalent,
        domain::EdgeKind::CompositionOperand => pb::EdgeKind::CompositionOperand,
        domain::EdgeKind::QuotientDividend => pb::EdgeKind::QuotientDividend,
        domain::EdgeKind::QuotientDivisor => pb::EdgeKind::QuotientDivisor,
        domain::EdgeKind::MergeOperand => pb::EdgeKind::MergeOperand,
    }
}

fn edge_family_to_pb(family: domain::EdgeFamily) -> pb::EdgeFamily {
    match family {
        domain::EdgeFamily::Lexical => pb::EdgeFamily::Lexical,
        domain::EdgeFamily::Semantic => pb::EdgeFamily::Semantic,
        domain::EdgeFamily::Selection => pb::EdgeFamily::Selection,
        domain::EdgeFamily::Projection => pb::EdgeFamily::Projection,
    }
}

fn endpoint_role_to_pb(role: domain::EndpointRole) -> pb::EdgeEndpointRole {
    match role {
        domain::EndpointRole::Unspecified => pb::EdgeEndpointRole::Unspecified,
        domain::EndpointRole::Mentioner => pb::EdgeEndpointRole::Mentioner,
        domain::EndpointRole::MentionedTerm => pb::EdgeEndpointRole::MentionedTerm,
        domain::EndpointRole::Refiner => pb::EdgeEndpointRole::Refiner,
        domain::EndpointRole::Refined => pb::EdgeEndpointRole::Refined,
        domain::EndpointRole::EquivalentPeer => pb::EdgeEndpointRole::EquivalentPeer,
        domain::EndpointRole::ConflictPeer => pb::EdgeEndpointRole::ConflictPeer,
        domain::EndpointRole::Supporter => pb::EdgeEndpointRole::Supporter,
        domain::EndpointRole::Supported => pb::EdgeEndpointRole::Supported,
        domain::EndpointRole::Defeater => pb::EdgeEndpointRole::Defeater,
        domain::EndpointRole::Defeated => pb::EdgeEndpointRole::Defeated,
        domain::EndpointRole::Superseder => pb::EdgeEndpointRole::Superseder,
        domain::EndpointRole::Superseded => pb::EdgeEndpointRole::Superseded,
        domain::EndpointRole::GroundedSpecification => pb::EdgeEndpointRole::GroundedSpecification,
        domain::EndpointRole::Evidence => pb::EdgeEndpointRole::Evidence,
        domain::EndpointRole::ContractSpecification => pb::EdgeEndpointRole::ContractSpecification,
        domain::EndpointRole::Assumption => pb::EdgeEndpointRole::Assumption,
        domain::EndpointRole::Guarantee => pb::EdgeEndpointRole::Guarantee,
        domain::EndpointRole::RelianceEvidence => pb::EdgeEndpointRole::RelianceEvidence,
        domain::EndpointRole::ReliantContract => pb::EdgeEndpointRole::ReliantContract,
        domain::EndpointRole::DischargingGuarantee => pb::EdgeEndpointRole::DischargingGuarantee,
        domain::EndpointRole::DischargedContract => pb::EdgeEndpointRole::DischargedContract,
        domain::EndpointRole::AdmissibleEnvironment => pb::EdgeEndpointRole::AdmissibleEnvironment,
        domain::EndpointRole::BoundedContract => pb::EdgeEndpointRole::BoundedContract,
        domain::EndpointRole::Contract => pb::EdgeEndpointRole::Contract,
        domain::EndpointRole::ContractRefiner => pb::EdgeEndpointRole::ContractRefiner,
        domain::EndpointRole::ContractRefined => pb::EdgeEndpointRole::ContractRefined,
        domain::EndpointRole::EquivalentContract => pb::EdgeEndpointRole::EquivalentContract,
        domain::EndpointRole::CompositionOperand => pb::EdgeEndpointRole::CompositionOperand,
        domain::EndpointRole::CompositionResult => pb::EdgeEndpointRole::CompositionResult,
        domain::EndpointRole::QuotientDividend => pb::EdgeEndpointRole::QuotientDividend,
        domain::EndpointRole::QuotientDivisor => pb::EdgeEndpointRole::QuotientDivisor,
        domain::EndpointRole::QuotientResult => pb::EdgeEndpointRole::QuotientResult,
        domain::EndpointRole::MergeOperand => pb::EdgeEndpointRole::MergeOperand,
        domain::EndpointRole::MergeResult => pb::EdgeEndpointRole::MergeResult,
    }
}

fn vertex_kind_to_pb(kind: domain::VertexKind) -> pb::VertexKind {
    match kind {
        domain::VertexKind::Specification => pb::VertexKind::Specification,
        domain::VertexKind::Term => pb::VertexKind::Term,
        domain::VertexKind::Evidence => pb::VertexKind::Evidence,
        domain::VertexKind::Assumption => pb::VertexKind::Assumption,
        domain::VertexKind::Guarantee => pb::VertexKind::Guarantee,
        domain::VertexKind::Contract => pb::VertexKind::Contract,
    }
}

fn text_anchor_to_pb(anchor: &domain::TextAnchor) -> pb::TextAnchor {
    pb::TextAnchor {
        selector: anchor.selector.clone(),
        text: anchor.text.clone(),
        role: anchor.role.clone(),
    }
}

/// Convert a derived edge to its wire form. Symmetric `from_pb` is deliberately
/// absent: nothing receives edges into the domain yet — they are derived, not
/// ingested — so that direction attaches with edge derivation.
pub fn edge_to_pb(e: &domain::Edge) -> pb::Edge {
    edge_to_pb_with_current(e, true)
}

pub fn edge_to_pb_with_current(e: &domain::Edge, current: bool) -> pb::Edge {
    pb::Edge {
        id: e.id.clone(),
        source: e.source.clone(),
        target: e.target.clone(),
        kind: edge_kind_to_pb(e.kind) as i32,
        source_kind: vertex_kind_to_pb(e.source_kind) as i32,
        target_kind: vertex_kind_to_pb(e.target_kind) as i32,
        source_anchor: e.source_anchor.as_ref().map(text_anchor_to_pb),
        target_anchor: e.target_anchor.as_ref().map(text_anchor_to_pb),
        basis_spec_ids: e.basis_spec_ids.clone(),
        derivation: Some(pb::Derivation {
            method: e.derivation.method.clone(),
            version: e.derivation.version.clone(),
        }),
        recorded_at: e.recorded_at.clone(),
        family: edge_family_to_pb(e.family()) as i32,
        source_role: endpoint_role_to_pb(e.source_role) as i32,
        target_role: endpoint_role_to_pb(e.target_role) as i32,
        relied_spec_id: e.relied_spec_id.clone(),
        current,
    }
}

pub fn term_node_to_pb(term: &domain::TermNode) -> pb::TermNode {
    pb::TermNode {
        id: term.id.clone(),
        form: term.form.clone(),
        head: term.head.clone(),
        lang_version: term.lang_version.clone(),
        derivation_version: term.derivation_version.clone(),
    }
}

pub fn derived_node_to_pb(node: &domain::DerivedNode) -> pb::DerivedNode {
    let (id, value) = match node {
        domain::DerivedNode::Evidence { id, evidence } => (
            id.clone(),
            pb::derived_node::Value::Evidence(pb::EvidenceNode {
                evidence: Some(evidence_to_pb(evidence)),
            }),
        ),
        domain::DerivedNode::Assumption {
            id,
            expression,
            formula_json,
            derivation_version,
        } => (
            id.clone(),
            pb::derived_node::Value::Assumption(pb::AssumptionNode {
                expression: expression.clone(),
                derivation_version: derivation_version.clone(),
                formula_json: formula_json.clone(),
            }),
        ),
        domain::DerivedNode::Guarantee {
            id,
            expression,
            force,
            formula_json,
            derivation_version,
        } => (
            id.clone(),
            pb::derived_node::Value::Guarantee(pb::GuaranteeNode {
                expression: expression.clone(),
                force: force.clone(),
                derivation_version: derivation_version.clone(),
                formula_json: formula_json.clone(),
            }),
        ),
        domain::DerivedNode::Contract {
            id,
            assumption_json,
            guarantee_json,
            interface_json,
            operation,
            derivation_version,
        } => (
            id.clone(),
            pb::derived_node::Value::Contract(pb::ContractNode {
                assumption_json: assumption_json.clone(),
                guarantee_json: guarantee_json.clone(),
                interface_json: interface_json.clone(),
                operation: operation.clone(),
                derivation_version: derivation_version.clone(),
            }),
        ),
    };
    pb::DerivedNode {
        id,
        value: Some(value),
    }
}

pub fn relation_assessment_to_pb(
    assessment: &domain::RelationAssessment,
) -> pb::RelationAssessment {
    use domain::AssessmentOutcome as Outcome;
    let mut wire = pb::RelationAssessment {
        id: assessment.id.clone(),
        left: assessment.left.clone(),
        right: assessment.right.clone(),
        candidate_derivation: Some(pb::Derivation {
            method: assessment.candidate_derivation.method.clone(),
            version: assessment.candidate_derivation.version.clone(),
        }),
        semantic_derivation: Some(pb::Derivation {
            method: assessment.semantic_derivation.method.clone(),
            version: assessment.semantic_derivation.version.clone(),
        }),
        recorded_at: assessment.recorded_at.clone(),
        ..Default::default()
    };
    wire.kind = match &assessment.outcome {
        Outcome::Refines {
            concrete,
            abstract_,
        } => {
            wire.concrete = Some(concrete.clone());
            wire.r#abstract = Some(abstract_.clone());
            pb::AssessmentKind::Refines
        }
        Outcome::Equivalent => pb::AssessmentKind::Equivalent,
        Outcome::HardContradiction => pb::AssessmentKind::HardContradiction,
        Outcome::AdvisoryTension => pb::AssessmentKind::AdvisoryTension,
        Outcome::DescriptiveConflict => pb::AssessmentKind::DescriptiveConflict,
        Outcome::EnvelopeConflict => pb::AssessmentKind::EnvelopeConflict,
        Outcome::Independent => pb::AssessmentKind::Independent,
        Outcome::Unknown => pb::AssessmentKind::Unknown,
        Outcome::FormulaEntails {
            antecedent,
            consequence,
        } => {
            wire.antecedent = Some(antecedent.clone());
            wire.consequence = Some(consequence.clone());
            pb::AssessmentKind::FormulaEntails
        }
        Outcome::FormulaEquivalent => pb::AssessmentKind::FormulaEquivalent,
        Outcome::FormulaContradiction => pb::AssessmentKind::FormulaContradiction,
        Outcome::FormulaUnknown => pb::AssessmentKind::FormulaUnknown,
        Outcome::ContractRefines {
            concrete,
            abstract_,
        } => {
            wire.concrete = Some(concrete.clone());
            wire.r#abstract = Some(abstract_.clone());
            pb::AssessmentKind::ContractRefines
        }
        Outcome::ContractEquivalent => pb::AssessmentKind::ContractEquivalent,
        Outcome::ContractIncomparable => pb::AssessmentKind::ContractIncomparable,
        Outcome::DischargeCandidate {
            source,
            target,
            relied_spec_id,
        } => {
            wire.source = Some(source.clone());
            wire.target = Some(target.clone());
            wire.relied_spec_id = Some(relied_spec_id.clone());
            pb::AssessmentKind::DischargeCandidate
        }
    } as i32;
    wire
}

// ---- Locator ---------------------------------------------------------------

fn locator_to_pb(l: &domain::Locator) -> pb::Locator {
    let value = match l {
        domain::Locator::File { path, line, col } => pb::locator::Value::File(pb::FileLocator {
            path: path.clone(),
            line: *line,
            col: *col,
        }),
        domain::Locator::Url { url } => {
            pb::locator::Value::Url(pb::UrlLocator { url: url.clone() })
        }
    };
    pb::Locator { value: Some(value) }
}

fn locator_from_pb(l: pb::Locator) -> Result<domain::Locator, ConvertError> {
    match l.value.ok_or(ConvertError::MissingField("locator.value"))? {
        pb::locator::Value::File(f) => Ok(domain::Locator::File {
            path: f.path,
            line: f.line,
            col: f.col,
        }),
        pb::locator::Value::Url(u) => Ok(domain::Locator::Url { url: u.url }),
    }
}

// ---- Snapshot / Anchor -----------------------------------------------------

fn anchor_to_pb(a: &domain::Anchor) -> pb::Anchor {
    let value = match a {
        domain::Anchor::Git { commit, dirty } => pb::anchor::Value::Git(pb::GitAnchor {
            commit: commit.clone(),
            dirty: *dirty,
        }),
        domain::Anchor::Worktree => pb::anchor::Value::Worktree(pb::WorktreeAnchor {}),
        domain::Anchor::Web {
            retrieved_at,
            status,
            content_type,
            last_modified,
        } => pb::anchor::Value::Web(pb::WebAnchor {
            retrieved_at: retrieved_at.clone(),
            status: *status as u32,
            content_type: content_type.clone(),
            last_modified: last_modified.clone(),
        }),
    };
    pb::Anchor { value: Some(value) }
}

fn anchor_from_pb(a: pb::Anchor) -> Result<domain::Anchor, ConvertError> {
    match a.value.ok_or(ConvertError::MissingField("anchor.value"))? {
        pb::anchor::Value::Git(g) => Ok(domain::Anchor::Git {
            commit: g.commit,
            dirty: g.dirty,
        }),
        pb::anchor::Value::Worktree(_) => Ok(domain::Anchor::Worktree),
        pb::anchor::Value::Web(w) => Ok(domain::Anchor::Web {
            retrieved_at: w.retrieved_at,
            status: w.status as u16,
            content_type: w.content_type,
            last_modified: w.last_modified,
        }),
    }
}

fn snapshot_to_pb(s: &domain::Snapshot) -> pb::Snapshot {
    // The captured bytes (`content`) are intentionally not carried on the wire —
    // the blob store is the byte authority.
    pb::Snapshot {
        content_hash: s.content_hash.clone(),
        bytes: s.bytes as u64,
        captured_at: s.captured_at.clone(),
        anchor: Some(anchor_to_pb(&s.anchor)),
    }
}

fn snapshot_from_pb(s: pb::Snapshot) -> Result<domain::Snapshot, ConvertError> {
    Ok(domain::Snapshot {
        // Content is not on the wire; a received node has empty content.
        content: String::new(),
        content_hash: s.content_hash,
        bytes: s.bytes as usize,
        captured_at: s.captured_at,
        anchor: anchor_from_pb(
            s.anchor
                .ok_or(ConvertError::MissingField("snapshot.anchor"))?,
        )?,
    })
}

// ---- Origin ----------------------------------------------------------------

fn origin_to_pb(o: &domain::Origin) -> pb::Origin {
    pb::Origin {
        author: o.author.clone(),
        created_at: o.created_at.clone(),
        updated_at: o.updated_at.clone(),
    }
}

fn origin_from_pb(o: pb::Origin) -> domain::Origin {
    domain::Origin {
        author: o.author,
        created_at: o.created_at,
        updated_at: o.updated_at,
    }
}

// ---- Evidence / Meta -------------------------------------------------------

fn evidence_to_pb(e: &domain::Evidence) -> pb::Evidence {
    pb::Evidence {
        kind: kind_to_pb(e.kind) as i32,
        locator: Some(locator_to_pb(&e.locator)),
        snapshot: Some(snapshot_to_pb(&e.snapshot)),
        origin: Some(origin_to_pb(&e.origin)),
    }
}

fn evidence_from_pb(e: pb::Evidence) -> Result<domain::Evidence, ConvertError> {
    Ok(domain::Evidence {
        kind: kind_from_pb(e.kind),
        locator: locator_from_pb(
            e.locator
                .ok_or(ConvertError::MissingField("evidence.locator"))?,
        )?,
        snapshot: snapshot_from_pb(
            e.snapshot
                .ok_or(ConvertError::MissingField("evidence.snapshot"))?,
        )?,
        origin: e.origin.map(origin_from_pb).unwrap_or_default(),
    })
}

fn meta_to_pb(m: &domain::Meta) -> pb::Meta {
    pb::Meta {
        evidence_requests: m.evidence_requests.clone(),
        evidence_request_generation: m.evidence_request_generation.clone(),
        evidence: m.evidence.iter().map(evidence_to_pb).collect(),
        created_at: m.created_at.clone(),
        cli: m.cli.clone(),
        cli_version: m.cli_version.clone(),
        updates: m
            .updates
            .iter()
            .map(|(id, update)| pb::MetaUpdate {
                id: id.clone(),
                source: update.source.clone(),
                applied_at: update.applied_at.clone(),
                value_json: update.value.to_string(),
            })
            .collect(),
    }
}

fn meta_from_pb(m: pb::Meta) -> Result<domain::Meta, ConvertError> {
    Ok(domain::Meta {
        evidence_requests: m.evidence_requests,
        evidence_request_generation: m.evidence_request_generation,
        evidence: m
            .evidence
            .into_iter()
            .map(evidence_from_pb)
            .collect::<Result<Vec<_>, _>>()?,
        created_at: m.created_at,
        cli: m.cli,
        cli_version: m.cli_version,
        updates: m
            .updates
            .into_iter()
            .map(|update| {
                let value = serde_json::from_str(&update.value_json).map_err(|error| {
                    ConvertError::InvalidJson {
                        field: "meta.updates.value_json",
                        message: error.to_string(),
                    }
                })?;
                Ok((
                    update.id,
                    domain::MetaUpdate {
                        source: update.source,
                        applied_at: update.applied_at,
                        value,
                    },
                ))
            })
            .collect::<Result<_, ConvertError>>()?,
    })
}

// ---- Node ------------------------------------------------------------------

/// Convert a persisted node to its wire form, deriving the response-time
/// [`pb::SentenceView`] from the raw sentence text.
pub fn node_to_pb(n: &domain::Node) -> pb::Node {
    node_to_pb_with_sentence(n, sentence_view(&n.statement))
}

/// Add-RPC conversion: the synchronous boundary returns stored facts only.
/// Meaning interpretation is deliberately absent from the acceptance path.
pub fn accepted_node_to_pb(n: &domain::Node) -> pb::Node {
    node_to_pb_with_sentence(n, None)
}

pub fn node_to_pb_with_selection(n: &domain::Node, selection: &domain::SelectionView) -> pb::Node {
    let mut node = node_to_pb(n);
    node.selection = Some(pb::SelectionView {
        current: selection.current(),
        supporting_edge_ids: selection.supporting_edge_ids.clone(),
        defeating_edge_ids: selection.defeating_edge_ids.clone(),
        superseding_edge_ids: selection.superseding_edge_ids.clone(),
        policy_version: selection.policy_version.clone(),
        support_score: selection.support_score,
        evidence_score: selection.evidence_score,
        relation_score: selection.relation_score,
        contributions: selection
            .contributions
            .iter()
            .map(|contribution| pb::ScoreContribution {
                kind: contribution.kind.as_str().into(),
                points: contribution.points,
                edge_id: contribution.edge_id.clone(),
                source_node_id: contribution.source_node_id.clone(),
                evidence_node_id: contribution.evidence_node_id.clone(),
                detail: contribution.detail.clone(),
            })
            .collect(),
        exclusions: selection
            .exclusions
            .iter()
            .map(|exclusion| pb::SelectionExclusion {
                kind: exclusion.kind.as_str().into(),
                edge_id: exclusion.edge_id.clone(),
                competing_node_id: exclusion.competing_node_id.clone(),
                detail: exclusion.detail.clone(),
            })
            .collect(),
    });
    node
}

fn node_to_pb_with_sentence(n: &domain::Node, sentence: Option<pb::SentenceView>) -> pb::Node {
    pb::Node {
        id: n.id.clone(),
        statement: n.statement.clone(),
        lang_version: n.lang_version.clone(),
        sentence,
        meta: Some(meta_to_pb(&n.meta)),
        selection: None,
    }
}

impl TryFrom<pb::Node> for domain::Node {
    type Error = ConvertError;

    /// Only the stored truth crosses back: id, statement, lang_version, meta.
    /// The `sentence` view is derived — ignored on receive.
    fn try_from(n: pb::Node) -> Result<domain::Node, ConvertError> {
        Ok(domain::Node {
            id: n.id,
            statement: n.statement,
            lang_version: n.lang_version,
            meta: meta_from_pb(n.meta.ok_or(ConvertError::MissingField("node.meta"))?)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{
        Anchor, Evidence, Kind, Locator, Meta, MetaUpdate, Node, Origin, Snapshot,
    };

    fn sample() -> Node {
        Node {
            id: "n1".into(),
            statement: "When the order ships, the system shall notify the customer.".into(),
            lang_version: so_lang::LANG_VERSION.into(),
            meta: Meta {
                evidence_requests: vec!["src/x.rs:3:7".into()],
                evidence_request_generation: String::new(),
                evidence: vec![
                    Evidence {
                        kind: Kind::Constitutive,
                        locator: Locator::File {
                            path: "src/x.rs".into(),
                            line: Some(3),
                            col: Some(7),
                        },
                        snapshot: Snapshot {
                            content: "bytes not on wire".into(),
                            content_hash: "deadbeef".into(),
                            bytes: 17,
                            captured_at: "2026-07-05T00:00:00Z".into(),
                            anchor: Anchor::Git {
                                commit: "abc123".into(),
                                dirty: true,
                            },
                        },
                        origin: Origin {
                            author: Some("jane".into()),
                            created_at: None,
                            updated_at: Some("2026-01-01T00:00:00Z".into()),
                        },
                    },
                    Evidence {
                        kind: Kind::Unknown,
                        locator: Locator::Url {
                            url: "https://e.com/x".into(),
                        },
                        snapshot: Snapshot {
                            content: "body".into(),
                            content_hash: "cafe".into(),
                            bytes: 4,
                            captured_at: "t".into(),
                            anchor: Anchor::Web {
                                retrieved_at: "t".into(),
                                status: 200,
                                content_type: Some("text/html".into()),
                                last_modified: None,
                            },
                        },
                        origin: Origin::default(),
                    },
                ],
                created_at: "2026-07-05T00:00:00Z".into(),
                cli: "spec".into(),
                cli_version: "test".into(),
                updates: [(
                    "job-1".to_string(),
                    MetaUpdate {
                        source: "example".to_string(),
                        applied_at: "2026-07-11T00:00:00Z".to_string(),
                        value: serde_json::json!({"commit": "abc123"}),
                    },
                )]
                .into(),
            },
        }
    }

    #[test]
    fn node_round_trips_through_proto_dropping_only_content() {
        let node = sample();
        let wire = node_to_pb(&node);
        let back = Node::try_from(wire).unwrap();

        // Content is not carried on the wire; everything else is identical.
        let mut expected = node.clone();
        for ev in &mut expected.meta.evidence {
            ev.snapshot.content = String::new();
        }
        assert_eq!(back, expected);
    }

    #[test]
    fn sentence_view_is_derived_for_an_obligation() {
        let wire = node_to_pb(&sample());
        let view = wire.sentence.expect("view must be derived");
        assert_eq!(view.speech_act, pb::SpeechAct::Obligation as i32);
        assert_eq!(
            view.canonical,
            "When the order ships, the system shall notify the customer."
        );
        let contract = view.contract.expect("obligations have a contract view");
        assert_eq!(contract.assumption, "⊤");
        assert_eq!(contract.force, "binding");
    }

    #[test]
    fn accepted_node_wire_view_contains_only_stored_facts() {
        let wire = accepted_node_to_pb(&sample());
        assert!(wire.sentence.is_none());
        assert_eq!(
            wire.meta.unwrap().evidence_requests,
            ["src/x.rs:3:7".to_string()]
        );
    }

    #[test]
    fn contract_guarantee_omits_the_purpose_adjunct() {
        let mut node = sample();
        // Round 11 (fail-closed verb boundary): `stays live` was a
        // boundary-less bare run — the ambiguous class — so the purpose
        // clause is copular now (`remains` is a clause copula).
        node.statement =
            "The daemon shall persist the node, so that the claim remains live.".into();
        let view = node_to_pb(&node).sentence.unwrap();
        let contract = view.contract.unwrap();
        // Closed-class words render in canonical (lowercase) casing.
        assert_eq!(contract.guarantee, "the daemon shall persist the node.");
        // The canonical rendering keeps the purpose; only the guarantee drops it.
        assert!(view.canonical.contains("so that"));
    }

    #[test]
    fn definitions_have_no_contract_view() {
        let mut node = sample();
        node.statement = "A session means a sequence of requests.".into();
        let view = node_to_pb(&node).sentence.unwrap();
        assert_eq!(view.speech_act, pb::SpeechAct::Definition as i32);
        assert!(view.contract.is_none());
    }

    #[test]
    fn permissions_have_no_contract_view() {
        // A permission admits behavior rather than constraining it: it keeps
        // its speech act but carries no lone-sentence (⊤, G) contract view —
        // it enters contracts only through pairing, on the environment side.
        let mut node = sample();
        node.statement = "The client may retry.".into();
        let view = node_to_pb(&node).sentence.unwrap();
        assert_eq!(view.speech_act, pb::SpeechAct::Permission as i32);
        assert!(view.contract.is_none());
    }

    #[test]
    fn unparseable_statement_degrades_to_no_view() {
        let mut node = sample();
        // A pre-0.2 row accepted by an older grammar: no pivot for 0.2.
        node.statement = "The pump quickly.".into();
        let wire = node_to_pb(&node);
        assert!(wire.sentence.is_none());
        // The node itself still crosses the wire and converts back.
        assert!(Node::try_from(wire).is_ok());
    }

    #[test]
    fn missing_meta_is_a_convert_error() {
        let mut wire = node_to_pb(&sample());
        wire.meta = None;
        assert_eq!(
            Node::try_from(wire),
            Err(ConvertError::MissingField("node.meta"))
        );
    }

    #[test]
    fn edge_maps_endpoints_and_kind_to_pb() {
        use crate::domain::{Derivation, Edge, EdgeKind, EndpointRole, VertexKind};
        let edge = Edge {
            id: "e1".into(),
            source: "n1".into(),
            source_kind: VertexKind::Specification,
            source_role: EndpointRole::Mentioner,
            target: "n2".into(),
            target_kind: VertexKind::Term,
            target_role: EndpointRole::MentionedTerm,
            kind: EdgeKind::MentionsTerm,
            source_anchor: None,
            target_anchor: None,
            relied_spec_id: None,
            basis_spec_ids: vec![],
            derivation: Derivation {
                method: "test".into(),
                version: "1".into(),
            },
            recorded_at: "t".into(),
        };
        let wire = edge_to_pb(&edge);
        assert_eq!(wire.id, "e1");
        assert_eq!(wire.source, "n1");
        assert_eq!(wire.target, "n2");
        assert_eq!(wire.kind, pb::EdgeKind::MentionsTerm as i32);
        assert_eq!(wire.source_kind, pb::VertexKind::Specification as i32);
        assert_eq!(wire.family, pb::EdgeFamily::Lexical as i32);
        assert_eq!(wire.source_role, pb::EdgeEndpointRole::Mentioner as i32);
        assert_eq!(wire.target_role, pb::EdgeEndpointRole::MentionedTerm as i32);
    }

    #[test]
    fn every_nonlexical_edge_kind_has_a_wire_kind_family_and_roles() {
        use crate::domain::{Derivation, Edge, EdgeKind, VertexKind};
        for (kind, wire_kind, wire_family) in [
            (
                EdgeKind::Refines,
                pb::EdgeKind::Refines,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::Equivalent,
                pb::EdgeKind::Equivalent,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::HardContradiction,
                pb::EdgeKind::HardContradiction,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::AdvisoryTension,
                pb::EdgeKind::AdvisoryTension,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::DescriptiveConflict,
                pb::EdgeKind::DescriptiveConflict,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::EnvelopeConflict,
                pb::EdgeKind::EnvelopeConflict,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::OccurrenceReliance,
                pb::EdgeKind::OccurrenceReliance,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::GuaranteeDischarge,
                pb::EdgeKind::GuaranteeDischarge,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::AdmissibilityEnvelope,
                pb::EdgeKind::AdmissibilityEnvelope,
                pb::EdgeFamily::Semantic,
            ),
            (
                EdgeKind::Supports,
                pb::EdgeKind::Supports,
                pb::EdgeFamily::Selection,
            ),
            (
                EdgeKind::Defeats,
                pb::EdgeKind::Defeats,
                pb::EdgeFamily::Selection,
            ),
            (
                EdgeKind::Supersedes,
                pb::EdgeKind::Supersedes,
                pb::EdgeFamily::Selection,
            ),
        ] {
            let (source_role, target_role) = kind.endpoint_roles();
            let edge = Edge {
                id: format!("edge-{}", kind.as_str()),
                source: "a".into(),
                source_kind: VertexKind::Specification,
                source_role,
                target: "b".into(),
                target_kind: VertexKind::Specification,
                target_role,
                kind,
                source_anchor: None,
                target_anchor: None,
                relied_spec_id: kind.is_pairing().then(|| "relied".into()),
                basis_spec_ids: vec![],
                derivation: Derivation {
                    method: "test".into(),
                    version: "v1".into(),
                },
                recorded_at: "t".into(),
            };
            let wire = edge_to_pb(&edge);
            assert_eq!(wire.kind, wire_kind as i32);
            assert_eq!(wire.family, wire_family as i32);
            assert_ne!(wire.source_role, pb::EdgeEndpointRole::Unspecified as i32);
            assert_ne!(wire.target_role, pb::EdgeEndpointRole::Unspecified as i32);
            assert_eq!(wire.relied_spec_id.is_some(), kind.is_pairing());
        }
    }
}
