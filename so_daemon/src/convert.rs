//! Conversions between the serde domain types and the generated protobuf
//! messages ([`so_protocol::pb`]).
//!
//! The two representations are kept deliberately separate: the domain types are
//! the serde model the daemon persists; the protobuf
//! messages are the wire form. This module is the single place that maps one to
//! the other. Domain → proto is total ([`From`]); proto → domain is fallible
//! ([`TryFrom`]) because a message received off the wire may omit a required
//! field or oneof arm.

use so_lang::grammar;

use crate::domain;
use so_protocol::pb;

/// A malformed wire message: a required field or oneof arm was absent.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum ConvertError {
    #[error("missing required field on the wire: {0}")]
    MissingField(&'static str),
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

// ---- Assumption / Guarantee (language types) -------------------------------

fn assumption_to_pb(a: &grammar::Assumption) -> pb::Assumption {
    let conditions = match a {
        grammar::Assumption::Top => Vec::new(),
        grammar::Assumption::Conditions { clauses } => clauses
            .iter()
            .map(|c| pb::Condition {
                keyword: c.keyword.clone(),
                text: c.text.clone(),
            })
            .collect(),
    };
    pb::Assumption { conditions }
}

fn assumption_from_pb(a: pb::Assumption) -> grammar::Assumption {
    // An empty condition list is the ubiquitous case ⊤.
    if a.conditions.is_empty() {
        grammar::Assumption::Top
    } else {
        grammar::Assumption::Conditions {
            clauses: a
                .conditions
                .into_iter()
                .map(|c| grammar::Condition {
                    keyword: c.keyword,
                    text: c.text,
                })
                .collect(),
        }
    }
}

fn guarantee_to_pb(g: &grammar::Guarantee) -> pb::Guarantee {
    pb::Guarantee {
        subject: g.subject.clone(),
        response: g.response.clone(),
    }
}

fn guarantee_from_pb(g: pb::Guarantee) -> grammar::Guarantee {
    grammar::Guarantee {
        subject: g.subject,
        response: g.response,
    }
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
        evidence: m.evidence.iter().map(evidence_to_pb).collect(),
        created_at: m.created_at.clone(),
        cli: m.cli.clone(),
        cli_version: m.cli_version.clone(),
    }
}

fn meta_from_pb(m: pb::Meta) -> Result<domain::Meta, ConvertError> {
    Ok(domain::Meta {
        evidence: m
            .evidence
            .into_iter()
            .map(evidence_from_pb)
            .collect::<Result<Vec<_>, _>>()?,
        created_at: m.created_at,
        cli: m.cli,
        cli_version: m.cli_version,
    })
}

// ---- Node ------------------------------------------------------------------

impl From<&domain::Node> for pb::Node {
    fn from(n: &domain::Node) -> pb::Node {
        pb::Node {
            id: n.id.clone(),
            statement: n.statement.clone(),
            assumption: Some(assumption_to_pb(&n.assumption)),
            guarantee: Some(guarantee_to_pb(&n.guarantee)),
            meta: Some(meta_to_pb(&n.meta)),
        }
    }
}

impl TryFrom<pb::Node> for domain::Node {
    type Error = ConvertError;

    fn try_from(n: pb::Node) -> Result<domain::Node, ConvertError> {
        Ok(domain::Node {
            id: n.id,
            statement: n.statement,
            assumption: assumption_from_pb(
                n.assumption
                    .ok_or(ConvertError::MissingField("node.assumption"))?,
            ),
            guarantee: guarantee_from_pb(
                n.guarantee
                    .ok_or(ConvertError::MissingField("node.guarantee"))?,
            ),
            meta: meta_from_pb(n.meta.ok_or(ConvertError::MissingField("node.meta"))?)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::{Anchor, Evidence, Kind, Locator, Meta, Node, Origin, Snapshot};

    fn sample() -> Node {
        Node {
            id: "n1".into(),
            statement: "When the order ships, the system shall notify the customer.".into(),
            assumption: grammar::Assumption::Conditions {
                clauses: vec![grammar::Condition {
                    keyword: "When".into(),
                    text: "the order ships".into(),
                }],
            },
            guarantee: grammar::Guarantee {
                subject: "system".into(),
                response: "notify the customer".into(),
            },
            meta: Meta {
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
            },
        }
    }

    #[test]
    fn node_round_trips_through_proto_dropping_only_content() {
        let node = sample();
        let wire = pb::Node::from(&node);
        let back = Node::try_from(wire).unwrap();

        // Content is not carried on the wire; everything else is identical.
        let mut expected = node.clone();
        for ev in &mut expected.meta.evidence {
            ev.snapshot.content = String::new();
        }
        assert_eq!(back, expected);
    }

    #[test]
    fn ubiquitous_assumption_survives_as_top() {
        let mut node = sample();
        node.assumption = grammar::Assumption::Top;
        let back = Node::try_from(pb::Node::from(&node)).unwrap();
        assert_eq!(back.assumption, grammar::Assumption::Top);
    }

    #[test]
    fn missing_guarantee_is_a_convert_error() {
        let mut wire = pb::Node::from(&sample());
        wire.guarantee = None;
        assert_eq!(
            Node::try_from(wire),
            Err(ConvertError::MissingField("node.guarantee"))
        );
    }
}
