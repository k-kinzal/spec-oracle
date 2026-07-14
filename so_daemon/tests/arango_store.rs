//! Integration test for the ArangoDB-backed node store.
//!
//! Gated on `ARANGODB_URL`: with no server configured the test is a no-op, so
//! the suite stays green on a machine without ArangoDB. Point it at a running
//! instance (e.g. `ARANGODB_URL=http://localhost:8529`) to exercise the real
//! round trip. Auth is read from `ARANGODB_USER` / `ARANGODB_PASSWORD`
//! (defaulting to `root` / empty), and the database from `ARANGODB_DB`
//! (defaulting to `spec_oracle_test`).

use so_daemon::arango::{ArangoConfig, ArangoNodeStore};
use so_daemon::domain::{
    Anchor, AssessmentOutcome, DerivedNode, Edge, EdgeKind, Evidence, Kind, Locator, Meta,
    MetaUpdate, Node, Origin, RelationAssessment, Snapshot,
};
use so_daemon::store::{GraphStore, NodeStore};

fn sample_node(id: &str) -> Node {
    Node {
        id: id.to_string(),
        statement: "The pump shall stop.".to_string(),
        lang_version: so_lang::LANG_VERSION.to_string(),
        meta: Meta {
            evidence_requests: vec![
                r#"{"kind":"constitutive","locator":"src/pump.rs:10"}"#.to_string()
            ],
            evidence_request_generation: String::new(),
            evidence: vec![],
            created_at: "2026-07-05T00:00:00Z".to_string(),
            cli: "spec".to_string(),
            cli_version: "test".to_string(),
            updates: Default::default(),
        },
    }
}

fn captured_evidence() -> Evidence {
    Evidence {
        kind: Kind::Constitutive,
        locator: Locator::File {
            path: "src/pump.rs".to_string(),
            line: Some(10),
            col: None,
        },
        snapshot: Snapshot {
            content: "fn stop() {}".to_string(),
            content_hash: "deadbeef".to_string(),
            bytes: 12,
            captured_at: "2026-07-05T00:00:00Z".to_string(),
            anchor: Anchor::Worktree,
        },
        origin: Origin::default(),
    }
}

#[test]
fn arango_round_trip_when_available() {
    let url = match std::env::var("ARANGODB_URL") {
        Ok(u) => u,
        Err(_) => {
            eprintln!("skipping arango_round_trip_when_available: ARANGODB_URL not set");
            return;
        }
    };
    let username = std::env::var("ARANGODB_USER").unwrap_or_else(|_| "root".to_string());
    let password = std::env::var("ARANGODB_PASSWORD").unwrap_or_default();
    let database = std::env::var("ARANGODB_DB").unwrap_or_else(|_| "spec_oracle_test".to_string());

    let cfg = ArangoConfig {
        url: &url,
        database: &database,
        username: &username,
        password: &password,
    };
    let store = ArangoNodeStore::connect(&cfg).expect("connect to ArangoDB");

    // Relation assessments are append-only audit data, separate from topology.
    let assessment = RelationAssessment {
        id: format!("test-assessment-{}", uuid::Uuid::new_v4()),
        left: "candidate-a".into(),
        right: "candidate-b".into(),
        candidate_derivation: so_daemon::graph_generation::candidate_derivation(),
        semantic_derivation: so_daemon::graph_generation::semantic_derivation(),
        outcome: AssessmentOutcome::Unknown,
        recorded_at: "2026-07-12T00:00:00Z".into(),
    };
    assert!(store
        .append_relation_assessment(&assessment)
        .expect("append assessment"));
    assert!(!store
        .append_relation_assessment(&assessment)
        .expect("assessment append is idempotent"));
    assert_eq!(
        store
            .get_relation_assessment(&assessment.id)
            .expect("get assessment"),
        Some(assessment)
    );

    // Nodes are immutable and this integration database intentionally persists
    // across runs. A fresh id prevents a prior run's asynchronous Job facts
    // from changing the initial-state assertions below.
    let node = sample_node(&format!(
        "test-node-arango-roundtrip-{}",
        uuid::Uuid::new_v4()
    ));
    store.add_node(&node).expect("add_node");

    let back = store
        .get_node(&node.id)
        .expect("get_node")
        .expect("node must exist after add");

    // Identity and the logical/epistemic metadata survive the round trip …
    assert_eq!(back.id, node.id);
    assert_eq!(back.statement, node.statement);
    assert_eq!(back.lang_version, node.lang_version);
    assert_eq!(back.meta.evidence_requests, node.meta.evidence_requests);
    assert!(back.meta.evidence.is_empty());

    // Job results merge into Node Meta and are idempotent on the Job ID.
    let update = MetaUpdate {
        source: "arango-test".to_string(),
        applied_at: "2026-07-11T00:00:00Z".to_string(),
        value: serde_json::json!({"commit": "abc123"}),
    };
    let evidence = [captured_evidence()];
    store
        .apply_job_result(&node.id, "test-job", &update, Some(&evidence))
        .expect("apply_job_result");
    let updated = store.get_node(&node.id).unwrap().unwrap();
    assert_eq!(updated.meta.updates["test-job"], update);
    assert_eq!(updated.meta.evidence.len(), 1);
    assert_eq!(updated.meta.evidence[0].snapshot.content_hash, "deadbeef");
    // Snapshot bytes stay in the blob store; only metadata is in ArangoDB.
    assert_eq!(updated.meta.evidence[0].snapshot.content, "");

    // A missing key is a clean `None`, not an error.
    assert!(store
        .get_node("no-such-node-xyzzy")
        .expect("get_node missing")
        .is_none());

    // The maintained count includes our node, and keyset paging can page to it.
    assert!(store.count_nodes().expect("count_nodes") >= 1);

    // Node-derived graph structure is persisted in native term-node and edge
    // collections. The term is a lexical connector, not a Relation record.
    so_daemon::graph_generation::generate_and_persist(&node, &store, "2026-07-12T00:00:01Z")
        .expect("generate graph structure");
    let mut conflicting = sample_node(&format!(
        "test-node-arango-conflict-{}",
        uuid::Uuid::new_v4()
    ));
    conflicting.statement = "The pump shall not stop.".to_string();
    store.add_node(&conflicting).expect("add conflicting node");
    let conflict_report = so_daemon::graph_generation::generate_and_persist(
        &conflicting,
        &store,
        "2026-07-12T00:00:02Z",
    )
    .expect("generate semantic graph structure");
    let edges = store
        .list_edges(
            &[node.id.clone(), conflicting.id.clone()],
            &so_daemon::graph_generation::current_derivations(),
        )
        .expect("list_edges");
    assert!(edges
        .iter()
        .any(|edge| edge.kind == so_daemon::domain::EdgeKind::MentionsTerm));
    assert!(edges
        .iter()
        .any(|edge| edge.kind == EdgeKind::HardContradiction));
    assert!(conflict_report
        .outcomes
        .get("hard_contradiction")
        .is_some_and(|count| *count >= 1));
    assert!(conflict_report.assessments_inserted >= 1);

    // The native adjacency queries return the complete bounded input needed by
    // the shared fitness policy, including semantic competitors and their
    // Evidence projection Nodes.
    let proof = DerivedNode::evidence(captured_evidence());
    let proof_edge = Edge::projection(
        EdgeKind::GroundedBy,
        &node.id,
        proof.id(),
        so_daemon::evidence_capture::evidence_derivation(),
        "2026-07-12T00:00:03Z",
    )
    .unwrap();
    store
        .put_derived_node(&proof, &proof_edge)
        .expect("persist selection evidence");
    let population = store
        .selection_population(
            &[node.id.clone(), conflicting.id.clone()],
            &so_daemon::graph_generation::current_derivations(),
        )
        .expect("read fitness neighborhood");
    let views =
        so_daemon::selection::derive_views(&[node.id.clone(), conflicting.id.clone()], &population);
    assert!(views[&node.id].current);
    assert!(!views[&conflicting.id].current);
    assert!(views[&conflicting.id]
        .exclusions
        .iter()
        .any(|reason| reason.kind.as_str() == "insufficient_support"));
    let term_ids: Vec<String> = edges
        .iter()
        .filter(|edge| edge.target_kind == so_daemon::domain::VertexKind::Term)
        .map(|edge| edge.target.clone())
        .collect();
    let terms = store.get_term_nodes(&term_ids).expect("get_term_nodes");
    assert!(terms.iter().any(|term| term.form == "pump"));
    // Keyset pagination is bounded and terminates: walk the whole collection in
    // small pages, following the cursor, and confirm our node is reachable and
    // no page exceeds the limit.
    let mut cursor: Option<String> = None;
    let mut found = false;
    let mut pages = 0;
    loop {
        let page = store
            .list_nodes(cursor.as_deref(), 100)
            .expect("list_nodes");
        assert!(page.nodes.len() <= 100, "a page never exceeds the limit");
        if page.nodes.iter().any(|n| n.id == node.id) {
            found = true;
        }
        pages += 1;
        assert!(pages < 100_000, "cursor must terminate");
        match page.next_cursor {
            Some(c) => cursor = Some(c),
            None => break,
        }
    }
    assert!(found, "the round-tripped node must appear in a page");
}
