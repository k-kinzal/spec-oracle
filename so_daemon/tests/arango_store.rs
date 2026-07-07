//! Integration test for the ArangoDB-backed node store.
//!
//! Gated on `ARANGODB_URL`: with no server configured the test is a no-op, so
//! the suite stays green on a machine without ArangoDB. Point it at a running
//! instance (e.g. `ARANGODB_URL=http://localhost:8529`) to exercise the real
//! round trip. Auth is read from `ARANGODB_USER` / `ARANGODB_PASSWORD`
//! (defaulting to `root` / empty), and the database from `ARANGODB_DB`
//! (defaulting to `spec_oracle_test`).

use so_daemon::arango::{ArangoConfig, ArangoNodeStore};
use so_daemon::domain::{Anchor, Evidence, Kind, Locator, Meta, Node, Origin, Snapshot};
use so_daemon::store::{GraphStore, NodeStore};

fn sample_node(id: &str) -> Node {
    Node {
        id: id.to_string(),
        statement: "The pump shall stop.".to_string(),
        lang_version: so_lang::LANG_VERSION.to_string(),
        meta: Meta {
            evidence: vec![Evidence {
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
            }],
            created_at: "2026-07-05T00:00:00Z".to_string(),
            cli: "spec".to_string(),
            cli_version: "test".to_string(),
        },
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

    let node = sample_node("test-node-arango-roundtrip");
    store.add_node(&node).expect("add_node");

    let back = store
        .get_node(&node.id)
        .expect("get_node")
        .expect("node must exist after add");

    // Identity and the logical/epistemic metadata survive the round trip …
    assert_eq!(back.id, node.id);
    assert_eq!(back.statement, node.statement);
    assert_eq!(back.lang_version, node.lang_version);
    assert_eq!(back.meta.evidence.len(), 1);
    assert_eq!(back.meta.evidence[0].kind, node.meta.evidence[0].kind);
    assert_eq!(
        back.meta.evidence[0].snapshot.content_hash,
        node.meta.evidence[0].snapshot.content_hash
    );
    // … but the snapshot bytes are NOT stored in the graph: the blob store is
    // the byte authority, so a fetched node's content is empty.
    assert_eq!(back.meta.evidence[0].snapshot.content, "");

    // A missing key is a clean `None`, not an error.
    assert!(store
        .get_node("no-such-node-xyzzy")
        .expect("get_node missing")
        .is_none());

    // The maintained count includes our node, and keyset paging can page to it.
    assert!(store.count_nodes().expect("count_nodes") >= 1);

    // Keyset pagination is bounded and terminates: walk the whole collection in
    // small pages, following the cursor, and confirm our node is reachable and
    // no page exceeds the limit.
    let mut cursor: Option<String> = None;
    let mut found = false;
    let mut pages = 0;
    loop {
        let page = store.list_nodes(cursor.as_deref(), 100).expect("list_nodes");
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
