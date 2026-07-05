//! Regression test for git-backed snapshot/origin capture.
//!
//! Exercises the exact case the in-module unit tests missed: a modified file in
//! a *subdirectory*, addressed by a *relative* locator with the process running
//! at the repository root. Earlier, this doubled the git pathspec — silently
//! reporting `dirty: false` and dropping the git author.
//!
//! It drives the ingest use case at the library level with an in-memory node
//! store and a temp-dir blob store, so it stays hermetic and does not require a
//! running ArangoDB. The relative-locator regression depends on the process
//! working directory being the repo root, so this test sets it — safe because
//! this is the sole test in its (single-process) binary.

use std::fs;
use std::process::Command;

use so_daemon::add::{self, AddRequest};
use so_daemon::domain::Anchor;
use so_daemon::store::{FileBlobStore, InMemoryNodeStore};

fn git(dir: &std::path::Path, args: &[&str]) {
    let out = Command::new("git")
        .current_dir(dir)
        .args(args)
        .output()
        .expect("git should be available");
    assert!(
        out.status.success(),
        "git {:?} failed: {}",
        args,
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn captures_dirty_flag_and_git_author_for_subdir_relative_path() {
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path();

    // A repository with a committed file two directories deep.
    git(root, &["init", "-q"]);
    fs::create_dir_all(root.join("pkg/order")).unwrap();
    fs::write(root.join("pkg/order/total.rs"), "let total = 1;\n").unwrap();
    git(root, &["add", "."]);
    git(
        root,
        &[
            "-c",
            "user.email=tester@example.com",
            "-c",
            "user.name=Regression Tester",
            "commit",
            "-q",
            "-m",
            "seed",
        ],
    );

    // Dirty the working tree.
    fs::write(root.join("pkg/order/total.rs"), "let total = 2;\n").unwrap();

    // The regression only reproduces with a relative locator resolved against a
    // process CWD at the repo root, so run from there and restore afterwards.
    let original_cwd = std::env::current_dir().unwrap();
    std::env::set_current_dir(root).unwrap();

    let nodes = InMemoryNodeStore::new();
    let blobs = FileBlobStore::open(&root.join("blobs")).unwrap();
    let req = AddRequest {
        statement: "The total shall be positive.",
        evidence_values: &["pkg/order/total.rs:1".to_string()],
        now: "2026-07-05T00:00:00Z",
        cli: "spec",
        cli_version: "test",
    };
    let result = add::run(&req, &nodes, &blobs);

    std::env::set_current_dir(original_cwd).unwrap();

    let node = result.expect("add should succeed");
    let ev = &node.meta.evidence[0];

    // The commit is pinned and the dirty working tree is detected.
    match &ev.snapshot.anchor {
        Anchor::Git { dirty, .. } => assert!(
            *dirty,
            "modified subdir file must be reported dirty; got {:#?}",
            ev.snapshot.anchor
        ),
        other => panic!("expected a git anchor, got {other:#?}"),
    }

    // The git author is discovered as sense-① origin.
    assert_eq!(
        ev.origin.author.as_deref(),
        Some("Regression Tester"),
        "git author must be discovered for a relative subdir path; got {:#?}",
        ev.origin
    );
}
