//! The `spec` command-line interface — a thin front end over the gRPC client.
//!
//! Capture and persistence happen in the daemon (`specd`); this binary
//! only resolves the caller's input channels, sends the request, and renders the
//! node the daemon returns. It therefore carries no `--arango-*`/`--dir` flags —
//! those configure the daemon — only a `--server` address.

use std::process::ExitCode;

use clap::{Parser, Subcommand};

use so_client::Client;
use so_protocol::pb;
use tracing::Instrument;

/// Exit code for a statement/evidence syntax error (bad input).
const EXIT_USAGE: u8 = 2;
/// Exit code for a connection/capture/store failure (environment/runtime).
const EXIT_RUNTIME: u8 = 1;

#[derive(Parser)]
#[command(
    name = "spec",
    version,
    about = "An assume-guarantee contract specification graph, ingested from constrained natural language."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Add a specification node from a constrained-NL statement and its evidence.
    Add(AddArgs),
}

#[derive(clap::Args)]
struct AddArgs {
    /// The constrained-NL statement, e.g.
    /// "When the order is submitted, the system shall record the total."
    statement: String,

    /// Evidence grounding the statement. Repeatable. Each value is a JSON object
    /// (or array) with `kind` and `locator` (and optional `origin`), or a bare
    /// locator string (recorded as kind "unknown"). Prefix with `@` to read a
    /// file, or use `-` to read stdin. Note: the locator is resolved by the
    /// daemon, so a file locator names a path on the daemon's filesystem.
    #[arg(long = "evidence", value_name = "JSON|LOCATOR")]
    evidence: Vec<String>,

    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    /// Print the created node as JSON on success.
    #[arg(long = "json")]
    json: bool,
}

fn main() -> ExitCode {
    let _telemetry = match so_tracing::init("spec", env!("CARGO_PKG_VERSION")) {
        Ok(guard) => guard,
        Err(e) => {
            eprintln!("error: failed to initialize telemetry: {e:#}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };

    let cli = Cli::parse();
    match cli.command {
        Command::Add(args) => run_add(args),
    }
}

fn run_add(args: AddArgs) -> ExitCode {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(rt) => rt,
        Err(e) => {
            eprintln!("error: failed to start async runtime: {e}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };

    let policy = so_tracing::capture_policy();
    let span = tracing::info_span!(
        "spec.cli.add",
        "spec.telemetry.capture" = policy.as_str(),
        "spec.statement.length" = args.statement.len() as u64,
        "spec.evidence.arg_count" = args.evidence.len() as u64,
        "spec.statement.hash" = tracing::field::Empty,
        "spec.statement.text" = tracing::field::Empty,
        "server.address" = %args.server,
    );
    so_tracing::record_statement_on_span(&span, policy, &args.statement);

    let result = runtime.block_on(
        async {
            let mut client = Client::connect(args.server.clone()).await?;
            client
                .add(
                    &args.statement,
                    &args.evidence,
                    "spec",
                    env!("CARGO_PKG_VERSION"),
                )
                .await
        }
        .instrument(span),
    );

    match result {
        Ok(node) => {
            if args.json {
                match serde_json::to_string_pretty(&node_to_json(&node)) {
                    Ok(s) => println!("{s}"),
                    Err(e) => {
                        eprintln!("error: failed to render node: {e}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!("Added {}", node_summary(&node));
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: {e}");
            // Bad input the user can fix (a channel error or a daemon
            // `INVALID_ARGUMENT`) is a usage error; everything else (connection,
            // capture, store, decode) is a runtime failure.
            let code = if e.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            };
            ExitCode::from(code)
        }
    }
}

fn node_summary(node: &pb::Node) -> String {
    let evidence_count = node
        .meta
        .as_ref()
        .map(|meta| meta.evidence.len())
        .unwrap_or_default();
    format!("{}  ({} evidence)", node.id, evidence_count)
}

fn node_to_json(node: &pb::Node) -> serde_json::Value {
    serde_json::json!({
        "id": &node.id,
        "statement": &node.statement,
        "assumption": assumption_to_json(node.assumption.as_ref()),
        "guarantee": guarantee_to_json(node.guarantee.as_ref()),
        "meta": meta_to_json(node.meta.as_ref()),
    })
}

fn assumption_to_json(assumption: Option<&pb::Assumption>) -> serde_json::Value {
    let conditions = assumption
        .map(|a| a.conditions.as_slice())
        .unwrap_or_default();
    if conditions.is_empty() {
        serde_json::json!({ "kind": "top" })
    } else {
        serde_json::json!({
            "kind": "conditions",
            "clauses": conditions
                .iter()
                .map(|c| serde_json::json!({
                    "keyword": &c.keyword,
                    "text": &c.text,
                }))
                .collect::<Vec<_>>()
        })
    }
}

fn guarantee_to_json(guarantee: Option<&pb::Guarantee>) -> serde_json::Value {
    match guarantee {
        Some(g) => serde_json::json!({
            "subject": &g.subject,
            "response": &g.response,
        }),
        None => serde_json::Value::Null,
    }
}

fn meta_to_json(meta: Option<&pb::Meta>) -> serde_json::Value {
    match meta {
        Some(m) => serde_json::json!({
            "evidence": m.evidence.iter().map(evidence_to_json).collect::<Vec<_>>(),
            "created_at": &m.created_at,
            "cli": &m.cli,
            "cli_version": &m.cli_version,
        }),
        None => serde_json::Value::Null,
    }
}

fn evidence_to_json(evidence: &pb::Evidence) -> serde_json::Value {
    let mut value = serde_json::json!({
        "kind": kind_to_json(evidence.kind),
        "locator": locator_to_json(evidence.locator.as_ref()),
        "snapshot": snapshot_to_json(evidence.snapshot.as_ref()),
    });
    if let Some(origin) = evidence.origin.as_ref().and_then(origin_to_json) {
        value["origin"] = origin;
    }
    value
}

fn kind_to_json(kind: i32) -> &'static str {
    match pb::Kind::try_from(kind).unwrap_or(pb::Kind::Unspecified) {
        pb::Kind::Constitutive => "constitutive",
        pb::Kind::Demonstrative => "demonstrative",
        pb::Kind::Testimonial => "testimonial",
        pb::Kind::Assertoric => "assertoric",
        pb::Kind::Circumstantial => "circumstantial",
        pb::Kind::Counter => "counter",
        pb::Kind::Unknown | pb::Kind::Unspecified => "unknown",
    }
}

fn locator_to_json(locator: Option<&pb::Locator>) -> serde_json::Value {
    match locator.and_then(|l| l.value.as_ref()) {
        Some(pb::locator::Value::File(file)) => {
            let mut value = serde_json::json!({
                "type": "file",
                "path": &file.path,
            });
            if let Some(line) = file.line {
                value["line"] = serde_json::json!(line);
            }
            if let Some(col) = file.col {
                value["col"] = serde_json::json!(col);
            }
            value
        }
        Some(pb::locator::Value::Url(url)) => serde_json::json!({
            "type": "url",
            "url": &url.url,
        }),
        None => serde_json::Value::Null,
    }
}

fn snapshot_to_json(snapshot: Option<&pb::Snapshot>) -> serde_json::Value {
    match snapshot {
        Some(s) => serde_json::json!({
            "content_hash": &s.content_hash,
            "bytes": s.bytes,
            "captured_at": &s.captured_at,
            "anchor": anchor_to_json(s.anchor.as_ref()),
        }),
        None => serde_json::Value::Null,
    }
}

fn anchor_to_json(anchor: Option<&pb::Anchor>) -> serde_json::Value {
    match anchor.and_then(|a| a.value.as_ref()) {
        Some(pb::anchor::Value::Git(git)) => serde_json::json!({
            "type": "git",
            "commit": &git.commit,
            "dirty": git.dirty,
        }),
        Some(pb::anchor::Value::Worktree(_)) => serde_json::json!({
            "type": "worktree",
        }),
        Some(pb::anchor::Value::Web(web)) => {
            let mut value = serde_json::json!({
                "type": "web",
                "retrieved_at": &web.retrieved_at,
                "status": web.status,
            });
            if let Some(content_type) = &web.content_type {
                value["content_type"] = serde_json::json!(content_type);
            }
            if let Some(last_modified) = &web.last_modified {
                value["last_modified"] = serde_json::json!(last_modified);
            }
            value
        }
        None => serde_json::Value::Null,
    }
}

fn origin_to_json(origin: &pb::Origin) -> Option<serde_json::Value> {
    let mut map = serde_json::Map::new();
    if let Some(author) = &origin.author {
        map.insert("author".to_string(), serde_json::json!(author));
    }
    if let Some(created_at) = &origin.created_at {
        map.insert("created_at".to_string(), serde_json::json!(created_at));
    }
    if let Some(updated_at) = &origin.updated_at {
        map.insert("updated_at".to_string(), serde_json::json!(updated_at));
    }
    if map.is_empty() {
        None
    } else {
        Some(serde_json::Value::Object(map))
    }
}
