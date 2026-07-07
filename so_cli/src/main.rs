//! The `spec` command-line interface — a thin front end over the gRPC client.
//!
//! Parsing, capture, and persistence happen in the daemon (`specd`); this binary
//! only resolves the caller's input channels, sends the request, and renders the
//! nodes the daemon returns — one per sentence of the specification. It
//! therefore carries no `--arango-*`/`--dir` flags — those configure the
//! daemon — only a `--server` address.

use std::process::ExitCode;

use clap::{Parser, Subcommand};

use so_client::Client;
use so_protocol::pb;
use tracing::Instrument;

/// Exit code for a specification/evidence syntax error (bad input).
const EXIT_USAGE: u8 = 2;
/// Exit code for a connection/capture/store failure (environment/runtime).
const EXIT_RUNTIME: u8 = 1;

#[derive(Parser)]
#[command(
    name = "spec",
    version,
    about = "A specification graph in constrained natural language, read through assume-guarantee contracts."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Add a specification (one node per sentence) with its evidence.
    Add(AddArgs),
    /// Read one bounded page of the specification graph (nodes + edges).
    Graph(GraphArgs),
}

#[derive(clap::Args)]
struct AddArgs {
    /// One or more sentences of the constrained specification language, e.g.
    /// "When the order is submitted, the system shall record the total."
    specification: String,

    /// Evidence grounding the specification. Repeatable. Each value is a JSON object
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

    /// Print the created nodes as a JSON array on success.
    #[arg(long = "json")]
    json: bool,
}

#[derive(clap::Args)]
struct GraphArgs {
    /// Maximum nodes to return in this page. 0 lets the daemon choose its
    /// default; the daemon clamps to a hard maximum, so a graph read is always
    /// bounded — there is deliberately no "fetch everything" option.
    #[arg(long = "page-size", default_value_t = 0, value_name = "N")]
    page_size: u32,

    /// Opaque continuation token from a previous page's `next_page_token`. Omit
    /// to start from the beginning.
    #[arg(long = "page-token", default_value = "", value_name = "TOKEN")]
    page_token: String,

    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    /// Print the page as a JSON graph object ({nodes, edges, next_page_token,
    /// total_nodes}) instead of a human summary.
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
        Command::Graph(args) => run_graph(args),
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
        "spec.specification.length" = args.specification.len() as u64,
        "spec.evidence.arg_count" = args.evidence.len() as u64,
        "spec.specification.hash" = tracing::field::Empty,
        "spec.specification.text" = tracing::field::Empty,
        "server.address" = %args.server,
    );
    so_tracing::record_specification_on_span(&span, policy, &args.specification);

    let result = runtime.block_on(
        async {
            let mut client = Client::connect(args.server.clone()).await?;
            client
                .add(
                    &args.specification,
                    &args.evidence,
                    "spec",
                    env!("CARGO_PKG_VERSION"),
                )
                .await
        }
        .instrument(span),
    );

    match result {
        Ok(nodes) => {
            if args.json {
                let rendered: Vec<serde_json::Value> = nodes.iter().map(node_to_json).collect();
                match serde_json::to_string_pretty(&rendered) {
                    Ok(s) => println!("{s}"),
                    Err(e) => {
                        eprintln!("error: failed to render nodes: {e}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                for node in &nodes {
                    println!("Added {}", node_summary(node));
                }
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

fn run_graph(args: GraphArgs) -> ExitCode {
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

    let span = tracing::info_span!(
        "spec.cli.graph",
        "spec.page.requested_size" = args.page_size as u64,
        "spec.page.has_cursor" = !args.page_token.is_empty(),
        "server.address" = %args.server,
    );

    let result = runtime.block_on(
        async {
            let mut client = Client::connect(args.server.clone()).await?;
            client.get_graph(args.page_size, &args.page_token).await
        }
        .instrument(span),
    );

    match result {
        Ok(page) => {
            if args.json {
                let rendered = serde_json::json!({
                    "nodes": page.nodes.iter().map(node_to_json).collect::<Vec<_>>(),
                    "edges": page.edges.iter().map(edge_to_json).collect::<Vec<_>>(),
                    "next_page_token": page.next_page_token,
                    "total_nodes": page.total_nodes,
                });
                match serde_json::to_string_pretty(&rendered) {
                    Ok(s) => println!("{s}"),
                    Err(e) => {
                        eprintln!("error: failed to render graph: {e}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!(
                    "{} of {} node(s), {} edge(s)",
                    page.nodes.len(),
                    page.total_nodes,
                    page.edges.len()
                );
                for node in &page.nodes {
                    println!("  {}", node_summary(node));
                }
                if page.next_page_token.is_empty() {
                    println!("(end of graph)");
                } else {
                    println!("next page: --page-token {}", page.next_page_token);
                }
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: {e}");
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
    let speech_act = node
        .sentence
        .as_ref()
        .map(|s| speech_act_to_str(s.speech_act))
        .unwrap_or("unknown");
    format!("{}  {}  ({} evidence)", node.id, speech_act, evidence_count)
}

fn node_to_json(node: &pb::Node) -> serde_json::Value {
    serde_json::json!({
        "id": &node.id,
        "statement": &node.statement,
        "lang_version": &node.lang_version,
        "sentence": sentence_to_json(node.sentence.as_ref()),
        "meta": meta_to_json(node.meta.as_ref()),
    })
}

fn edge_to_json(edge: &pb::Edge) -> serde_json::Value {
    serde_json::json!({
        "id": &edge.id,
        "source": &edge.source,
        "target": &edge.target,
        "kind": edge_kind_to_str(edge.kind),
    })
}

fn edge_kind_to_str(kind: i32) -> &'static str {
    match pb::EdgeKind::try_from(kind).unwrap_or(pb::EdgeKind::Unspecified) {
        pb::EdgeKind::Refines => "refines",
        pb::EdgeKind::Composes => "composes",
        pb::EdgeKind::Contradicts => "contradicts",
        pb::EdgeKind::Unspecified => "unspecified",
    }
}

fn sentence_to_json(sentence: Option<&pb::SentenceView>) -> serde_json::Value {
    match sentence {
        Some(s) => serde_json::json!({
            "speech_act": speech_act_to_str(s.speech_act),
            "canonical": &s.canonical,
            "contract": contract_to_json(s.contract.as_ref()),
        }),
        None => serde_json::Value::Null,
    }
}

fn contract_to_json(contract: Option<&pb::ContractView>) -> serde_json::Value {
    match contract {
        Some(c) => serde_json::json!({
            "assumption": &c.assumption,
            "guarantee": &c.guarantee,
            "force": &c.force,
        }),
        None => serde_json::Value::Null,
    }
}

fn speech_act_to_str(speech_act: i32) -> &'static str {
    match pb::SpeechAct::try_from(speech_act).unwrap_or(pb::SpeechAct::Unspecified) {
        pb::SpeechAct::Definition => "definition",
        pb::SpeechAct::Description => "description",
        pb::SpeechAct::Obligation => "obligation",
        pb::SpeechAct::Prohibition => "prohibition",
        pb::SpeechAct::Recommendation => "recommendation",
        pb::SpeechAct::Permission => "permission",
        pb::SpeechAct::Unspecified => "unknown",
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
