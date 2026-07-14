//! The `spec` command-line interface — a thin front end over the gRPC client.
//!
//! The daemon (`specd`) parses and persists one Specification Node, then runs
//! Evidence capture and all other processing as Jobs. This binary only resolves
//! the caller's descriptor input channels, sends the request, and renders the
//! one accepted Node. It
//! therefore carries no `--arango-*`/`--dir` flags — those configure the
//! daemon — only a `--server` address.

mod graph;

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use so_client::Client;
use so_protocol::pb;
use tracing::Instrument;

/// Exit code for specification syntax/count or a client-side channel error.
const EXIT_USAGE: u8 = 2;
/// Exit code for a connection or synchronous store failure.
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
    /// Add exactly one specification sentence; Evidence capture is asynchronous.
    Add(AddArgs),
    /// Render the specification graph directly in the terminal.
    Graph(GraphArgs),
}

#[derive(clap::Args)]
struct AddArgs {
    /// Exactly one sentence of the constrained specification language, e.g.
    /// "When the order is submitted, the system shall record the total."
    specification: String,

    /// Evidence requested for the specification. Capture is asynchronous.
    /// Repeatable. Each value is a JSON object
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

    /// Print the created node as a JSON object on success.
    #[arg(long = "json")]
    json: bool,
}

#[derive(clap::Args)]
struct GraphArgs {
    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    /// Width of the terminal graph in columns. Defaults to $COLUMNS or 120.
    #[arg(long, value_name = "COLUMNS", value_parser = clap::value_parser!(u16).range(40..))]
    width: Option<u16>,
}

fn main() -> ExitCode {
    let _telemetry =
        match so_tracing::init_without_console_output("spec", env!("CARGO_PKG_VERSION")) {
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
        Ok(node) => {
            if args.json {
                match serde_json::to_string_pretty(&node_to_json(&node)) {
                    Ok(s) => println!("{s}"),
                    Err(e) => {
                        eprintln!("error: failed to render nodes: {e}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!("Added {}  {}", node.id, node.statement);
                if !args.evidence.is_empty() {
                    println!(
                        "Evidence capture scheduled ({} request(s))",
                        args.evidence.len()
                    );
                }
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: {e}");
            // Bad input the user can fix (a channel error or a daemon
            // `INVALID_ARGUMENT`) is a usage error; everything else
            // (connection, synchronous store, decode) is a runtime failure.
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
        "spec.graph.selection" = "whole",
        "server.address" = %args.server,
        "spec.graph.specification_count" = tracing::field::Empty,
        "spec.graph.term_count" = tracing::field::Empty,
        "spec.graph.edge_count" = tracing::field::Empty,
    );
    let result = runtime.block_on(read_whole_graph(args.server.clone()).instrument(span));

    match result {
        Ok(graph) => {
            print!("{}", graph.render(args.width));
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

async fn read_whole_graph(server: String) -> Result<graph::Graph, so_client::ClientError> {
    const PAGE_SIZE: u32 = 1000;

    let mut client = Client::connect(server).await?;
    let mut specifications = BTreeMap::new();
    let mut terms = BTreeMap::new();
    let mut derived = BTreeMap::new();
    let mut edges = BTreeMap::new();
    let mut page_token = String::new();
    let mut seen_tokens = BTreeSet::new();

    let reported_specification_count = loop {
        let page = client.get_graph(PAGE_SIZE, &page_token).await?;
        let page_total = page.total_nodes;
        for node in page.nodes {
            specifications.insert(node.id.clone(), node);
        }
        for term in page.term_nodes {
            terms.insert(term.id.clone(), term);
        }
        for node in page.derived_nodes {
            derived.insert(node.id.clone(), node);
        }
        for edge in page.edges {
            edges.insert(edge.id.clone(), edge);
        }
        if page.next_page_token.is_empty() {
            break page_total;
        }
        if !seen_tokens.insert(page.next_page_token.clone()) {
            return Err(so_client::ClientError::InvalidGraphResponse(
                "daemon repeated a graph page token".to_string(),
            ));
        }
        page_token = page.next_page_token;
    };

    if specifications.len() as u64 != reported_specification_count {
        return Err(so_client::ClientError::InvalidGraphResponse(format!(
            "graph changed while it was being read: daemon reported {reported_specification_count} specifications but {} were received; rerun spec graph",
            specifications.len()
        )));
    }

    tracing::Span::current().record(
        "spec.graph.specification_count",
        specifications.len() as u64,
    );
    tracing::Span::current().record("spec.graph.term_count", terms.len() as u64);
    tracing::Span::current().record("spec.graph.edge_count", edges.len() as u64);
    graph::Graph::from_wire(
        specifications.into_values(),
        terms.into_values(),
        derived.into_values(),
        edges.into_values(),
    )
    .map_err(so_client::ClientError::InvalidGraphResponse)
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
            "evidence_requests": &m.evidence_requests,
            "evidence": m.evidence.iter().map(evidence_to_json).collect::<Vec<_>>(),
            "created_at": &m.created_at,
            "cli": &m.cli,
            "cli_version": &m.cli_version,
            "updates": m.updates.iter().map(meta_update_to_json).collect::<Vec<_>>(),
        }),
        None => serde_json::Value::Null,
    }
}

fn meta_update_to_json(update: &pb::MetaUpdate) -> serde_json::Value {
    let value = serde_json::from_str(&update.value_json)
        .unwrap_or_else(|_| serde_json::Value::String(update.value_json.clone()));

    serde_json::json!({
        "id": &update.id,
        "source": &update.source,
        "applied_at": &update.applied_at,
        "value": value,
    })
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

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_graph(args: &[&str]) -> GraphArgs {
        let cli = Cli::try_parse_from(args).expect("graph arguments should parse");
        match cli.command {
            Command::Graph(args) => args,
            Command::Add(_) => panic!("expected graph command"),
        }
    }

    #[test]
    fn graph_without_arguments_selects_the_whole_graph() {
        let args = parse_graph(&["spec", "graph"]);

        assert_eq!(args.server, "http://127.0.0.1:50051");
        assert_eq!(args.width, None);
    }

    #[test]
    fn graph_accepts_presentation_options_without_a_seed() {
        let args = parse_graph(&[
            "spec",
            "graph",
            "--width",
            "160",
            "--server",
            "http://specd:50051",
        ]);

        assert_eq!(args.width, Some(160));
        assert_eq!(args.server, "http://specd:50051");
    }

    #[test]
    fn graph_rejects_a_positional_seed() {
        let error = match Cli::try_parse_from(["spec", "graph", "spec-42"]) {
            Err(error) => error,
            Ok(_) => panic!("graph must not require or accept a positional seed"),
        };

        assert_eq!(error.kind(), clap::error::ErrorKind::UnknownArgument);
    }

    #[test]
    fn graph_does_not_expose_a_required_seed_option() {
        let error = match Cli::try_parse_from(["spec", "graph", "--around", "spec-42"]) {
            Err(error) => error,
            Ok(_) => panic!("--around must not define the graph command"),
        };

        assert_eq!(error.kind(), clap::error::ErrorKind::UnknownArgument);
    }

    #[test]
    fn meta_update_json_exposes_plugin_value_as_json() {
        let update = pb::MetaUpdate {
            id: "job-id".to_string(),
            source: "github-evidence".to_string(),
            applied_at: "2026-07-11T00:00:00Z".to_string(),
            value_json: r#"{"commit":"abc123"}"#.to_string(),
        };

        assert_eq!(
            meta_update_to_json(&update),
            serde_json::json!({
                "id": "job-id",
                "source": "github-evidence",
                "applied_at": "2026-07-11T00:00:00Z",
                "value": { "commit": "abc123" },
            })
        );
    }
}
