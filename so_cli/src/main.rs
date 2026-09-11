//! The `spec` command-line interface — a thin front end over the gRPC client.
//!
//! The daemon (`specd`) parses and persists one Specification Node, then runs
//! Evidence capture and all other processing as Event Consumers. This binary only resolves
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
    /// Inspect or rebuild the specification graph.
    Graph(GraphArgs),
    /// Add and query manual Evidence judgments.
    Evidence(EvidenceArgs),
}

#[derive(clap::Args)]
struct EvidenceArgs {
    #[command(subcommand)]
    command: EvidenceCommand,
}

#[derive(Subcommand)]
enum EvidenceCommand {
    /// Capture or reuse Evidence and affirm or deny a target.
    Add(EvidenceAddArgs),
    /// Extract an Evidence subgraph with the Evidence query language.
    Graph(EvidenceGraphArgs),
}

#[derive(clap::Args)]
struct EvidenceAddArgs {
    /// Existing Evidence id, JSON descriptor, bare locator, @file, or stdin (-).
    evidence: String,

    /// Affirm this Specification or Evidence id.
    #[arg(
        long,
        value_name = "TARGET_ID",
        conflicts_with = "denies",
        required_unless_present = "denies"
    )]
    affirms: Option<String>,

    /// Deny this Specification or Evidence id.
    #[arg(
        long,
        value_name = "TARGET_ID",
        conflicts_with = "affirms",
        required_unless_present = "affirms"
    )]
    denies: Option<String>,

    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    #[arg(long)]
    json: bool,
}

#[derive(clap::Args)]
struct EvidenceGraphArgs {
    /// Read-only openCypher returning one named path, e.g.
    /// "MATCH p=(a:Evidence)-[:EVIDENCE_DENIES]->(b:Evidence) RETURN p".
    query: String,

    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    #[arg(long, value_name = "COLUMNS", value_parser = clap::value_parser!(u16).range(40..))]
    width: Option<u16>,

    #[arg(long)]
    json: bool,
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
    #[command(subcommand)]
    command: GraphCommand,
}

#[derive(Subcommand)]
enum GraphCommand {
    /// Render the specification graph directly in the terminal.
    Show(GraphShowArgs),
    /// Reapply graph derivations asynchronously to every existing Node.
    Rebuild(GraphRebuildArgs),
}

#[derive(clap::Args)]
struct GraphShowArgs {
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

    /// Render every immutable Ledger Edge, including historical derivations
    /// and superseded projections. Current derivations remain marked.
    #[arg(long)]
    ledger: bool,

    /// Render the selected specification set as its induced current graph,
    /// including the current Evidence, projections, and relationships that
    /// remain connected to selected specifications.
    #[arg(long, conflicts_with = "ledger")]
    current: bool,
}

#[derive(clap::Args)]
struct GraphRebuildArgs {
    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    /// Print the accepted rebuild as a JSON object.
    #[arg(long)]
    json: bool,
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
        Command::Graph(GraphArgs {
            command: GraphCommand::Show(args),
        }) => run_graph_show(args),
        Command::Graph(GraphArgs {
            command: GraphCommand::Rebuild(args),
        }) => run_graph_rebuild(args),
        Command::Evidence(EvidenceArgs {
            command: EvidenceCommand::Add(args),
        }) => run_evidence_add(args),
        Command::Evidence(EvidenceArgs {
            command: EvidenceCommand::Graph(args),
        }) => run_evidence_graph(args),
    }
}

fn run_evidence_add(args: EvidenceAddArgs) -> ExitCode {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("error: failed to start async runtime: {error}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };
    let (target, relation) = match (args.affirms, args.denies) {
        (Some(target), None) => (target, pb::EvidenceRelationKind::Affirms),
        (None, Some(target)) => (target, pb::EvidenceRelationKind::Denies),
        _ => {
            eprintln!("error: exactly one of --affirms or --denies is required");
            return ExitCode::from(EXIT_USAGE);
        }
    };
    let result = runtime.block_on(async {
        let mut client = Client::connect(args.server).await?;
        client
            .add_evidence_relation(
                &args.evidence,
                &target,
                relation,
                "spec",
                env!("CARGO_PKG_VERSION"),
            )
            .await
    });
    match result {
        Ok(response) => {
            let Some(evidence_node) = response.evidence_node else {
                eprintln!("error: daemon response contained no Evidence Node");
                return ExitCode::from(EXIT_RUNTIME);
            };
            let Some(edge) = response.edge else {
                eprintln!("error: daemon response contained no Evidence Edge");
                return ExitCode::from(EXIT_RUNTIME);
            };
            if args.json {
                let evidence = evidence_node.value.as_ref().and_then(|value| match value {
                    pb::derived_node::Value::Evidence(node) => node.evidence.as_ref(),
                    _ => None,
                });
                let value = serde_json::json!({
                    "evidence_node": {
                        "id": evidence_node.id,
                        "evidence": evidence.map(evidence_to_json),
                    },
                    "edge": edge_to_json(&edge),
                    "evidence_node_inserted": response.evidence_node_inserted,
                    "edge_inserted": response.edge_inserted,
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&value)
                        .expect("Evidence response JSON is serializable")
                );
            } else {
                println!(
                    "{} {} {}",
                    evidence_node.id,
                    edge_kind_to_str(edge.kind),
                    edge.target
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => client_error_exit(error),
    }
}

fn run_evidence_graph(args: EvidenceGraphArgs) -> ExitCode {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("error: failed to start async runtime: {error}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };
    let result = runtime.block_on(read_evidence_graph(args.server, &args.query));
    match result {
        Ok((specifications, evidence, edges, selected, paths)) => {
            if args.json {
                let value = serde_json::json!({
                    "query": args.query,
                    "selected_evidence_ids": selected,
                    "paths": paths.values().map(|path| serde_json::json!({
                        "id": path.id,
                        "node_ids": path.node_ids,
                        "edge_ids": path.edge_ids,
                    })).collect::<Vec<_>>(),
                    "evidence_nodes": evidence.values().filter_map(|node| {
                        let value = node.value.as_ref()?;
                        let pb::derived_node::Value::Evidence(evidence_node) = value else {
                            return None;
                        };
                        Some(serde_json::json!({
                            "id": node.id,
                            "evidence": evidence_node.evidence.as_ref().map(evidence_to_json),
                        }))
                    }).collect::<Vec<_>>(),
                    "specification_nodes": specifications.values().map(node_to_json).collect::<Vec<_>>(),
                    "edges": edges.values().map(edge_to_json).collect::<Vec<_>>(),
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&value)
                        .expect("Evidence graph JSON is serializable")
                );
                ExitCode::SUCCESS
            } else {
                match graph::Graph::from_wire(
                    specifications.into_values(),
                    std::iter::empty(),
                    evidence.into_values(),
                    edges.into_values(),
                ) {
                    Ok(graph) => {
                        print!("{}", graph.render(args.width));
                        ExitCode::SUCCESS
                    }
                    Err(error) => {
                        eprintln!("error: {error}");
                        ExitCode::from(EXIT_RUNTIME)
                    }
                }
            }
        }
        Err(error) => client_error_exit(error),
    }
}

async fn read_evidence_graph(
    server: String,
    query: &str,
) -> Result<
    (
        BTreeMap<String, pb::Node>,
        BTreeMap<String, pb::DerivedNode>,
        BTreeMap<String, pb::Edge>,
        BTreeSet<String>,
        BTreeMap<String, pb::GraphPath>,
    ),
    so_client::ClientError,
> {
    const PAGE_SIZE: u32 = 100;
    let mut client = Client::connect(server).await?;
    let mut specifications = BTreeMap::new();
    let mut evidence = BTreeMap::new();
    let mut edges = BTreeMap::new();
    let mut selected = BTreeSet::new();
    let mut paths = BTreeMap::new();
    let mut token = String::new();
    let mut seen = BTreeSet::new();
    loop {
        let page = client
            .query_evidence_graph(query, PAGE_SIZE, &token)
            .await?;
        for node in page.specification_nodes {
            specifications.insert(node.id.clone(), node);
        }
        for node in page.evidence_nodes {
            evidence.insert(node.id.clone(), node);
        }
        for edge in page.edges {
            edges.insert(edge.id.clone(), edge);
        }
        selected.extend(page.selected_evidence_ids);
        for path in page.paths {
            paths.insert(path.id.clone(), path);
        }
        if page.next_page_token.is_empty() {
            break;
        }
        if !seen.insert(page.next_page_token.clone()) {
            return Err(so_client::ClientError::InvalidGraphResponse(
                "daemon repeated an Evidence graph page token".into(),
            ));
        }
        token = page.next_page_token;
    }
    Ok((specifications, evidence, edges, selected, paths))
}

fn client_error_exit(error: so_client::ClientError) -> ExitCode {
    eprintln!("error: {error}");
    ExitCode::from(if error.is_bad_input() {
        EXIT_USAGE
    } else {
        EXIT_RUNTIME
    })
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

fn run_graph_show(args: GraphShowArgs) -> ExitCode {
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
    let result = runtime.block_on(
        read_whole_graph(args.server.clone(), args.ledger, args.current).instrument(span),
    );

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

fn run_graph_rebuild(args: GraphRebuildArgs) -> ExitCode {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("error: failed to start async runtime: {error}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };
    let span = tracing::info_span!(
        "spec.cli.graph_rebuild",
        "server.address" = %args.server,
        "command.id" = tracing::field::Empty,
        "spec.graph.total_nodes" = tracing::field::Empty,
    );
    let result = runtime.block_on(
        async {
            let mut client = Client::connect(args.server).await?;
            client
                .start_graph_rebuild("spec", env!("CARGO_PKG_VERSION"))
                .await
        }
        .instrument(span),
    );

    match result {
        Ok(rebuild) => {
            tracing::Span::current().record("command.id", rebuild.rebuild_id.as_str());
            tracing::Span::current().record("spec.graph.total_nodes", rebuild.total_nodes);
            if args.json {
                let value = serde_json::json!({
                    "rebuild_id": rebuild.rebuild_id,
                    "started_at": rebuild.started_at,
                    "total_nodes": rebuild.total_nodes,
                });
                match serde_json::to_string_pretty(&value) {
                    Ok(rendered) => println!("{rendered}"),
                    Err(error) => {
                        eprintln!("error: failed to render graph rebuild: {error}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!(
                    "Graph rebuild started {}  ({} existing node(s))",
                    rebuild.rebuild_id, rebuild.total_nodes
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            let code = if error.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            };
            ExitCode::from(code)
        }
    }
}

struct WireGraph {
    specifications: BTreeMap<String, pb::Node>,
    terms: BTreeMap<String, pb::TermNode>,
    derived: BTreeMap<String, pb::DerivedNode>,
    edges: BTreeMap<String, pb::Edge>,
}

async fn read_whole_graph(
    server: String,
    ledger: bool,
    current: bool,
) -> Result<graph::Graph, so_client::ClientError> {
    let mut wire = read_wire_graph(server, ledger).await?;
    if current {
        retain_current_graph(&mut wire);
    }
    tracing::Span::current().record(
        "spec.graph.specification_count",
        wire.specifications.len() as u64,
    );
    tracing::Span::current().record("spec.graph.term_count", wire.terms.len() as u64);
    tracing::Span::current().record("spec.graph.edge_count", wire.edges.len() as u64);
    graph::Graph::from_wire(
        wire.specifications.into_values(),
        wire.terms.into_values(),
        wire.derived.into_values(),
        wire.edges.into_values(),
    )
    .map(|graph| {
        if current {
            graph.with_scope(graph::GraphScope::Current)
        } else if ledger {
            graph.with_scope(graph::GraphScope::Ledger)
        } else {
            graph
        }
    })
    .map_err(so_client::ClientError::InvalidGraphResponse)
}

async fn read_wire_graph(
    server: String,
    ledger: bool,
) -> Result<WireGraph, so_client::ClientError> {
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

    if ledger {
        terms.clear();
        derived.clear();
        edges.clear();
        let mut ledger_token = String::new();
        let mut seen_ledger_tokens = BTreeSet::new();
        loop {
            let page = client.get_ledger(PAGE_SIZE, &ledger_token).await?;
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
                break;
            }
            if !seen_ledger_tokens.insert(page.next_page_token.clone()) {
                return Err(so_client::ClientError::InvalidGraphResponse(
                    "daemon repeated a Ledger page token".to_string(),
                ));
            }
            ledger_token = page.next_page_token;
        }
    }

    Ok(WireGraph {
        specifications,
        terms,
        derived,
        edges,
    })
}

fn retain_current_graph(graph: &mut WireGraph) {
    let current_specification_ids: BTreeSet<String> = graph
        .specifications
        .values()
        .filter(|node| node.selection.as_ref().is_some_and(|view| view.current))
        .map(|node| node.id.clone())
        .collect();
    graph
        .edges
        .retain(|_, edge| edge_belongs_to_current_graph(edge, &current_specification_ids));
    let referenced_ids: BTreeSet<String> = graph
        .edges
        .values()
        .flat_map(|edge| {
            [
                Some(edge.source.clone()),
                Some(edge.target.clone()),
                edge.relied_spec_id.clone(),
            ]
            .into_iter()
            .flatten()
        })
        .collect();
    graph
        .specifications
        .retain(|id, _| current_specification_ids.contains(id));
    graph.terms.retain(|id, _| referenced_ids.contains(id));
    graph.derived.retain(|id, _| referenced_ids.contains(id));
}

fn edge_belongs_to_current_graph(edge: &pb::Edge, current_ids: &BTreeSet<String>) -> bool {
    let endpoint_is_current = |kind: i32, id: &str| {
        pb::VertexKind::try_from(kind).unwrap_or(pb::VertexKind::Unspecified)
            != pb::VertexKind::Specification
            || current_ids.contains(id)
    };
    endpoint_is_current(edge.source_kind, &edge.source)
        && endpoint_is_current(edge.target_kind, &edge.target)
        && edge
            .relied_spec_id
            .as_deref()
            .is_none_or(|id| current_ids.contains(id))
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
            "evidence_request_generation": &m.evidence_request_generation,
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

fn edge_to_json(edge: &pb::Edge) -> serde_json::Value {
    serde_json::json!({
        "id": edge.id,
        "source": edge.source,
        "source_kind": vertex_kind_to_str(edge.source_kind),
        "source_role": endpoint_role_to_str(edge.source_role),
        "target": edge.target,
        "target_kind": vertex_kind_to_str(edge.target_kind),
        "target_role": endpoint_role_to_str(edge.target_role),
        "kind": edge_kind_to_str(edge.kind),
        "family": edge_family_to_str(edge.family),
        "recorded_at": edge.recorded_at,
        "current": edge.current,
    })
}

fn edge_kind_to_str(kind: i32) -> &'static str {
    match pb::EdgeKind::try_from(kind).unwrap_or(pb::EdgeKind::Unspecified) {
        pb::EdgeKind::EvidenceAffirms => "evidence_affirms",
        pb::EdgeKind::EvidenceDenies => "evidence_denies",
        pb::EdgeKind::GroundedBy => "grounded_by",
        _ => "other",
    }
}

fn edge_family_to_str(family: i32) -> &'static str {
    match pb::EdgeFamily::try_from(family).unwrap_or(pb::EdgeFamily::Unspecified) {
        pb::EdgeFamily::Epistemic => "epistemic",
        pb::EdgeFamily::Projection => "projection",
        pb::EdgeFamily::Lexical => "lexical",
        pb::EdgeFamily::Semantic => "semantic",
        pb::EdgeFamily::Unspecified => "unspecified",
    }
}

fn vertex_kind_to_str(kind: i32) -> &'static str {
    match pb::VertexKind::try_from(kind).unwrap_or(pb::VertexKind::Unspecified) {
        pb::VertexKind::Specification => "specification",
        pb::VertexKind::Evidence => "evidence",
        pb::VertexKind::Term => "term",
        pb::VertexKind::Assumption => "assumption",
        pb::VertexKind::Guarantee => "guarantee",
        pb::VertexKind::Contract => "contract",
        pb::VertexKind::Entity => "entity",
        pb::VertexKind::Behavior => "behavior",
        pb::VertexKind::Unspecified => "unspecified",
    }
}

fn endpoint_role_to_str(role: i32) -> &'static str {
    match pb::EdgeEndpointRole::try_from(role).unwrap_or(pb::EdgeEndpointRole::Unspecified) {
        pb::EdgeEndpointRole::AffirmingEvidence => "affirming_evidence",
        pb::EdgeEndpointRole::AffirmedSpecification => "affirmed_specification",
        pb::EdgeEndpointRole::AffirmedEvidence => "affirmed_evidence",
        pb::EdgeEndpointRole::DenyingEvidence => "denying_evidence",
        pb::EdgeEndpointRole::DeniedSpecification => "denied_specification",
        pb::EdgeEndpointRole::DeniedEvidence => "denied_evidence",
        _ => "other",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_graph_show(args: &[&str]) -> GraphShowArgs {
        let cli = Cli::try_parse_from(args).expect("graph arguments should parse");
        match cli.command {
            Command::Graph(GraphArgs {
                command: GraphCommand::Show(args),
            }) => args,
            Command::Graph(GraphArgs {
                command: GraphCommand::Rebuild(_),
            }) => panic!("expected graph show command"),
            Command::Add(_) => panic!("expected graph command"),
            Command::Evidence(_) => panic!("expected graph command"),
        }
    }

    #[test]
    fn cli_rejects_removed_subcommands() {
        for command in ["refresh", "redispatch", "select", "pair", "current"] {
            assert!(
                Cli::try_parse_from(["spec", command]).is_err(),
                "{command} must not remain on the CLI surface"
            );
        }
    }

    #[test]
    fn graph_requires_an_explicit_subcommand() {
        assert!(Cli::try_parse_from(["spec", "graph"]).is_err());
    }

    #[test]
    fn evidence_add_requires_one_polarity_and_evidence_graph_accepts_a_query() {
        let cli = Cli::try_parse_from([
            "spec",
            "evidence",
            "add",
            "evidence-source",
            "--denies",
            "evidence-old",
        ])
        .unwrap();
        match cli.command {
            Command::Evidence(EvidenceArgs {
                command: EvidenceCommand::Add(args),
            }) => {
                assert_eq!(args.evidence, "evidence-source");
                assert_eq!(args.denies.as_deref(), Some("evidence-old"));
                assert!(args.affirms.is_none());
            }
            _ => panic!("expected evidence add"),
        }
        assert!(Cli::try_parse_from([
            "spec",
            "evidence",
            "add",
            "evidence-source",
            "--affirms",
            "spec-a",
            "--denies",
            "spec-b",
        ])
        .is_err());

        let cli = Cli::try_parse_from([
            "spec",
            "evidence",
            "graph",
            "MATCH p=(a:Evidence)-[:EVIDENCE_DENIES]->(b:Evidence) RETURN p",
        ])
        .unwrap();
        assert!(matches!(
            cli.command,
            Command::Evidence(EvidenceArgs {
                command: EvidenceCommand::Graph(EvidenceGraphArgs { .. })
            })
        ));
    }

    #[test]
    fn graph_show_without_arguments_selects_the_whole_graph() {
        let args = parse_graph_show(&["spec", "graph", "show"]);

        assert_eq!(args.server, "http://127.0.0.1:50051");
        assert_eq!(args.width, None);
        assert!(!args.ledger);
        assert!(!args.current);
    }

    #[test]
    fn graph_accepts_presentation_options_without_a_seed() {
        let args = parse_graph_show(&[
            "spec",
            "graph",
            "show",
            "--width",
            "160",
            "--server",
            "http://specd:50051",
        ]);

        assert_eq!(args.width, Some(160));
        assert_eq!(args.server, "http://specd:50051");
        assert!(!args.ledger);
        assert!(!args.current);
    }

    #[test]
    fn graph_current_and_ledger_are_distinct_views() {
        let current = parse_graph_show(&["spec", "graph", "show", "--current"]);
        assert!(current.current);
        assert!(!current.ledger);

        let ledger = parse_graph_show(&["spec", "graph", "show", "--ledger"]);
        assert!(ledger.ledger);
        assert!(!ledger.current);

        assert!(Cli::try_parse_from(["spec", "graph", "show", "--current", "--ledger"]).is_err());
    }

    #[test]
    fn graph_rebuild_is_a_distinct_subcommand() {
        let cli = Cli::try_parse_from([
            "spec",
            "graph",
            "rebuild",
            "--server",
            "http://specd:50051",
            "--json",
        ])
        .unwrap();
        match cli.command {
            Command::Graph(GraphArgs {
                command: GraphCommand::Rebuild(args),
            }) => {
                assert_eq!(args.server, "http://specd:50051");
                assert!(args.json);
            }
            _ => panic!("expected graph rebuild command"),
        }
    }

    #[test]
    fn current_graph_keeps_attached_projections_but_not_receded_specifications() {
        let current = BTreeSet::from(["selected".to_string()]);
        let projection = pb::Edge {
            source: "selected".into(),
            source_kind: pb::VertexKind::Specification as i32,
            target: "evidence".into(),
            target_kind: pb::VertexKind::Evidence as i32,
            ..Default::default()
        };
        let receded_projection = pb::Edge {
            source: "receded".into(),
            ..projection.clone()
        };
        let relation_to_receded = pb::Edge {
            target: "receded".into(),
            target_kind: pb::VertexKind::Specification as i32,
            ..projection.clone()
        };
        let pairing_relying_on_receded = pb::Edge {
            target: "selected".into(),
            target_kind: pb::VertexKind::Specification as i32,
            relied_spec_id: Some("receded".into()),
            ..projection.clone()
        };

        assert!(edge_belongs_to_current_graph(&projection, &current));
        assert!(!edge_belongs_to_current_graph(
            &receded_projection,
            &current
        ));
        assert!(!edge_belongs_to_current_graph(
            &relation_to_receded,
            &current
        ));
        assert!(!edge_belongs_to_current_graph(
            &pairing_relying_on_receded,
            &current
        ));
    }

    #[test]
    fn graph_rejects_a_positional_seed() {
        let error = match Cli::try_parse_from(["spec", "graph", "spec-42"]) {
            Err(error) => error,
            Ok(_) => panic!("graph must not require or accept a positional seed"),
        };

        assert_eq!(error.kind(), clap::error::ErrorKind::InvalidSubcommand);
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
