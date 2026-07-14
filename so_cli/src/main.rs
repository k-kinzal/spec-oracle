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

use clap::{Parser, Subcommand, ValueEnum};
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
    /// Replace or refresh one candidate's complete Evidence descriptor set.
    Refresh(RefreshArgs),
    /// Append an explicit selection judgment between Specification Nodes.
    Select(SelectArgs),
    /// Append a proved assume-guarantee pairing with an explicit reliance.
    Pair(PairArgs),
    /// Render the specification graph directly in the terminal.
    Graph(GraphArgs),
    /// Emit the fitness-selected current specification set.
    Current(CurrentArgs),
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
struct RefreshArgs {
    /// Existing Specification Node id whose current Evidence input is replaced.
    node_id: String,

    /// Complete replacement Evidence set. Repeatable; values use the same
    /// JSON/bare-locator and @file/stdin channels as `spec add`. Supplying none
    /// clears the current Evidence view while Ledger history remains.
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

    /// Print the stored pre-capture Node state as JSON.
    #[arg(long)]
    json: bool,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum SelectionKind {
    Supports,
    Defeats,
    Supersedes,
}

impl SelectionKind {
    fn wire(self) -> pb::EdgeKind {
        match self {
            Self::Supports => pb::EdgeKind::Supports,
            Self::Defeats => pb::EdgeKind::Defeats,
            Self::Supersedes => pb::EdgeKind::Supersedes,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::Supports => "supports",
            Self::Defeats => "defeats",
            Self::Supersedes => "supersedes",
        }
    }
}

#[derive(clap::Args)]
struct SelectArgs {
    /// The explicit selection judgment to append.
    kind: SelectionKind,
    /// Supporter, defeater, or superseder Specification Node id.
    source: String,
    /// Supported, defeated, or superseded Specification Node id.
    target: String,
    /// Additional Specification Node id that makes the judgment checkable.
    #[arg(long = "basis", value_name = "NODE_ID")]
    basis_spec_ids: Vec<String>,
    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,
    /// Print the appended Edge as JSON.
    #[arg(long = "json")]
    json: bool,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum PairingKind {
    OccurrenceReliance,
    GuaranteeDischarge,
    AdmissibilityEnvelope,
}

impl PairingKind {
    fn wire(self) -> pb::EdgeKind {
        match self {
            Self::OccurrenceReliance => pb::EdgeKind::OccurrenceReliance,
            Self::GuaranteeDischarge => pb::EdgeKind::GuaranteeDischarge,
            Self::AdmissibilityEnvelope => pb::EdgeKind::AdmissibilityEnvelope,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::OccurrenceReliance => "occurrence_reliance",
            Self::GuaranteeDischarge => "guarantee_discharge",
            Self::AdmissibilityEnvelope => "admissibility_envelope",
        }
    }
}

#[derive(clap::Args)]
struct PairArgs {
    /// The causal role of the source in the target contract.
    kind: PairingKind,
    /// Evidence-bearing Specification Node id.
    source: String,
    /// Specification Node id whose guarantee is conditioned.
    target: String,
    /// Authored Specification Node naming exactly what the target awaits.
    #[arg(long, value_name = "NODE_ID")]
    relied: String,
    /// Additional authored Specification Node making the pairing checkable.
    #[arg(long = "basis", value_name = "NODE_ID")]
    basis_spec_ids: Vec<String>,
    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,
    /// Print the appended Edge as JSON.
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
struct CurrentArgs {
    /// Address of the spec-oracle daemon.
    #[arg(
        long = "server",
        env = "SPEC_ORACLE_SERVER",
        default_value = "http://127.0.0.1:50051",
        value_name = "URL"
    )]
    server: String,

    /// Emit one machine-readable current graph containing the selected
    /// specifications, attached nodes and relationships, and fitness reasons.
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
        Command::Refresh(args) => run_refresh(args),
        Command::Select(args) => run_select(args),
        Command::Pair(args) => run_pair(args),
        Command::Graph(args) => run_graph(args),
        Command::Current(args) => run_current(args),
    }
}

fn run_pair(args: PairArgs) -> ExitCode {
    let runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(rt) => rt,
        Err(error) => {
            eprintln!("error: failed to start async runtime: {error}");
            return ExitCode::from(EXIT_RUNTIME);
        }
    };
    let result = runtime.block_on(async {
        let mut client = Client::connect(args.server.clone()).await?;
        client
            .add_assumption_relation(
                &args.source,
                &args.target,
                &args.relied,
                args.kind.wire(),
                &args.basis_spec_ids,
            )
            .await
    });
    match result {
        Ok(edge) => {
            if args.json {
                let derivation = edge.derivation.as_ref();
                let value = serde_json::json!({
                    "id": edge.id,
                    "source": edge.source,
                    "target": edge.target,
                    "relied_spec_id": edge.relied_spec_id,
                    "kind": args.kind.as_str(),
                    "basis_spec_ids": edge.basis_spec_ids,
                    "derivation": derivation.map(|d| serde_json::json!({
                        "method": d.method,
                        "version": d.version,
                    })),
                    "recorded_at": edge.recorded_at,
                });
                match serde_json::to_string_pretty(&value) {
                    Ok(output) => println!("{output}"),
                    Err(error) => {
                        eprintln!("error: failed to render Edge: {error}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!(
                    "Paired {}  {} {} {} (relied {})",
                    edge.id,
                    edge.source,
                    args.kind.as_str(),
                    edge.target,
                    edge.relied_spec_id.as_deref().unwrap_or("")
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(if error.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            })
        }
    }
}

fn run_select(args: SelectArgs) -> ExitCode {
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
        "spec.cli.select",
        "selection.kind" = args.kind.as_str(),
        "selection.source" = %args.source,
        "selection.target" = %args.target,
        "selection.basis_count" = args.basis_spec_ids.len() as u64,
        "server.address" = %args.server,
    );
    let result = runtime.block_on(
        async {
            let mut client = Client::connect(args.server.clone()).await?;
            client
                .add_selection_relation(
                    &args.source,
                    &args.target,
                    args.kind.wire(),
                    &args.basis_spec_ids,
                )
                .await
        }
        .instrument(span),
    );
    match result {
        Ok(edge) => {
            if args.json {
                let derivation = edge.derivation.as_ref();
                let value = serde_json::json!({
                    "id": edge.id,
                    "source": edge.source,
                    "target": edge.target,
                    "kind": args.kind.as_str(),
                    "basis_spec_ids": edge.basis_spec_ids,
                    "derivation": derivation.map(|d| serde_json::json!({
                        "method": d.method,
                        "version": d.version,
                    })),
                    "recorded_at": edge.recorded_at,
                });
                match serde_json::to_string_pretty(&value) {
                    Ok(output) => println!("{output}"),
                    Err(error) => {
                        eprintln!("error: failed to render Edge: {error}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else {
                println!(
                    "Selected {}  {} {} {}",
                    edge.id,
                    edge.source,
                    args.kind.as_str(),
                    edge.target
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(if error.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            })
        }
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

fn run_refresh(args: RefreshArgs) -> ExitCode {
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
    let result = runtime.block_on(async {
        let mut client = Client::connect(args.server.clone()).await?;
        client.replace_evidence(&args.node_id, &args.evidence).await
    });
    match result {
        Ok(node) => {
            if args.json {
                match serde_json::to_string_pretty(&node_to_json(&node)) {
                    Ok(output) => println!("{output}"),
                    Err(error) => {
                        eprintln!("error: failed to render Node: {error}");
                        return ExitCode::from(EXIT_RUNTIME);
                    }
                }
            } else if args.evidence.is_empty() {
                println!(
                    "Cleared current Evidence for {}; prior captures remain in the Ledger",
                    node.id
                );
            } else {
                println!(
                    "Replaced Evidence inputs for {}; capture scheduled ({} request(s))",
                    node.id,
                    args.evidence.len()
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(if error.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            })
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

fn run_current(args: CurrentArgs) -> ExitCode {
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
        "spec.cli.current",
        "server.address" = %args.server,
        "spec.current.candidate_count" = tracing::field::Empty,
        "spec.current.selected_count" = tracing::field::Empty,
    );
    if args.json {
        let result = runtime.block_on(read_current_graph_json(args.server).instrument(span));
        return match result {
            Ok(value) => match serde_json::to_string_pretty(&value) {
                Ok(output) => {
                    println!("{output}");
                    ExitCode::SUCCESS
                }
                Err(error) => {
                    eprintln!("error: failed to render current graph: {error}");
                    ExitCode::from(EXIT_RUNTIME)
                }
            },
            Err(error) => {
                eprintln!("error: {error}");
                ExitCode::from(if error.is_bad_input() {
                    EXIT_USAGE
                } else {
                    EXIT_RUNTIME
                })
            }
        };
    }
    let result = runtime.block_on(read_all_specifications(args.server).instrument(span));

    match result {
        Ok(specifications) => {
            let total = specifications.len();
            let selected: Vec<&pb::Node> = specifications
                .iter()
                .filter(|node| node.selection.as_ref().is_some_and(|view| view.current))
                .collect();
            let policy_version = specifications
                .iter()
                .filter_map(|node| node.selection.as_ref())
                .map(|view| view.policy_version.as_str())
                .find(|version| !version.is_empty())
                .unwrap_or("unavailable");
            tracing::Span::current().record("spec.current.candidate_count", total as u64);
            tracing::Span::current().record("spec.current.selected_count", selected.len() as u64);

            println!(
                "Current specification set ({policy_version}): {} of {total} candidates",
                selected.len()
            );
            for node in selected {
                let selection = node
                    .selection
                    .as_ref()
                    .expect("selected Node has a selection view");
                println!(
                    "{}  fitness {:+} (Evidence {:+}, relations {:+})  {}",
                    node.id,
                    selection.support_score,
                    selection.evidence_score,
                    selection.relation_score,
                    node.statement
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(if error.is_bad_input() {
                EXIT_USAGE
            } else {
                EXIT_RUNTIME
            })
        }
    }
}

async fn read_all_specifications(server: String) -> Result<Vec<pb::Node>, so_client::ClientError> {
    const PAGE_SIZE: u32 = 1000;

    let mut client = Client::connect(server).await?;
    let mut specifications = BTreeMap::new();
    let mut page_token = String::new();
    let mut seen_tokens = BTreeSet::new();
    let reported_count = loop {
        let page = client.get_graph(PAGE_SIZE, &page_token).await?;
        let page_total = page.total_nodes;
        for node in page.nodes {
            specifications.insert(node.id.clone(), node);
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
    if specifications.len() as u64 != reported_count {
        return Err(so_client::ClientError::InvalidGraphResponse(format!(
            "graph changed while the current set was being read: daemon reported {reported_count} specifications but {} were received; rerun spec current",
            specifications.len()
        )));
    }
    Ok(specifications.into_values().collect())
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

async fn read_current_graph_json(
    server: String,
) -> Result<serde_json::Value, so_client::ClientError> {
    let mut graph = read_wire_graph(server, false).await?;
    let candidate_count = graph.specifications.len();
    let policy_version = graph
        .specifications
        .values()
        .filter_map(|node| node.selection.as_ref())
        .map(|view| view.policy_version.clone())
        .find(|version| !version.is_empty())
        .unwrap_or_else(|| "unavailable".into());
    retain_current_graph(&mut graph);
    tracing::Span::current().record("spec.current.candidate_count", candidate_count as u64);
    tracing::Span::current().record(
        "spec.current.selected_count",
        graph.specifications.len() as u64,
    );
    Ok(serde_json::json!({
        "policy_version": policy_version,
        "candidate_count": candidate_count,
        "current_count": graph.specifications.len(),
        "specifications": graph.specifications.values()
            .map(specification_with_selection_to_json)
            .collect::<Vec<_>>(),
        "term_nodes": graph.terms.values().map(term_node_to_json).collect::<Vec<_>>(),
        "derived_nodes": graph.derived.values().map(derived_node_to_json).collect::<Vec<_>>(),
        "edges": graph.edges.values().map(edge_to_json).collect::<Vec<_>>(),
    }))
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

fn term_node_to_json(node: &pb::TermNode) -> serde_json::Value {
    serde_json::json!({
        "id": &node.id,
        "form": &node.form,
        "head": &node.head,
        "lang_version": &node.lang_version,
        "derivation_version": &node.derivation_version,
    })
}

fn derived_node_to_json(node: &pb::DerivedNode) -> serde_json::Value {
    match node.value.as_ref() {
        Some(pb::derived_node::Value::Evidence(value)) => serde_json::json!({
            "id": &node.id,
            "node_kind": "evidence",
            "evidence": value.evidence.as_ref().map(evidence_to_json),
        }),
        Some(pb::derived_node::Value::Assumption(value)) => serde_json::json!({
            "id": &node.id,
            "node_kind": "assumption",
            "expression": &value.expression,
            "formula_json": &value.formula_json,
            "derivation_version": &value.derivation_version,
        }),
        Some(pb::derived_node::Value::Guarantee(value)) => serde_json::json!({
            "id": &node.id,
            "node_kind": "guarantee",
            "expression": &value.expression,
            "force": &value.force,
            "derivation_version": &value.derivation_version,
        }),
        None => serde_json::json!({
            "id": &node.id,
            "node_kind": "unknown",
        }),
    }
}

fn edge_to_json(edge: &pb::Edge) -> serde_json::Value {
    let kind = pb::EdgeKind::try_from(edge.kind).unwrap_or(pb::EdgeKind::Unspecified);
    let family = pb::EdgeFamily::try_from(edge.family).unwrap_or(pb::EdgeFamily::Unspecified);
    let source_kind =
        pb::VertexKind::try_from(edge.source_kind).unwrap_or(pb::VertexKind::Unspecified);
    let target_kind =
        pb::VertexKind::try_from(edge.target_kind).unwrap_or(pb::VertexKind::Unspecified);
    let source_role = pb::EdgeEndpointRole::try_from(edge.source_role)
        .unwrap_or(pb::EdgeEndpointRole::Unspecified);
    let target_role = pb::EdgeEndpointRole::try_from(edge.target_role)
        .unwrap_or(pb::EdgeEndpointRole::Unspecified);
    serde_json::json!({
        "id": &edge.id,
        "source": &edge.source,
        "target": &edge.target,
        "kind": enum_label(kind.as_str_name(), "EDGE_KIND_"),
        "family": enum_label(family.as_str_name(), "EDGE_FAMILY_"),
        "source_kind": enum_label(source_kind.as_str_name(), "VERTEX_KIND_"),
        "target_kind": enum_label(target_kind.as_str_name(), "VERTEX_KIND_"),
        "source_role": enum_label(source_role.as_str_name(), "EDGE_ENDPOINT_ROLE_"),
        "target_role": enum_label(target_role.as_str_name(), "EDGE_ENDPOINT_ROLE_"),
        "source_anchor": edge.source_anchor.as_ref().map(text_anchor_to_json),
        "target_anchor": edge.target_anchor.as_ref().map(text_anchor_to_json),
        "relied_spec_id": &edge.relied_spec_id,
        "basis_spec_ids": &edge.basis_spec_ids,
        "derivation": edge.derivation.as_ref().map(|derivation| serde_json::json!({
            "method": &derivation.method,
            "version": &derivation.version,
        })),
        "recorded_at": &edge.recorded_at,
        "current": edge.current,
    })
}

fn text_anchor_to_json(anchor: &pb::TextAnchor) -> serde_json::Value {
    serde_json::json!({
        "selector": &anchor.selector,
        "text": &anchor.text,
        "role": &anchor.role,
    })
}

fn enum_label(name: &str, prefix: &str) -> String {
    name.strip_prefix(prefix)
        .unwrap_or(name)
        .to_ascii_lowercase()
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

fn specification_with_selection_to_json(node: &pb::Node) -> serde_json::Value {
    let mut value = node_to_json(node);
    value["selection"] = selection_to_json(node.selection.as_ref());
    value
}

fn selection_to_json(selection: Option<&pb::SelectionView>) -> serde_json::Value {
    let Some(selection) = selection else {
        return serde_json::Value::Null;
    };
    serde_json::json!({
        "current": selection.current,
        "policy_version": &selection.policy_version,
        "support_score": selection.support_score,
        "evidence_score": selection.evidence_score,
        "relation_score": selection.relation_score,
        "supporting_edge_ids": &selection.supporting_edge_ids,
        "defeating_edge_ids": &selection.defeating_edge_ids,
        "superseding_edge_ids": &selection.superseding_edge_ids,
        "contributions": selection.contributions.iter().map(|contribution| serde_json::json!({
            "kind": &contribution.kind,
            "points": contribution.points,
            "edge_id": &contribution.edge_id,
            "source_node_id": &contribution.source_node_id,
            "evidence_node_id": &contribution.evidence_node_id,
            "detail": &contribution.detail,
        })).collect::<Vec<_>>(),
        "exclusions": selection.exclusions.iter().map(|exclusion| serde_json::json!({
            "kind": &exclusion.kind,
            "edge_id": &exclusion.edge_id,
            "competing_node_id": &exclusion.competing_node_id,
            "detail": &exclusion.detail,
        })).collect::<Vec<_>>(),
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

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_graph(args: &[&str]) -> GraphArgs {
        let cli = Cli::try_parse_from(args).expect("graph arguments should parse");
        match cli.command {
            Command::Graph(args) => args,
            Command::Add(_)
            | Command::Refresh(_)
            | Command::Select(_)
            | Command::Pair(_)
            | Command::Current(_) => {
                panic!("expected graph command")
            }
        }
    }

    #[test]
    fn current_command_exposes_a_machine_readable_mode() {
        let cli = Cli::try_parse_from(["spec", "current", "--json", "--server", "http://specd"])
            .expect("current arguments should parse");
        let Command::Current(args) = cli.command else {
            panic!("expected current command");
        };
        assert!(args.json);
        assert_eq!(args.server, "http://specd");
    }

    #[test]
    fn refresh_accepts_a_complete_replacement_evidence_set() {
        let cli = Cli::try_parse_from([
            "spec",
            "refresh",
            "node-1",
            "--evidence",
            "proof.rs:1",
            "--evidence",
            r#"{"kind":"counter","locator":"report.md:2"}"#,
        ])
        .expect("refresh arguments should parse");
        let Command::Refresh(args) = cli.command else {
            panic!("expected refresh command");
        };
        assert_eq!(args.node_id, "node-1");
        assert_eq!(args.evidence.len(), 2);
    }

    #[test]
    fn select_accepts_only_the_explicit_selection_vocabulary() {
        let cli = Cli::try_parse_from([
            "spec",
            "select",
            "supersedes",
            "replacement",
            "old",
            "--basis",
            "review",
        ])
        .unwrap();
        let Command::Select(args) = cli.command else {
            panic!("expected select command")
        };
        assert!(matches!(args.kind, SelectionKind::Supersedes));
        assert_eq!(args.source, "replacement");
        assert_eq!(args.target, "old");
        assert_eq!(args.basis_spec_ids, vec!["review"]);

        assert!(Cli::try_parse_from(["spec", "select", "refines", "a", "b"]).is_err());
    }

    #[test]
    fn pair_requires_an_explicit_relied_specification() {
        let cli = Cli::try_parse_from([
            "spec",
            "pair",
            "guarantee-discharge",
            "source",
            "target",
            "--relied",
            "awaited",
        ])
        .unwrap();
        let Command::Pair(args) = cli.command else {
            panic!("expected pair command")
        };
        assert!(matches!(args.kind, PairingKind::GuaranteeDischarge));
        assert_eq!(args.source, "source");
        assert_eq!(args.target, "target");
        assert_eq!(args.relied, "awaited");
        assert!(
            Cli::try_parse_from(["spec", "pair", "guarantee-discharge", "source", "target"])
                .is_err()
        );
    }

    #[test]
    fn graph_without_arguments_selects_the_whole_graph() {
        let args = parse_graph(&["spec", "graph"]);

        assert_eq!(args.server, "http://127.0.0.1:50051");
        assert_eq!(args.width, None);
        assert!(!args.ledger);
        assert!(!args.current);
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
        assert!(!args.ledger);
        assert!(!args.current);
    }

    #[test]
    fn graph_current_and_ledger_are_distinct_views() {
        let current = parse_graph(&["spec", "graph", "--current"]);
        assert!(current.current);
        assert!(!current.ledger);

        let ledger = parse_graph(&["spec", "graph", "--ledger"]);
        assert!(ledger.ledger);
        assert!(!ledger.current);

        assert!(Cli::try_parse_from(["spec", "graph", "--current", "--ledger"]).is_err());
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
