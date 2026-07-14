//! `specd` — the spec-oracle ingest daemon.
//!
//! Serves the `spec_oracle.v1.SpecificationGraph` gRPC contract. Because capture runs
//! against *this process's* filesystem and git, the daemon must run where the
//! evidence lives (or where a checkout of it is reachable). ArangoDB credentials
//! are read from the environment only (`ARANGODB_USER` / `ARANGODB_PASSWORD`), so
//! they never reach the process table or shell history.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use clap::Parser;
use tonic::transport::Server;
use tracing::Instrument;

use so_daemon::add_mailbox::AddMailbox;
use so_daemon::arango::{ArangoConfig, ArangoNodeStore};
use so_daemon::jobs::JobMailbox;
use so_daemon::mailbox::NodeAdded;
use so_daemon::service::SpecificationGraphService;
use so_daemon::store::{FileBlobStore, GraphStore, InMemoryNodeStore};
use so_protocol::pb::specification_graph_server::SpecificationGraphServer;

/// Which node-store backend `specd` serves from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
enum StoreKind {
    /// Persist to ArangoDB (the production default).
    Arango,
    /// A non-persistent in-memory store — no database required. For local runs,
    /// demos, and the graph UI without ArangoDB; data is lost on restart.
    Memory,
}

#[derive(Parser)]
#[command(
    name = "specd",
    version,
    about = "The spec-oracle ingest daemon: a gRPC service that captures evidence and persists specification nodes."
)]
struct Args {
    /// Address to listen on for gRPC.
    #[arg(
        long = "listen",
        env = "SPEC_ORACLE_LISTEN",
        default_value = "127.0.0.1:50051",
        value_name = "ADDR"
    )]
    listen: SocketAddr,

    /// Directory whose `.spec-oracle/blobs/` holds the content-addressed snapshot
    /// bytes (defaults to the current directory). Specification nodes live in
    /// ArangoDB, not here.
    #[arg(long = "dir", env = "SPEC_ORACLE_DIR", value_name = "PATH")]
    dir: Option<PathBuf>,

    /// ArangoDB endpoint. The same product runs locally, self-hosted, or managed
    /// — this only points at wherever it currently lives.
    #[arg(
        long = "arango-url",
        env = "ARANGODB_URL",
        default_value = "http://localhost:8529",
        value_name = "URL"
    )]
    arango_url: String,

    /// ArangoDB database name.
    #[arg(
        long = "arango-db",
        env = "ARANGODB_DB",
        default_value = "spec_oracle",
        value_name = "NAME"
    )]
    arango_db: String,

    /// Node-store backend. `arango` (default) persists to ArangoDB; `memory`
    /// runs without a database (non-persistent, for local dev/demos/UI). With
    /// `memory` the `--arango-*` flags are ignored.
    #[arg(
        long = "store",
        env = "SPEC_ORACLE_STORE",
        value_enum,
        default_value_t = StoreKind::Arango,
        value_name = "BACKEND"
    )]
    store: StoreKind,
}

fn main() -> ExitCode {
    let _telemetry = match so_tracing::init("specd", env!("CARGO_PKG_VERSION")) {
        Ok(guard) => guard,
        Err(e) => {
            eprintln!("error: failed to initialize telemetry: {e:#}");
            return ExitCode::FAILURE;
        }
    };

    let args = Args::parse();
    match run(args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
    }
}

fn run(args: Args) -> anyhow::Result<()> {
    let run_span = tracing::info_span!(
        "spec.daemon.run",
        "server.address" = %args.listen,
        "db.system" = "arangodb",
        "db.name" = %args.arango_db,
    );
    let run_entered = run_span.enter();

    // Build the stores in a synchronous context, before the tokio runtime exists.
    // The ArangoDB driver is blocking and constructs its own HTTP client; doing it
    // here avoids a "runtime within a runtime" panic once we enter `block_on`.
    let base_dir = args.dir.unwrap_or_else(|| PathBuf::from("."));
    let blobs_dir = base_dir.join(".spec-oracle").join("blobs");
    tracing::info!("blob.dir" = %blobs_dir.display(), "opening blob store");
    let blobs = FileBlobStore::open(&blobs_dir)?;

    // Build the selected node-store backend. Both implement the same
    // `GraphStore` seam, so the service is identical either way.
    let nodes: Arc<dyn GraphStore + Send + Sync> = match args.store {
        StoreKind::Arango => {
            // Credentials come from the environment, never the command line, so
            // they do not leak into shell history or the process table.
            let username = std::env::var("ARANGODB_USER").unwrap_or_else(|_| "root".to_string());
            let password = std::env::var("ARANGODB_PASSWORD").unwrap_or_default();
            let cfg = ArangoConfig {
                url: &args.arango_url,
                database: &args.arango_db,
                username: &username,
                password: &password,
            };
            tracing::info!("db.url" = %args.arango_url, "connecting to ArangoDB");
            Arc::new(ArangoNodeStore::connect(&cfg)?)
        }
        StoreKind::Memory => {
            tracing::warn!(
                "using the in-memory node store: nodes are NOT persisted and are lost on restart"
            );
            Arc::new(InMemoryNodeStore::new())
        }
    };

    let blobs: Arc<dyn so_daemon::store::BlobStore + Send + Sync> = Arc::new(blobs);

    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    drop(run_entered);
    runtime.block_on(
        async move {
            let (jobs, jobs_task) = JobMailbox::start(nodes.clone(), blobs.clone());
            let scheduled = schedule_job_reconciliation(nodes.clone(), &jobs).await?;
            tracing::info!(
                "job.reconciliation.scheduled" = scheduled,
                "post-acceptance Job reconciliation scheduled"
            );
            let (adds, adds_task) = AddMailbox::start(nodes.clone(), jobs.clone());
            let service = SpecificationGraphService::new(nodes, adds.clone());
            tracing::info!("specd listening");
            let serve_result = Server::builder()
                .add_service(SpecificationGraphServer::new(service))
                .serve_with_shutdown(args.listen, shutdown_signal())
                .await;

            tracing::info!("draining Add Mailbox");
            adds.shutdown().await?;
            adds_task.await?;
            tracing::info!("draining Job Mailbox");
            jobs.shutdown().await?;
            jobs_task.await?;
            serve_result?;
            Ok::<(), anyhow::Error>(())
        }
        .instrument(run_span),
    )?;
    Ok(())
}

async fn schedule_job_reconciliation(
    nodes: Arc<dyn GraphStore + Send + Sync>,
    jobs: &JobMailbox,
) -> anyhow::Result<u64> {
    const PAGE_SIZE: usize = 500;
    let message_id = format!(
        "job-reconciliation:{}:{}",
        so_daemon::evidence_capture::CAPTURE_VERSION,
        so_daemon::graph_generation::reconciliation_version()
    );
    let mut cursor: Option<String> = None;
    let mut scheduled = 0_u64;
    loop {
        let store = nodes.clone();
        let after = cursor.clone();
        let page =
            tokio::task::spawn_blocking(move || store.list_nodes(after.as_deref(), PAGE_SIZE))
                .await??;
        for node in page.nodes {
            if so_daemon::evidence_capture::needs_capture(&node)
                || so_daemon::graph_generation::needs_generation(&node)
                || so_daemon::github::needs_resolution(&node)
            {
                jobs.node_added(NodeAdded::new(&message_id, node)).await?;
                scheduled = scheduled.saturating_add(1);
            }
        }
        match page.next_cursor {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(scheduled)
}

async fn shutdown_signal() {
    match tokio::signal::ctrl_c().await {
        Ok(()) => tracing::info!("shutdown signal received"),
        Err(e) => tracing::warn!("error" = %e, "failed to listen for shutdown signal"),
    }
}
