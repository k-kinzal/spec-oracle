mod config;
mod migration;
mod model_service;
mod project;
mod service;
mod storage;

use config::SpecdConfig;
use project::ProjectManager;
use service::SpecOracleService;
use tonic::transport::Server;
use tracing_subscriber::EnvFilter;

pub mod proto {
    tonic::include_proto!("spec_oracle");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Load configuration
    let config = SpecdConfig::load_or_default()?;

    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| EnvFilter::new(&config.log_level))
        )
        .init();

    tracing::info!("Starting specd...");
    tracing::info!("Projects directory: {}", config.default_path.display());

    // Initialize project manager
    let mut project_manager = ProjectManager::new(config.default_path.clone());

    // Discover existing projects
    project_manager.discover_projects()?;

    // Ensure default project exists
    project_manager.ensure_default()?;

    tracing::info!("Loaded {} project(s)", project_manager.list_projects()?.len());

    // Create gRPC service
    let addr = config.listen_address.parse()?;
    let svc = SpecOracleService::new(project_manager)?;

    tracing::info!("specd listening on {}", addr);

    // Start gRPC server
    Server::builder()
        .add_service(proto::spec_oracle_server::SpecOracleServer::new(svc))
        .serve(addr)
        .await?;

    Ok(())
}
