mod service;

use service::SpecOracleService;
use std::path::PathBuf;
use tonic::transport::Server;
use tracing_subscriber::EnvFilter;

pub mod proto {
    tonic::include_proto!("spec_oracle");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    let addr = "[::1]:50051".parse()?;
    let store_path = std::env::var("SPECD_STORE_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            dirs_or_default().join("spec-oracle").join("specs.json")
        });

    tracing::info!("specd listening on {}", addr);
    tracing::info!("store path: {}", store_path.display());

    let svc = SpecOracleService::new(store_path)?;

    Server::builder()
        .add_service(proto::spec_oracle_server::SpecOracleServer::new(svc))
        .serve(addr)
        .await?;

    Ok(())
}

fn dirs_or_default() -> PathBuf {
    std::env::var("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("."))
}
