//! Integration tests for UDA/f model operations
//!
//! Tests Universe, Domain, Transform, AdmissibleSet operations.

use specd::proto::spec_oracle_client::SpecOracleClient;
use specd::proto::*;
use std::collections::HashMap;
use tonic::Request;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// Helper function to create a test client
async fn test_client() -> Result<SpecOracleClient<tonic::transport::Channel>> {
    let client = SpecOracleClient::connect("http://[::1]:50051").await?;
    Ok(client)
}

#[tokio::test]
async fn test_universe_operations() -> Result<()> {
    let mut client = test_client().await?;

    // Create universe
    let resp = client
        .create_universe(Request::new(CreateUniverseRequest {
            layer: 1,
            name: "Test-U1".to_string(),
            description: "Test formal universe".to_string(),
        }))
        .await?;

    let universe = resp.into_inner().universe.unwrap();
    assert_eq!(universe.name, "Test-U1");
    assert_eq!(universe.layer, 1);

    // Get universe
    let resp = client
        .get_universe(Request::new(GetUniverseRequest {
            id: universe.id.clone(),
        }))
        .await?;

    let retrieved = resp.into_inner().universe.unwrap();
    assert_eq!(retrieved.id, universe.id);
    assert_eq!(retrieved.name, "Test-U1");

    // List universes
    let resp = client
        .list_universes(Request::new(ListUniversesRequest {}))
        .await?;

    let universes = resp.into_inner().universes;
    assert!(universes.iter().any(|u| u.id == universe.id));

    // Delete universe
    client
        .delete_universe(Request::new(DeleteUniverseRequest {
            id: universe.id.clone(),
        }))
        .await?;

    // Verify deletion
    let result = client
        .get_universe(Request::new(GetUniverseRequest {
            id: universe.id,
        }))
        .await;

    assert!(result.is_err());

    Ok(())
}

#[tokio::test]
async fn test_domain_operations() -> Result<()> {
    let mut client = test_client().await?;

    // Create universe first
    let universe_resp = client
        .create_universe(Request::new(CreateUniverseRequest {
            layer: 1,
            name: "Test-Universe-For-Domain".to_string(),
            description: "Universe for domain testing".to_string(),
        }))
        .await?;

    let universe_id = universe_resp.into_inner().universe.unwrap().id;

    // Create domain
    let resp = client
        .create_domain(Request::new(CreateDomainRequest {
            name: "Test Domain".to_string(),
            description: "A test domain".to_string(),
            universe_id: universe_id.clone(),
        }))
        .await?;

    let domain = resp.into_inner().domain.unwrap();
    assert_eq!(domain.name, "Test Domain");
    assert_eq!(domain.universe_id, universe_id);

    // Get domain
    let resp = client
        .get_domain(Request::new(GetDomainRequest {
            id: domain.id.clone(),
        }))
        .await?;

    let retrieved = resp.into_inner().domain.unwrap();
    assert_eq!(retrieved.id, domain.id);

    // List domains
    let resp = client
        .list_domains(Request::new(ListDomainsRequest {
            universe_id: universe_id.clone(),
        }))
        .await?;

    let domains = resp.into_inner().domains;
    assert!(domains.iter().any(|d| d.id == domain.id));

    // Cleanup
    client
        .delete_universe(Request::new(DeleteUniverseRequest {
            id: universe_id,
        }))
        .await?;

    Ok(())
}

#[tokio::test]
async fn test_transform_operations() -> Result<()> {
    let mut client = test_client().await?;

    // Create source and target universes
    let u1_resp = client
        .create_universe(Request::new(CreateUniverseRequest {
            layer: 1,
            name: "Source-U1".to_string(),
            description: "Source universe".to_string(),
        }))
        .await?;

    let u2_resp = client
        .create_universe(Request::new(CreateUniverseRequest {
            layer: 2,
            name: "Target-U2".to_string(),
            description: "Target universe".to_string(),
        }))
        .await?;

    let source_id = u1_resp.into_inner().universe.unwrap().id;
    let target_id = u2_resp.into_inner().universe.unwrap().id;

    // Create transform
    let resp = client
        .create_transform(Request::new(CreateTransformRequest {
            source_universe: source_id.clone(),
            target_universe: target_id.clone(),
            description: "Test forward transform".to_string(),
            kind: 1, // FORWARD
            strategy: Some(UdafTransformStrategy {
                strategy_type: "manual".to_string(),
                config: HashMap::new(),
            }),
        }))
        .await?;

    let transform = resp.into_inner().transform.unwrap();
    assert_eq!(transform.source_universe, source_id);
    assert_eq!(transform.target_universe, target_id);

    // Get transform
    let resp = client
        .get_transform(Request::new(GetTransformRequest {
            id: transform.id.clone(),
        }))
        .await?;

    let retrieved = resp.into_inner().transform.unwrap();
    assert_eq!(retrieved.id, transform.id);

    // List transforms
    let resp = client
        .list_transforms(Request::new(ListTransformsRequest {
            universe_id: String::new(),
        }))
        .await?;

    let transforms = resp.into_inner().transforms;
    assert!(transforms.iter().any(|t| t.id == transform.id));

    // Cleanup
    client
        .delete_universe(Request::new(DeleteUniverseRequest { id: source_id }))
        .await?;

    client
        .delete_universe(Request::new(DeleteUniverseRequest { id: target_id }))
        .await?;

    Ok(())
}

#[tokio::test]
async fn test_model_sync_and_validate() -> Result<()> {
    let mut client = test_client().await?;

    // Sync model
    let resp = client
        .sync_model(Request::new(SyncModelRequest {
            export_proof_metadata: false,
        }))
        .await?;

    let sync_result = resp.into_inner();
    assert!(sync_result.universes_count >= 1); // At least U0

    // Validate model
    let resp = client
        .validate_model(Request::new(ValidateModelRequest {}))
        .await?;

    let validation = resp.into_inner();
    assert!(validation.is_valid);
    assert!(validation.errors.is_empty());

    Ok(())
}
