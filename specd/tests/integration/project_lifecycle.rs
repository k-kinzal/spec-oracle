//! Integration tests for project lifecycle
//!
//! Tests project creation, usage, deletion, and isolation.

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
async fn test_project_create_list_delete() -> Result<()> {
    let mut client = test_client().await?;

    // Create project
    let resp = client
        .create_project(Request::new(CreateProjectRequest {
            name: "integration-test-1".to_string(),
            description: "Integration test project".to_string(),
        }))
        .await?;

    let project = resp.into_inner().project.unwrap();
    assert_eq!(project.name, "integration-test-1");
    assert_eq!(project.description, "Integration test project");

    // List projects
    let resp = client
        .list_projects(Request::new(ListProjectsRequest {}))
        .await?;

    let projects = resp.into_inner().projects;
    assert!(projects.iter().any(|p| p.name == "integration-test-1"));

    // Delete project
    client
        .delete_project(Request::new(DeleteProjectRequest {
            name: "integration-test-1".to_string(),
        }))
        .await?;

    // Verify deletion
    let resp = client
        .list_projects(Request::new(ListProjectsRequest {}))
        .await?;

    let projects = resp.into_inner().projects;
    assert!(!projects.iter().any(|p| p.name == "integration-test-1"));

    Ok(())
}

#[tokio::test]
async fn test_project_isolation() -> Result<()> {
    let mut client = test_client().await?;

    // Create two projects
    client
        .create_project(Request::new(CreateProjectRequest {
            name: "project-a".to_string(),
            description: "Project A".to_string(),
        }))
        .await?;

    client
        .create_project(Request::new(CreateProjectRequest {
            name: "project-b".to_string(),
            description: "Project B".to_string(),
        }))
        .await?;

    // Switch to project-a and add a node
    client
        .switch_project(Request::new(SwitchProjectRequest {
            name: "project-a".to_string(),
        }))
        .await?;

    let resp = client
        .add_node(Request::new(AddNodeRequest {
            content: "Spec in project A".to_string(),
            kind: 0, // Assertion
            metadata: HashMap::new(),
        }))
        .await?;

    let node_a_id = resp.into_inner().node.unwrap().id;

    // Switch to project-b and add a different node
    client
        .switch_project(Request::new(SwitchProjectRequest {
            name: "project-b".to_string(),
        }))
        .await?;

    client
        .add_node(Request::new(AddNodeRequest {
            content: "Spec in project B".to_string(),
            kind: 0, // Assertion
            metadata: HashMap::new(),
        }))
        .await?;

    // Verify project-a only has its own node
    client
        .switch_project(Request::new(SwitchProjectRequest {
            name: "project-a".to_string(),
        }))
        .await?;

    let resp = client
        .list_nodes(Request::new(ListNodesRequest {
            kind_filter: 0,
        }))
        .await?;

    let nodes = resp.into_inner().nodes;
    assert_eq!(nodes.len(), 1);
    assert_eq!(nodes[0].id, node_a_id);
    assert_eq!(nodes[0].content, "Spec in project A");

    // Verify project-b only has its own node
    client
        .switch_project(Request::new(SwitchProjectRequest {
            name: "project-b".to_string(),
        }))
        .await?;

    let resp = client
        .list_nodes(Request::new(ListNodesRequest {
            kind_filter: 0,
        }))
        .await?;

    let nodes = resp.into_inner().nodes;
    assert_eq!(nodes.len(), 1);
    assert_eq!(nodes[0].content, "Spec in project B");

    // Cleanup
    client
        .delete_project(Request::new(DeleteProjectRequest {
            name: "project-a".to_string(),
        }))
        .await?;

    client
        .delete_project(Request::new(DeleteProjectRequest {
            name: "project-b".to_string(),
        }))
        .await?;

    Ok(())
}

#[tokio::test]
async fn test_current_project() -> Result<()> {
    let mut client = test_client().await?;

    // Get current project (should be default or spec-oracle)
    let resp = client
        .get_current_project(Request::new(GetCurrentProjectRequest {}))
        .await?;

    let current = resp.into_inner().project;
    assert!(current.is_some());

    // Create and switch to new project
    client
        .create_project(Request::new(CreateProjectRequest {
            name: "test-current".to_string(),
            description: "Test current project".to_string(),
        }))
        .await?;

    client
        .switch_project(Request::new(SwitchProjectRequest {
            name: "test-current".to_string(),
        }))
        .await?;

    // Verify current project changed
    let resp = client
        .get_current_project(Request::new(GetCurrentProjectRequest {}))
        .await?;

    let current = resp.into_inner().project.unwrap();
    assert_eq!(current.name, "test-current");

    // Cleanup
    client
        .delete_project(Request::new(DeleteProjectRequest {
            name: "test-current".to_string(),
        }))
        .await?;

    Ok(())
}
