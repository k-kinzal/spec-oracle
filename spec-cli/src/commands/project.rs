//! Project management commands (gRPC only)
//!
//! Implements create, list, use (switch), delete, and current project commands.

use crate::proto::{self, spec_oracle_client::SpecOracleClient};
use crate::ProjectCommands;
use tonic::Request;

type Client = SpecOracleClient<tonic::transport::Channel>;

/// Dispatch project subcommands
pub async fn dispatch_project(
    client: &mut Client,
    cmd: ProjectCommands,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        ProjectCommands::Create { name, description } => {
            execute_project_create(client, name, description).await
        }
        ProjectCommands::List => {
            execute_project_list(client).await
        }
        ProjectCommands::Use { name } => {
            execute_project_use(client, name).await
        }
        ProjectCommands::Delete { name } => {
            execute_project_delete(client, name).await
        }
        ProjectCommands::Current => {
            execute_project_current(client).await
        }
        ProjectCommands::Import { name, description, path } => {
            execute_project_import(client, name, description, path).await
        }
    }
}

async fn execute_project_create(
    client: &mut Client,
    name: String,
    description: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .create_project(Request::new(proto::CreateProjectRequest {
            name: name.clone(),
            description: description.clone(),
            storage_backend: proto::StorageBackend::LocalFile.into(),
        }))
        .await?;

    if let Some(project) = resp.into_inner().project {
        println!("Project created: {}", project.name);
        if !project.description.is_empty() {
            println!("  Description: {}", project.description);
        }
        println!("  Storage: local file");
    }

    Ok(())
}

async fn execute_project_list(
    client: &mut Client,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .list_projects(Request::new(proto::ListProjectsRequest {}))
        .await?;
    let projects = resp.into_inner().projects;

    // Get current project for marking
    let current = client
        .get_current_project(Request::new(proto::GetCurrentProjectRequest {}))
        .await
        .ok()
        .and_then(|r| r.into_inner().project)
        .map(|p| p.name);

    if projects.is_empty() {
        println!("No projects found.");
        println!("\nCreate one with: spec project create <name>");
    } else {
        println!("Projects ({}):", projects.len());
        println!();
        for project in &projects {
            let is_current = current.as_ref() == Some(&project.name);
            let marker = if is_current { " (active)" } else { "" };
            println!("  {}{}", project.name, marker);
            if !project.description.is_empty() {
                println!("    Description: {}", project.description);
            }
            println!("    Nodes: {}, Edges: {}", project.node_count, project.edge_count);
        }
    }

    Ok(())
}

async fn execute_project_use(
    client: &mut Client,
    name: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .switch_project(Request::new(proto::SwitchProjectRequest {
            name: name.clone(),
        }))
        .await?;

    if let Some(project) = resp.into_inner().project {
        println!("Switched to project: {}", project.name);
        println!("  Nodes: {}, Edges: {}", project.node_count, project.edge_count);
    }

    Ok(())
}

async fn execute_project_delete(
    client: &mut Client,
    name: String,
) -> Result<(), Box<dyn std::error::Error>> {
    client
        .delete_project(Request::new(proto::DeleteProjectRequest {
            name: name.clone(),
        }))
        .await?;

    println!("Project deleted: {}", name);

    Ok(())
}

async fn execute_project_current(
    client: &mut Client,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .get_current_project(Request::new(proto::GetCurrentProjectRequest {}))
        .await?;

    if let Some(project) = resp.into_inner().project {
        println!("Current project: {}", project.name);
        if !project.description.is_empty() {
            println!("  Description: {}", project.description);
        }
        println!("  Nodes: {}, Edges: {}", project.node_count, project.edge_count);
    } else {
        println!("No current project set.");
        println!("Use 'spec project use <name>' to select a project.");
    }

    Ok(())
}

async fn execute_project_import(
    client: &mut Client,
    name: String,
    description: String,
    path: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = client
        .import_project(Request::new(proto::ImportProjectRequest {
            name: name.clone(),
            description: description.clone(),
            spec_directory_path: path.clone(),
        }))
        .await?;

    let inner = resp.into_inner();
    if let Some(project) = inner.project {
        println!("✅ Project imported successfully!");
        println!("  Name: {}", project.name);
        if !project.description.is_empty() {
            println!("  Description: {}", project.description);
        }
        println!("  Imported:");
        println!("    Nodes: {}", inner.nodes_imported);
        println!("    Edges: {}", inner.edges_imported);
        println!("    Universes: {}", inner.universes_created);
        println!();
        println!("💡 Use 'spec project use {}' to switch to this project", project.name);
    }

    Ok(())
}
