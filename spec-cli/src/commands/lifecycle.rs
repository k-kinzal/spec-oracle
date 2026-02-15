/// Lifecycle management commands
///
/// Provides commands to manage specification lifecycle status:
/// - active: Normal specifications (default)
/// - deprecated: Still checked but shows warnings
/// - archived: Excluded from checks, kept for history

use spec_core::Store;
use std::error::Error;

/// Set specification status in metadata
fn set_status(
    store: &mut Store,
    id: &str,
    status: Option<&str>, // None means remove status (activate)
) -> Result<(), Box<dyn Error>> {
    let mut graph = store.load()?;

    // Find node by exact ID or prefix match
    let node_id = graph.nodes()
        .find(|n| n.id == id || n.id.starts_with(id))
        .map(|n| n.id.clone())
        .ok_or_else(|| format!("Specification not found: {}", id))?;

    // Update metadata
    if let Some(status_value) = status {
        graph.update_node_metadata(&node_id, "status".to_string(), status_value.to_string())
            .ok_or_else(|| format!("Failed to update specification: {}", node_id))?;
        println!("✓ Specification [{}] marked as {}", &node_id[..8], status_value);
    } else {
        // To remove status, we need to update with empty value or use a special marker
        // For now, we'll use a special value "active" to indicate active status
        graph.update_node_metadata(&node_id, "status".to_string(), "active".to_string())
            .ok_or_else(|| format!("Failed to update specification: {}", node_id))?;
        println!("✓ Specification [{}] activated", &node_id[..8]);
    }

    // Save graph
    store.save(&graph)?;

    Ok(())
}

/// Archive a specification (status = "archived")
pub fn execute_archive(store: &mut Store, id: String) -> Result<(), Box<dyn Error>> {
    set_status(store, &id, Some("archived"))
}

/// Deprecate a specification (status = "deprecated")
pub fn execute_deprecate(store: &mut Store, id: String) -> Result<(), Box<dyn Error>> {
    set_status(store, &id, Some("deprecated"))
}

/// Activate a specification (remove status)
pub fn execute_activate(store: &mut Store, id: String) -> Result<(), Box<dyn Error>> {
    set_status(store, &id, None)
}
