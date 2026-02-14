/// Migrate specifications from JSON file to directory format
///
/// Converts .spec/specs.json to directory structure:
/// - .spec/nodes/<uuid>.yaml (one file per specification)
/// - .spec/edges.yaml (all relationships)
///
/// Benefits:
/// - Prevents merge conflicts in team development
/// - Human-readable diffs for spec reviews
/// - File-level granularity for version control

use spec_core::{DirectoryStore, FileStore, Store};
use std::path::Path;

pub fn execute_migrate(
    source: Option<String>,
    target: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let source_path = source.unwrap_or_else(|| ".spec/specs.json".to_string());
    let target_path = target.unwrap_or_else(|| ".spec".to_string());

    let source_path = Path::new(&source_path);
    let target_path = Path::new(&target_path);

    if !source_path.exists() {
        eprintln!("✗ Error: Source file not found: {}", source_path.display());
        eprintln!("  Expected a specs.json file");
        return Ok(());
    }

    // Check if target directory already has nodes/ (already migrated)
    let nodes_dir = target_path.join("nodes");
    if nodes_dir.exists() && nodes_dir.is_dir() {
        eprintln!("✗ Error: Target directory already contains nodes/");
        eprintln!("  Migration appears to have already been performed");
        eprintln!("  Path: {}", nodes_dir.display());
        return Ok(());
    }

    println!("🔄 Migrating specifications...");
    println!("  From: {}", source_path.display());
    println!("  To:   {}/nodes/", target_path.display());

    // Load from JSON file
    let file_store = FileStore::new(source_path);
    let graph = file_store.load()?;

    println!("  📊 Loaded {} nodes, {} edges", graph.node_count(), graph.edge_count());

    // Save to directory format
    let dir_store = DirectoryStore::new(target_path);
    dir_store.save(&graph)?;

    println!("  ✅ Migration complete!");
    println!();
    println!("📁 New structure:");
    println!("  .spec/nodes/       - {} YAML files (one per specification)", graph.node_count());
    println!("  .spec/edges.yaml   - Relationship definitions");
    println!();
    println!("✨ Benefits:");
    println!("  • Merge conflicts: Minimized (different files)");
    println!("  • Diffs: Human-readable (YAML format)");
    println!("  • Reviews: File-level granularity");
    println!();
    println!("⚠️  Note: The original specs.json has been preserved.");
    println!("   You can safely delete it after verifying the migration:");
    println!("   rm {}", source_path.display());

    Ok(())
}
