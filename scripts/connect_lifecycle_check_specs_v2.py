#!/usr/bin/env python3
"""Connect lifecycle-aware check specs to lifecycle management specs (v2 - correct format)"""

import os
import yaml
from pathlib import Path
import time

def load_spec(spec_dir, spec_id_prefix):
    """Load a spec by ID prefix"""
    for yaml_file in spec_dir.glob("*.yaml"):
        with open(yaml_file, 'r') as f:
            data = yaml.safe_load(f)
            if data['id'].startswith(spec_id_prefix):
                return data['id'], yaml_file
    return None, None

def load_edges(edges_file):
    """Load edges.yaml"""
    if edges_file.exists():
        with open(edges_file, 'r') as f:
            edges = yaml.safe_load(f)
            return edges if edges else []
    return []

def save_edges(edges_file, edges):
    """Save edges to edges.yaml"""
    with open(edges_file, 'w') as f:
        yaml.dump(edges, f, default_flow_style=False, sort_keys=False)

def add_edge(edges, source_id, target_id, kind):
    """Add an edge if it doesn't exist"""
    edge_id = f"{source_id[:8]}-{kind.lower()}-{target_id[:8]}"

    # Check if edge already exists
    for edge in edges:
        if (edge['source'] == source_id and
            edge['target'] == target_id and
            edge['kind'] == kind):
            print(f"  ⏭️  Edge already exists: {kind} {source_id[:8]} → {target_id[:8]}")
            return False

    edges.append({
        'source': source_id,
        'target': target_id,
        'id': edge_id,
        'kind': kind,
        'metadata': {},
        'created_at': int(time.time())
    })
    print(f"  ✅ Added edge: {kind} {source_id[:8]} → {target_id[:8]}")
    return True

def main():
    spec_dir = Path(__file__).parent.parent / ".spec" / "nodes"
    edges_file = Path(__file__).parent.parent / ".spec" / "edges.yaml"

    print("🔗 Connecting lifecycle-aware check specifications...\n")

    # Find specs
    check_respect_id, _ = load_spec(spec_dir, "fb893fba")  # Check must respect lifecycle
    check_display_id, _ = load_spec(spec_dir, "2cd12c5e")  # Check displays status
    lifecycle_status_id, _ = load_spec(spec_dir, "4cf50a75")  # Lifecycle status support
    metadata_storage_id, _ = load_spec(spec_dir, "80b66322")  # Metadata storage

    if not all([check_respect_id, check_display_id, lifecycle_status_id, metadata_storage_id]):
        print("❌ Could not find all required specifications")
        return

    print(f"Found specifications:")
    print(f"  - Check respect lifecycle: {check_respect_id[:8]}")
    print(f"  - Check display status: {check_display_id[:8]}")
    print(f"  - Lifecycle status support: {lifecycle_status_id[:8]}")
    print(f"  - Metadata storage: {metadata_storage_id[:8]}")
    print()

    # Load existing edges
    edges = load_edges(edges_file)
    initial_count = len(edges)
    print(f"Loaded {initial_count} existing edges\n")

    # Add new edges
    print("Adding relationships:")
    added = 0

    # Check respect lifecycle Refines lifecycle status support
    if add_edge(edges, check_respect_id, lifecycle_status_id, "Refines"):
        added += 1

    # Check display status Refines lifecycle status support
    if add_edge(edges, check_display_id, lifecycle_status_id, "Refines"):
        added += 1

    # Check respect lifecycle depends on metadata storage
    if add_edge(edges, check_respect_id, metadata_storage_id, "DependsOn"):
        added += 1

    # Check display status Refines check respect lifecycle (display is a refinement of respect)
    if add_edge(edges, check_display_id, check_respect_id, "Refines"):
        added += 1

    # Save edges
    if added > 0:
        save_edges(edges_file, edges)
        print(f"\n✅ Added {added} new edge(s)")
        print(f"📊 Total edges: {len(edges)} (was {initial_count})")
    else:
        print("\n✅ All edges already exist")

if __name__ == "__main__":
    main()
