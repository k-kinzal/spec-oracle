#!/usr/bin/env python3
"""Connect isolated real specifications to appropriate parents."""

import yaml
import uuid
from pathlib import Path

# Manual mapping of isolated specs to parent specs based on semantic analysis
CONNECTIONS = {
    # Test scenarios -> General scenario requirement
    "14ba122f": ("bc5ad960", "Refines"),
    "50ed58d6": ("bc5ad960", "Refines"),
    "7bcc1eca": ("bc5ad960", "Refines"),
    "48b035be": ("bc5ad960", "Refines"),
    "33912c9c": ("bc5ad960", "Refines"),
    "ba2882a1": ("bc5ad960", "Refines"),

    # Extraction/AI assertions -> Reverse mapping parent
    "364af100": ("bc5ad960", "Refines"),
    "b549f3a8": ("bc5ad960", "Refines"),
    "49b943da": ("bc5ad960", "Refines"),
    "6fe50517": ("bc5ad960", "Refines"),
    "0a26c5b6": ("bc5ad960", "Refines"),

    # ORACLE assertion -> core concept
    "e9b11d11": ("bc5ad960", "Refines"),

    # CLI constraints -> CLI parent
    "e9c466e9": ("c6119c42", "Refines"),
    "41d13458": ("c6119c42", "Refines"),

    # Authentication constraint -> core concept
    "2e91fd85": ("bc5ad960", "Refines"),

    # Concepts guide assertion -> core concept
    "86c27166": ("bc5ad960", "Refines"),

    # Debug test node - DELETE
    "f1ff674b": ("DELETE", ""),
}

def connect_specs():
    """Connect isolated specifications."""
    nodes_dir = Path.home() / "Projects/spec-oracle/.spec/nodes"
    edges_file = Path.home() / "Projects/spec-oracle/.spec/edges.yaml"

    # Load edges (it's a list, not a dict)
    with open(edges_file, 'r') as f:
        edges = yaml.safe_load(f) or []

    initial_edge_count = len(edges)
    print(f"📊 Initial state: {initial_edge_count} edges\n")

    connected = 0
    deleted = 0
    skipped = 0

    for short_id, (parent_short_id, edge_kind) in CONNECTIONS.items():
        # Find full IDs
        source_files = list(nodes_dir.glob(f"{short_id}*.yaml"))
        if not source_files:
            print(f"  ⚠️  Source {short_id} not found, skipping")
            skipped += 1
            continue

        source_id = yaml.safe_load(open(source_files[0]))['id']

        # Handle DELETE action
        if parent_short_id == "DELETE":
            source_files[0].unlink()
            deleted += 1
            print(f"  ✓ Deleted {short_id} (test artifact)")
            continue

        # Find parent
        parent_files = list(nodes_dir.glob(f"{parent_short_id}*.yaml"))
        if not parent_files:
            print(f"  ⚠️  Parent {parent_short_id} not found for {short_id}, skipping")
            skipped += 1
            continue

        parent_id = yaml.safe_load(open(parent_files[0]))['id']

        # Check if edge already exists
        edge_exists = any(
            (e['source'] == parent_id and e['target'] == source_id) or
            (e['source'] == source_id and e['target'] == parent_id)
            for e in edges
        )

        if edge_exists:
            print(f"  ⏭️  Edge already exists: {short_id} <-> {parent_short_id}")
            skipped += 1
            continue

        # Create edge
        import time
        edge = {
            'source': parent_id,
            'target': source_id,
            'id': str(uuid.uuid4()),
            'kind': edge_kind,
            'created_at': int(time.time()),
            'metadata': {
                'auto_generated': 'true',
                'reason': 'Connect isolated spec to parent'
            }
        }
        edges.append(edge)
        connected += 1

        # Load spec content for display
        source_content = yaml.safe_load(open(source_files[0]))['content'][:60]
        parent_content = yaml.safe_load(open(parent_files[0]))['content'][:60]

        print(f"  ✓ Connected [{short_id}] {source_content}...")
        print(f"             -> [{parent_short_id}] {parent_content}...")

    # Save edges
    if connected > 0 or deleted > 0:
        with open(edges_file, 'w') as f:
            yaml.dump(edges, f, default_flow_style=False, sort_keys=False)

        print(f"\n✅ Results:")
        print(f"  Connections created: {connected}")
        print(f"  Nodes deleted: {deleted}")
        print(f"  Skipped: {skipped}")
        print(f"  Total edges: {len(edges)} (was {initial_edge_count})")
    else:
        print(f"\n  No changes needed (skipped: {skipped})")

if __name__ == "__main__":
    connect_specs()
