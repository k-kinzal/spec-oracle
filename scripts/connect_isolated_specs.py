#!/usr/bin/env python3
"""
Connect isolated specifications to appropriate parent specifications.
This script analyzes isolated specs and connects them based on semantic similarity.
"""

import json
import os
import yaml
from pathlib import Path
from typing import Dict, List, Set

# Mapping of isolated spec IDs to their appropriate parent specs (manually curated)
CONNECTIONS = {
    # Test scenarios -> Testing requirements
    "33912c9c": {"parent": "7807965f", "kind": "Refines"},  # load nonexistent -> Test specifications
    "ba2882a1": {"parent": "7807965f", "kind": "Refines"},  # detect inter universe inconsistencies missing transform
    "7bcc1eca": {"parent": "7807965f", "kind": "Refines"},  # detect inter universe inconsistencies with transform
    "50ed58d6": {"parent": "0a26c5b6", "kind": "Refines"},  # authentication required -> Authentication requirement

    # Password specs -> Password requirements
    "5fb5017a": {"parent": "e784e25b", "kind": "Refines"},  # Password >= 8 chars
    "543a0d34": {"parent": "e784e25b", "kind": "Refines"},  # validate_password invariant

    # User authentication specs -> Auth requirement
    "e61c0d6d": {"parent": "0a26c5b6", "kind": "Refines"},  # User must authenticate invariant
    "2e91fd85": {"parent": "0a26c5b6", "kind": "Refines"},  # User must be authenticated
    "417b1306": {"parent": "0a26c5b6", "kind": "Refines"},  # login invariant

    # CLI command specs -> CLI requirements
    "e9c466e9": {"parent": "b706e529", "kind": "Refines"},  # spec add auto-infer -> CLI separation requirement

    # Extraction engine specs -> Reverse mapping requirements
    "b549f3a8": {"parent": "c6119c42", "kind": "Refines"},  # AI extraction intent
    "364af100": {"parent": "c6119c42", "kind": "Refines"},  # Test extraction creates U0+U3
    "49b943da": {"parent": "c6119c42", "kind": "Refines"},  # PHPTestExtractor

    # ORACLE definition -> Motivation/core concept
    "e9b11d11": {"parent": "c6119c42", "kind": "Refines"},  # ORACLE as single source of truth

    # Violation specs -> Validation requirements
    "e72d7fd3": {"parent": "e784e25b", "kind": "Refines"},  # Amount > 0 violation

    # Debug/test artifact - DELETE
    "f1ff674b": {"action": "delete"},  # Debug test node
}

def load_spec_graph():
    """Load the specification graph from directory storage."""
    nodes_dir = Path.home() / "Projects/spec-oracle/.spec/nodes"
    edges_file = Path.home() / "Projects/spec-oracle/.spec/edges.yaml"

    nodes = {}
    for node_file in nodes_dir.glob("*.yaml"):
        with open(node_file, 'r') as f:
            node = yaml.safe_load(f)
            nodes[node['id']] = node

    with open(edges_file, 'r') as f:
        edges_data = yaml.safe_load(f)
        edges = edges_data.get('edges', [])

    return nodes, edges

def save_edges(edges: List[Dict]):
    """Save edges to edges.yaml."""
    edges_file = Path.home() / "Projects/spec-oracle/.spec/edges.yaml"
    with open(edges_file, 'w') as f:
        yaml.dump({'edges': edges}, f, default_flow_style=False, sort_keys=False)

def delete_node(node_id: str):
    """Delete a node's YAML file."""
    node_file = Path.home() / f"Projects/spec-oracle/.spec/nodes/{node_id}.yaml"
    if node_file.exists():
        node_file.unlink()
        print(f"  ✓ Deleted {node_id}")

def connect_isolated_specs():
    """Connect isolated specifications to their parents."""
    nodes, edges = load_spec_graph()

    print(f"📊 Current state:")
    print(f"  Nodes: {len(nodes)}")
    print(f"  Edges: {len(edges)}")
    print()

    # Process each connection
    new_edges = 0
    deleted_nodes = 0

    for node_id, config in CONNECTIONS.items():
        short_id = node_id[:8]

        # Check if node exists
        full_id = None
        for nid in nodes.keys():
            if nid.startswith(node_id):
                full_id = nid
                break

        if not full_id:
            print(f"  ⚠️  Node {short_id} not found, skipping")
            continue

        # Handle delete action
        if config.get("action") == "delete":
            delete_node(full_id)
            deleted_nodes += 1
            continue

        # Find parent
        parent_id = config["parent"]
        parent_full_id = None
        for nid in nodes.keys():
            if nid.startswith(parent_id):
                parent_full_id = nid
                break

        if not parent_full_id:
            print(f"  ⚠️  Parent {parent_id} not found for {short_id}, skipping")
            continue

        # Check if edge already exists
        edge_exists = any(
            (e['source'] == parent_full_id and e['target'] == full_id) or
            (e['source'] == full_id and e['target'] == parent_full_id)
            for e in edges
        )

        if edge_exists:
            print(f"  ⏭️  Edge already exists: {short_id} <-> {parent_id[:8]}")
            continue

        # Create edge
        edge = {
            'source': parent_full_id,
            'target': full_id,
            'kind': config["kind"],
            'created_at': '2026-02-15T00:00:00Z',
            'metadata': {
                'auto_generated': 'true',
                'reason': 'Connecting isolated spec to parent'
            }
        }
        edges.append(edge)
        new_edges += 1

        node_content = nodes[full_id].get('content', '')[:50]
        parent_content = nodes[parent_full_id].get('content', '')[:50]
        print(f"  ✓ Connected: [{short_id}] {node_content}...")
        print(f"             -> [{parent_id[:8]}] {parent_content}...")
        print()

    # Save updated edges
    if new_edges > 0 or deleted_nodes > 0:
        save_edges(edges)
        print(f"✅ Results:")
        print(f"  New edges created: {new_edges}")
        print(f"  Nodes deleted: {deleted_nodes}")
        print(f"  Total edges: {len(edges)}")
    else:
        print("  No changes needed")

if __name__ == "__main__":
    connect_isolated_specs()
