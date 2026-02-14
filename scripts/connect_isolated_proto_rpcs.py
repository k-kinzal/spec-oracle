#!/usr/bin/env python3
"""
Connect isolated proto RPC specifications to U0 requirements and U3 implementations.
This realizes the reverse mapping engine's promise: f₀₂⁻¹(U2) → U0 connections.
"""

import json
import uuid
from pathlib import Path

SPECS_PATH = Path('.spec/specs.json')

# Mapping of isolated proto RPCs to their conceptual U0 requirements
RPC_TO_U0_MAPPINGS = {
    "RPC: Diff timestamps": "temporal queries",
    "RPC: Remove edge": "edge operations",
    "RPC: List edges": "edge operations",
    "Edge operations": "edge operations",  # category spec
    "RPC: Remove node": "node operations",
    "RPC: List nodes": "node operations",
    "RPC: Get node": "node operations",
    "Node operations": "node operations",  # category spec
}

def load_specs():
    with open(SPECS_PATH) as f:
        return json.load(f)

def save_specs(data):
    with open(SPECS_PATH, 'w') as f:
        json.dump(data, f, indent=2)

def find_node_by_content(nodes, content_pattern):
    """Find node by partial content match (case-insensitive)."""
    pattern = content_pattern.lower()
    for i, node in enumerate(nodes):
        if pattern in node['content'].lower():
            return i, node
    return None, None

def create_edge(source_idx, target_idx, kind="Formalizes"):
    """Create a new edge."""
    return [
        source_idx,
        target_idx,
        {
            "id": str(uuid.uuid4()),
            "kind": kind,
            "metadata": {"auto_connected": "true", "script": "connect_isolated_proto_rpcs.py"},
            "created_at": 1771086000  # approximately current time
        }
    ]

def main():
    data = load_specs()
    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Build edge index to check what's already connected
    node_edges = {}
    for edge in edges:
        src_idx, tgt_idx, _ = edge
        if src_idx not in node_edges:
            node_edges[src_idx] = []
        if tgt_idx not in node_edges:
            node_edges[tgt_idx] = []
        node_edges[src_idx].append(edge)
        node_edges[tgt_idx].append(edge)

    # Find isolated proto RPCs
    proto_rpcs = [(i, n) for i, n in enumerate(nodes)
                  if n.get('metadata', {}).get('extractor') == 'proto_rpc']
    isolated_rpcs = [(i, n) for i, n in proto_rpcs if i not in node_edges]

    print(f"Found {len(isolated_rpcs)} isolated proto RPC specs")

    new_edges = []
    for idx, node in isolated_rpcs:
        content = node['content']
        print(f"\n[{node['id'][:8]}] {content}")

        # Find corresponding U0 requirement
        if content in RPC_TO_U0_MAPPINGS:
            search_pattern = RPC_TO_U0_MAPPINGS[content]
            u0_idx, u0_node = find_node_by_content(nodes, search_pattern)

            if u0_node and u0_node['formality_layer'] == 2:
                # Found U2 category spec - connect U2 RPC to U2 category
                edge = create_edge(u0_idx, idx, "Refines")
                new_edges.append(edge)
                print(f"  → Refines [U2] {u0_node['content'][:60]}")
            elif u0_node:
                print(f"  ⚠ Found but not U2: {u0_node['content'][:60]} (layer {u0_node['formality_layer']})")
        else:
            print(f"  ⚠ No mapping defined")

    # Add new edges
    if new_edges:
        edges.extend(new_edges)
        data['graph']['edges'] = edges
        save_specs(data)
        print(f"\n✅ Added {len(new_edges)} edges")
        print(f"Total edges: {len(edges)}")
    else:
        print(f"\n⚠️ No new edges added")

if __name__ == '__main__':
    main()
