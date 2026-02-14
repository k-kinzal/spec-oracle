#!/usr/bin/env python3
"""
Connect isolated proto_rpc specifications to related U0 specifications.

This script addresses the timing issue where proto_rpc specs were extracted
before related U0 specs were added, resulting in missing connections.

Based on Session 66-68 precedent for manual connection scripts.
"""

import json
import uuid
from datetime import datetime

SPECS_FILE = ".spec/specs.json"

# Manual connections based on semantic analysis
# Format: (proto_rpc_content_substring, u0_content_substring, edge_kind)
CONNECTIONS = [
    # Relationship inference
    ("AI-powered relationship inference", "Cross-layer edge inference", "DerivesFrom"),
    ("Automatic relationship inference", "Cross-layer edge inference", "DerivesFrom"),

    # Compliance and verification
    ("compliance", "verify-layers command checks multi-layer", "DerivesFrom"),
    ("compliance", "verify-layers command provides formal verification", "DerivesFrom"),

    # Layer operations
    ("Layer-aware operations", "specORACLE manages multi-layered specifications", "DerivesFrom"),
    ("Layer-aware operations", "Specifications at different formality layers", "DerivesFrom"),

    # Universe and domain
    ("Set node universe", "Universe struct represents the space", "DerivesFrom"),
    ("Inter-universe consistency", "UDAFModel.construct_u0()", "DerivesFrom"),

    # Temporal queries
    ("Temporal queries", "Query", "Refines"),
    ("node history", "Query", "Refines"),

    # Contract generation
    ("Executable contracts", "AdmissibleSet struct symbolically represents", "DerivesFrom"),

    # Synonym detection
    ("synonym", "AI-powered", "DerivesFrom"),
    ("related terms", "semantic", "DerivesFrom"),

    # Formalization
    ("Find formalizations", "Formalizes edge", "DerivesFrom"),
    ("Find formalizations", "Multi-layer specification tracking", "DerivesFrom"),
]

def load_specs():
    with open(SPECS_FILE, 'r') as f:
        return json.load(f)

def save_specs(data):
    with open(SPECS_FILE, 'w') as f:
        json.dump(data, f, indent=2)

def find_node_by_content(nodes, substring, layer=None):
    """Find node by content substring, optionally filtered by layer."""
    matches = []
    for i, node in enumerate(nodes):
        if substring.lower() in node['content'].lower():
            if layer is None or node.get('formality_layer') == layer:
                matches.append((i, node))
    return matches

def edge_exists(edges, src_idx, tgt_idx):
    """Check if edge already exists between two nodes."""
    for edge in edges:
        if edge[0] == src_idx and edge[1] == tgt_idx:
            return True
        if edge[0] == tgt_idx and edge[1] == src_idx:
            return True
    return False

def main():
    print("Loading specifications...")
    data = load_specs()
    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Find isolated proto_rpc nodes
    proto_rpc_indices = {i for i, node in enumerate(nodes)
                         if node.get('metadata', {}).get('extractor') == 'proto_rpc'}

    # Find which are isolated
    edge_connected = set()
    for edge in edges:
        src_idx, tgt_idx = edge[0], edge[1]
        if src_idx in proto_rpc_indices:
            edge_connected.add(src_idx)
        if tgt_idx in proto_rpc_indices:
            edge_connected.add(tgt_idx)

    isolated_proto_rpc = proto_rpc_indices - edge_connected

    print(f"Found {len(isolated_proto_rpc)} isolated proto_rpc specifications")
    print(f"Attempting {len(CONNECTIONS)} manual connections...\n")

    edges_created = 0
    connections_attempted = 0

    for proto_substr, u0_substr, edge_kind in CONNECTIONS:
        connections_attempted += 1

        # Find proto_rpc node (U2 layer)
        proto_matches = find_node_by_content(nodes, proto_substr, layer=2)
        if not proto_matches:
            print(f"⚠️  No proto_rpc node found for: {proto_substr}")
            continue

        # Find U0 node
        u0_matches = find_node_by_content(nodes, u0_substr, layer=0)
        if not u0_matches:
            print(f"⚠️  No U0 node found for: {u0_substr}")
            continue

        # Create edges
        for proto_idx, proto_node in proto_matches:
            if proto_idx not in isolated_proto_rpc:
                continue  # Skip if already connected

            for u0_idx, u0_node in u0_matches:
                if edge_exists(edges, u0_idx, proto_idx):
                    continue  # Skip if edge already exists

                # Create edge: U2 → U0 (DerivesFrom)
                edge = [
                    proto_idx,  # source: U2 proto_rpc spec
                    u0_idx,     # target: U0 requirement spec
                    {
                        "id": str(uuid.uuid4()),
                        "kind": edge_kind,
                        "metadata": {
                            "created_by": "connect_isolated_proto_rpc.py",
                            "reason": f"Connect proto_rpc '{proto_substr}' to U0 '{u0_substr}'"
                        },
                        "created_at": int(datetime.now().timestamp())
                    }
                ]
                edges.append(edge)
                edges_created += 1

                print(f"✅ Connected: [{proto_idx}] {proto_node['content'][:50]}...")
                print(f"          → [{u0_idx}] {u0_node['content'][:50]}...")
                print(f"          Edge: {edge_kind}\n")

    # Save updated graph
    print(f"\nSummary:")
    print(f"  Connections attempted: {connections_attempted}")
    print(f"  Edges created: {edges_created}")

    if edges_created > 0:
        save_specs(data)
        print(f"\n✅ Saved {edges_created} new edges to {SPECS_FILE}")
    else:
        print("\n⚠️  No new edges created")

if __name__ == '__main__':
    main()
