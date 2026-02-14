#!/usr/bin/env python3
"""
Connect the final 4 isolated specifications to achieve near-zero omissions.
"""

import json
import uuid
from pathlib import Path

SPECS_PATH = Path('.spec/specs.json')

def load_specs():
    with open(SPECS_PATH) as f:
        return json.load(f)

def save_specs(data):
    with open(SPECS_PATH, 'w') as f:
        json.dump(data, f, indent=2)

def find_node_by_id_prefix(nodes, id_prefix):
    """Find node by ID prefix."""
    for i, node in enumerate(nodes):
        if node['id'].startswith(id_prefix):
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
            "metadata": {"auto_connected": "true", "script": "connect_final_four.py"},
            "created_at": 1771086200
        }
    ]

def main():
    data = load_specs()
    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Find the 4 isolated specs by ID prefix
    connections = [
        # Extraction idempotency -> construct-u0 command
        ("ac78bcec", "8aff5987", "Refines"),

        # CLI coherent structure -> all high-priority features spec
        ("c6119c42", "fb2ff2ba", "Refines"),

        # CLI separation of concerns -> all high-priority features spec
        ("b706e529", "fb2ff2ba", "Refines"),

        # Proto RPC auto-connection -> all high-priority features spec
        ("04dd5a76", "fb2ff2ba", "Refines"),
    ]

    new_edges = []
    for src_prefix, tgt_prefix, kind in connections:
        src_idx, src_node = find_node_by_id_prefix(nodes, src_prefix)
        tgt_idx, tgt_node = find_node_by_id_prefix(nodes, tgt_prefix)

        if src_node and tgt_node:
            edge = create_edge(src_idx, tgt_idx, kind)
            new_edges.append(edge)
            print(f"[{src_prefix}] {src_node['content'][:50]}...")
            print(f"  → {kind} [{tgt_prefix}] {tgt_node['content'][:50]}...\n")
        else:
            print(f"⚠️  Failed to find: src={src_prefix} tgt={tgt_prefix}")

    # Add new edges
    if new_edges:
        edges.extend(new_edges)
        data['graph']['edges'] = edges
        save_specs(data)
        print(f"✅ Added {len(new_edges)} edges")
        print(f"Total edges: {len(edges)}")
    else:
        print(f"⚠️ No new edges added")

if __name__ == '__main__':
    main()
