#!/usr/bin/env python3
"""
Connect the isolated layer label specification (ab5e4dd1) with the find command implementation (8a79071d).

This resolves the last omission detected in the specifications.
"""

import json
import sys
from pathlib import Path
import time

def main():
    specs_path = Path.home() / "Projects/spec-oracle/.spec/specs.json"

    if not specs_path.exists():
        print(f"Error: {specs_path} not found")
        sys.exit(1)

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Find indices
    ab5e4dd1_idx = None
    eight_a_idx = None

    for i, node in enumerate(nodes):
        if node['id'].startswith('ab5e4dd1'):
            ab5e4dd1_idx = i
            print(f"Found ab5e4dd1 at index {i}: {node['content'][:80]}...")
        elif node['id'].startswith('8a79071d'):
            eight_a_idx = i
            print(f"Found 8a79071d at index {i}: {node['content'][:80]}...")

    if ab5e4dd1_idx is None or eight_a_idx is None:
        print("Error: Could not find both nodes")
        sys.exit(1)

    # Check if edge already exists
    edge_exists = False
    for edge in edges:
        if edge[0] == ab5e4dd1_idx and edge[1] == eight_a_idx:
            edge_exists = True
            print(f"Edge already exists: {ab5e4dd1_idx} -> {eight_a_idx}")
            break

    if not edge_exists:
        # Add Formalizes edge: U0 (ab5e4dd1) -> U3 (8a79071d)
        # Following the pattern: source=U0, target=U3
        new_edge = [
            ab5e4dd1_idx,
            eight_a_idx,
            {
                "id": f"edge-{ab5e4dd1_idx}-{eight_a_idx}-formalizes",
                "kind": "Formalizes",
                "metadata": {
                    "note": "Layer label display requirement (U0) formalized by find command implementation (U3)"
                },
                "created_at": int(time.time())
            }
        ]
        edges.append(new_edge)
        print(f"Added Formalizes edge: {ab5e4dd1_idx} (U0) -> {eight_a_idx} (U3)")

        # Save
        with open(specs_path, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Successfully updated {specs_path}")
        print(f"Total nodes: {len(nodes)}, Total edges: {len(edges)}")
    else:
        print("No changes needed")

if __name__ == '__main__':
    main()
