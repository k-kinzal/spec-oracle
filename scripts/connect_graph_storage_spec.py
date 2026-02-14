#!/usr/bin/env python3
"""
Connect the "Graph-based specification storage" spec to SpecGraph implementation.
"""

import json
from pathlib import Path

def main():
    specs_path = Path('.spec/specs.json')

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Find the nodes
    readme_idx = None
    specgraph_idx = None

    for idx, node in enumerate(nodes):
        if node['id'].startswith('6f0a3ae5'):
            readme_idx = idx
        if node['id'].startswith('ca9f0b06'):
            specgraph_idx = idx

    if readme_idx is None or specgraph_idx is None:
        print("❌ Could not find nodes")
        return

    print(f"📋 Connecting:")
    print(f"   FROM: [{nodes[readme_idx]['id'][:8]}] {nodes[readme_idx]['content'][:60]}")
    print(f"   TO:   [{nodes[specgraph_idx]['id'][:8]}] {nodes[specgraph_idx]['content'][:60]}")
    print()

    # Create edge
    edge = [
        readme_idx,
        specgraph_idx,
        {
            "id": f"readme-graph-storage",
            "kind": "DerivesFrom",
            "metadata": {
                "confidence": "0.90",
                "reason": "README describes SpecGraph implementation"
            },
            "created_at": 1771090100
        }
    ]

    edges.append(edge)
    data['graph']['edges'] = edges

    # Save
    with open(specs_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"✅ Connected README spec to SpecGraph implementation")
    print(f"   Edge: DerivesFrom (confidence: 0.90)")

if __name__ == '__main__':
    main()
