#!/usr/bin/env python3
"""
Count isolated specifications by kind.
"""

import json
from pathlib import Path
from collections import defaultdict

def main():
    specs_path = Path('.spec/specs.json')

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Find nodes with edges
    nodes_with_edges = set()
    for edge in edges:
        source_idx, target_idx, _ = edge
        nodes_with_edges.add(source_idx)
        nodes_with_edges.add(target_idx)

    # Count isolated by kind
    isolated_by_kind = defaultdict(int)
    isolated_non_def = []

    for idx, node in enumerate(nodes):
        if idx not in nodes_with_edges:
            kind = node['kind']
            isolated_by_kind[kind] += 1

            if kind != 'Definition':
                isolated_non_def.append({
                    'id': node['id'][:8],
                    'kind': kind,
                    'source': node.get('metadata', {}).get('source_file', 'manual'),
                    'content': node['content'][:80]
                })

    print("📊 Isolated Specifications by Kind")
    print("=" * 60)
    print()

    total = sum(isolated_by_kind.values())
    print(f"Total isolated: {total}")
    print()

    print("By kind:")
    for kind, count in sorted(isolated_by_kind.items(), key=lambda x: x[1], reverse=True):
        print(f"  {kind}: {count}")

    print()
    print(f"Non-Definition isolated: {len(isolated_non_def)}")

    if isolated_non_def:
        print()
        print("Non-Definition isolated specs (these need connections):")
        for spec in isolated_non_def:
            print(f"  [{spec['id']}] {spec['kind']} - {spec['source']}")
            print(f"    {spec['content']}")

if __name__ == '__main__':
    main()
