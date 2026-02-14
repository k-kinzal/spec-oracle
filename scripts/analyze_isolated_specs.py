#!/usr/bin/env python3
"""
Analyze isolated specifications to understand what needs to be connected.
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

    # Find isolated nodes
    isolated_by_source = defaultdict(list)
    isolated_by_extractor = defaultdict(int)

    for idx, node in enumerate(nodes):
        if idx not in nodes_with_edges:
            source_file = node.get('metadata', {}).get('source_file', 'manual')
            extractor = node.get('metadata', {}).get('extractor', 'manual')

            isolated_by_source[source_file].append({
                'id': node['id'][:8],
                'kind': node['kind'],
                'content': node['content'][:80]
            })

            if node.get('metadata', {}).get('inferred') == 'true':
                isolated_by_extractor[extractor] += 1

    # Report
    print(f"📊 Isolated Specification Analysis")
    print(f"=" * 60)
    print()

    print(f"Total isolated: {sum(len(v) for v in isolated_by_source.values())}")
    print()

    print("By source file:")
    for source, specs in sorted(isolated_by_source.items(), key=lambda x: len(x[1]), reverse=True):
        print(f"  {source}: {len(specs)} specs")
        for spec in specs[:3]:
            print(f"    - [{spec['id']}] {spec['kind']}: {spec['content']}")
        if len(specs) > 3:
            print(f"    ... and {len(specs) - 3} more")
        print()

    print("By extractor:")
    for extractor, count in sorted(isolated_by_extractor.items(), key=lambda x: x[1], reverse=True):
        print(f"  {extractor}: {count} specs")

if __name__ == '__main__':
    main()
