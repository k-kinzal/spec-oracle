#!/usr/bin/env python3
"""
Remove self-referencing edges from the specification graph.

Self-referencing edges (where source == target) are semantically invalid
and should be removed.
"""

import yaml
import sys

def main():
    edges_file = '.spec/edges.yaml'

    # Load edges
    with open(edges_file, 'r') as f:
        edges = yaml.safe_load(f)

    initial_count = len(edges)

    # Find self-referencing edges
    self_refs = [e for e in edges if e['source'] == e['target']]

    print(f'Total edges: {initial_count}')
    print(f'Self-referencing edges to remove: {len(self_refs)}')
    print()

    # Display what will be removed
    for edge in self_refs:
        print(f"  Removing: {edge['source'][:8]} --[{edge['kind']}]--> {edge['target'][:8]}")

    # Remove self-referencing edges
    cleaned_edges = [e for e in edges if e['source'] != e['target']]

    print()
    print(f'Edges after cleanup: {len(cleaned_edges)}')
    print(f'Removed: {len(edges) - len(cleaned_edges)} edges')

    # Save cleaned edges
    with open(edges_file, 'w') as f:
        yaml.dump(cleaned_edges, f, default_flow_style=False, sort_keys=False)

    print()
    print('✅ Self-referencing edges removed successfully!')

if __name__ == '__main__':
    main()
