#!/usr/bin/env python3
"""
Remove specifications extracted from meta-documentation.

PROBLEM.md is meta-documentation (problem descriptions, historical notes)
and should not be extracted as specifications.
"""

import json
from pathlib import Path

def remove_meta_doc_specs(specs_path: Path) -> dict:
    """Remove specs from meta-documentation files."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Meta-documentation files to exclude
    meta_doc_files = ['PROBLEM.md', 'CHANGELOG.md']

    # Find node indices to remove
    nodes_to_remove = set()
    for idx, node in enumerate(nodes):
        source_file = node.get('metadata', {}).get('source_file', '')
        if source_file in meta_doc_files:
            nodes_to_remove.add(idx)

    stats = {
        'total_nodes_before': len(nodes),
        'nodes_removed': len(nodes_to_remove),
        'nodes_by_source': {}
    }

    # Count by source file
    for idx in nodes_to_remove:
        source = nodes[idx].get('metadata', {}).get('source_file', 'unknown')
        stats['nodes_by_source'][source] = stats['nodes_by_source'].get(source, 0) + 1

    # Create mapping from old indices to new indices
    old_to_new = {}
    new_idx = 0
    for old_idx in range(len(nodes)):
        if old_idx not in nodes_to_remove:
            old_to_new[old_idx] = new_idx
            new_idx += 1

    # Remove nodes
    new_nodes = [node for idx, node in enumerate(nodes) if idx not in nodes_to_remove]

    # Update edges
    new_edges = []
    edges_removed = 0
    for edge in edges:
        source_idx, target_idx, edge_data = edge
        # Only keep edges where both endpoints exist
        if source_idx in old_to_new and target_idx in old_to_new:
            new_edges.append([
                old_to_new[source_idx],
                old_to_new[target_idx],
                edge_data
            ])
        else:
            edges_removed += 1

    stats['edges_removed'] = edges_removed
    stats['total_nodes_after'] = len(new_nodes)
    stats['total_edges_after'] = len(new_edges)

    data['graph']['nodes'] = new_nodes
    data['graph']['edges'] = new_edges

    return data, stats

def main():
    specs_path = Path('.spec/specs.json')

    if not specs_path.exists():
        print(f"❌ Specs file not found: {specs_path}")
        return

    print("🔍 Removing meta-documentation specifications...")
    print()

    # Remove
    data, stats = remove_meta_doc_specs(specs_path)

    # Report
    print(f"📊 Results:")
    print(f"   Total nodes before: {stats['total_nodes_before']}")
    print(f"   Nodes removed: {stats['nodes_removed']}")
    print(f"   Total nodes after: {stats['total_nodes_after']}")
    print(f"   Edges removed: {stats['edges_removed']}")
    print(f"   Edges remaining: {stats['total_edges_after']}")
    print()

    if stats['nodes_by_source']:
        print("📁 Removed by source:")
        for source, count in stats['nodes_by_source'].items():
            print(f"   - {source}: {count} specs")
        print()

    # Save
    with open(specs_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"✅ Saved changes to {specs_path}")
    print()
    print("📝 Meta-documentation specs removed.")
    print("   PROBLEM.md describes problems to solve, not requirements to implement.")

if __name__ == '__main__':
    main()
