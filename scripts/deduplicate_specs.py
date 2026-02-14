#!/usr/bin/env python3
"""
Remove duplicate specifications, keeping only the oldest instance.
Duplicates are identified by identical content.
"""

import json
import sys
from collections import defaultdict
from datetime import datetime

def deduplicate_specs(specs_path: str, execute: bool = False):
    """Remove duplicate specs, keeping oldest instance."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Group nodes by content
    content_groups = defaultdict(list)
    for node in nodes:
        content_groups[node['content']].append(node)

    # Find duplicates
    duplicates_to_remove = []
    stats = {
        'total_groups': 0,
        'duplicate_groups': 0,
        'nodes_to_remove': 0
    }

    for content, group in content_groups.items():
        stats['total_groups'] += 1
        if len(group) > 1:
            stats['duplicate_groups'] += 1
            # Sort by created_at (oldest first)
            group.sort(key=lambda n: n.get('created_at', ''))
            # Keep first (oldest), remove rest
            to_remove = group[1:]
            duplicates_to_remove.extend([n['id'] for n in to_remove])
            stats['nodes_to_remove'] += len(to_remove)

            print(f"\n📦 Duplicate group ({len(group)} instances):")
            print(f"   Content: {content[:80]}...")
            print(f"   Keeping: {group[0]['id'][:8]} (created: {group[0].get('created_at', 'unknown')})")
            for dup in to_remove:
                print(f"   Removing: {dup['id'][:8]} (created: {dup.get('created_at', 'unknown')})")

    if not duplicates_to_remove:
        print("\n✅ No duplicates found!")
        return

    print(f"\n📊 Statistics:")
    print(f"   Total content groups: {stats['total_groups']}")
    print(f"   Duplicate groups: {stats['duplicate_groups']}")
    print(f"   Nodes to remove: {stats['nodes_to_remove']}")
    print(f"   Nodes to keep: {len(nodes) - stats['nodes_to_remove']}")

    if not execute:
        print(f"\n💡 Dry run mode. Use --execute to apply changes.")
        return

    # Remove duplicate nodes and build index mapping
    duplicate_ids = set(duplicates_to_remove)

    # Build mapping from old index to new index
    old_to_new_index = {}
    new_nodes = []
    new_index = 0
    for old_index, node in enumerate(nodes):
        if node['id'] not in duplicate_ids:
            old_to_new_index[old_index] = new_index
            new_nodes.append(node)
            new_index += 1

    data['graph']['nodes'] = new_nodes

    # Remove edges referencing deleted nodes and update indices
    edges_before = len(edges)
    new_edges = []
    for edge in edges:
        # Edge format: [source_index, target_index, metadata]
        source_idx, target_idx, metadata = edge

        # Skip if either endpoint was deleted
        if source_idx not in old_to_new_index or target_idx not in old_to_new_index:
            continue

        # Update to new indices
        new_source = old_to_new_index[source_idx]
        new_target = old_to_new_index[target_idx]
        new_edges.append([new_source, new_target, metadata])

    data['graph']['edges'] = new_edges
    edges_removed = edges_before - len(new_edges)

    # Write back
    with open(specs_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"\n✅ Cleanup complete!")
    print(f"   Nodes removed: {stats['nodes_to_remove']}")
    print(f"   Edges removed: {edges_removed}")
    print(f"   Final node count: {len(data['graph']['nodes'])}")
    print(f"   Final edge count: {len(data['graph']['edges'])}")

if __name__ == '__main__':
    specs_path = '.spec/specs.json'
    execute = '--execute' in sys.argv

    deduplicate_specs(specs_path, execute)
