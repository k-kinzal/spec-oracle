#!/usr/bin/env python3
"""
Clean up malformed invariant specs that contain Rust code artifacts.

These are low-quality extraction results that slipped through the quality filter.
Examples:
- "Invariant: fetched.content, "User must authenticate""
- "Invariant: user.is_authenticated())".into(), NodeKind::Assertion, HashMap::new()).id.clone("
"""

import json
import sys

def is_malformed_invariant(node):
    """Check if a node is a malformed invariant containing Rust artifacts."""
    if node['kind'] != 'Constraint':
        return False

    content = node['content']
    if not content.startswith('Invariant: '):
        return False

    # Check for Rust syntax artifacts
    rust_artifacts = [
        'fetched.',
        '.into()',
        'NodeKind::',
        'HashMap::new()',
        '.clone(',
        '".into()',
        ').id.',
        'HashMap::from',
    ]

    return any(marker in content for marker in rust_artifacts)

def main():
    specs_file = '.spec/specs.json'

    with open(specs_file) as f:
        data = json.load(f)

    original_count = len(data['graph']['nodes'])

    # Find malformed nodes
    malformed = []
    clean_nodes = []

    for idx, node in enumerate(data['graph']['nodes']):
        if is_malformed_invariant(node):
            malformed.append((idx, node))
        else:
            clean_nodes.append(node)

    if not malformed:
        print("✓ No malformed invariants found")
        return 0

    print(f"Found {len(malformed)} malformed invariant(s):\n")
    for idx, node in malformed:
        print(f"  [{idx}] {node['id'][:8]}: {node['content'][:80]}")

    # Remove edges referencing deleted nodes
    malformed_indices = {idx for idx, _ in malformed}
    clean_edges = []
    removed_edges = 0

    for edge in data['graph']['edges']:
        src_idx, tgt_idx, metadata = edge
        if src_idx in malformed_indices or tgt_idx in malformed_indices:
            removed_edges += 1
        else:
            # Reindex edges after node removal
            new_src = src_idx - sum(1 for m_idx in malformed_indices if m_idx < src_idx)
            new_tgt = tgt_idx - sum(1 for m_idx in malformed_indices if m_idx < tgt_idx)
            clean_edges.append([new_src, new_tgt, metadata])

    # Update graph
    data['graph']['nodes'] = clean_nodes
    data['graph']['edges'] = clean_edges

    # Save
    with open(specs_file, 'w') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

    print(f"\n✅ Cleanup complete:")
    print(f"   Nodes removed: {len(malformed)}")
    print(f"   Edges removed: {removed_edges}")
    print(f"   Total nodes: {original_count} → {len(clean_nodes)}")

    return 0

if __name__ == '__main__':
    sys.exit(main())
