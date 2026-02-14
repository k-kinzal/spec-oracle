#!/usr/bin/env python3
"""
Connect isolated README.md specifications to the implementation graph.

README.md specs describe features that should be connected to:
- Implementation specs (code)
- Test specs
- Proto specs (RPC definitions)
"""

import json
from pathlib import Path

def connect_readme_specs(specs_path: Path) -> dict:
    """Connect README specs to implementation."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Build index
    node_by_id = {node['id']: (idx, node) for idx, node in enumerate(nodes)}

    # Find README specs
    readme_specs = []
    for idx, node in enumerate(nodes):
        source = node.get('metadata', {}).get('source_file', '')
        if source == 'README.md' and node.get('metadata', {}).get('inferred') == 'true':
            readme_specs.append((idx, node))

    # Find parent specs to connect to
    connection_patterns = [
        # Feature descriptions → Implementation specs
        ("Graph-based specification storage", ["Graph", "specification", "storage", "node"]),
        ("CLI automatically detects", ["CLI", "standalone", "detect", ".spec"]),
        ("Breakthrough feature", ["specification", "synchronized", "code"]),
        ("constraint: Universal invariant", ["constraint", "universal", "invariant"]),
        ("scenario: Existential requirement", ["scenario", "existential", "requirement"]),
    ]

    stats = {
        'readme_specs': len(readme_specs),
        'connections_made': 0,
        'connections': []
    }

    # For each README spec, find matching implementation spec
    for readme_idx, readme_node in readme_specs:
        content = readme_node.get('content', '').lower()

        # Skip command examples (already marked as Definition)
        if readme_node.get('kind') == 'Definition':
            continue

        # Find best matching parent
        best_match = None
        best_score = 0

        for target_idx, target_node in enumerate(nodes):
            # Skip self, skip other README specs, skip Definition kind
            if target_idx == readme_idx:
                continue
            if target_node.get('metadata', {}).get('source_file') == 'README.md':
                continue
            if target_node.get('kind') == 'Definition':
                continue

            target_content = target_node.get('content', '').lower()

            # Calculate keyword overlap
            readme_words = set(content.split())
            target_words = set(target_content.split())
            overlap = len(readme_words & target_words)

            if overlap > best_score:
                best_score = overlap
                best_match = target_idx

        # If we found a match, create edge
        if best_match is not None and best_score >= 2:  # At least 2 common words
            # Check if edge already exists
            edge_exists = any(
                (e[0] == readme_idx and e[1] == best_match) or
                (e[0] == best_match and e[1] == readme_idx)
                for e in edges
            )

            if not edge_exists:
                # Create DerivesFrom edge (README describes existing feature)
                edge = [
                    readme_idx,
                    best_match,
                    {
                        "id": f"readme-{readme_idx}-{best_match}",
                        "kind": "DerivesFrom",
                        "metadata": {
                            "confidence": str(min(0.95, 0.6 + (best_score * 0.05))),
                            "reason": "README documentation of existing feature"
                        },
                        "created_at": 1771090000
                    }
                ]
                edges.append(edge)

                stats['connections_made'] += 1
                stats['connections'].append({
                    'from': readme_node['id'][:8],
                    'from_content': readme_node['content'][:60],
                    'to': nodes[best_match]['id'][:8],
                    'to_content': nodes[best_match]['content'][:60],
                    'score': best_score
                })

    data['graph']['edges'] = edges

    return data, stats

def main():
    specs_path = Path('.spec/specs.json')

    if not specs_path.exists():
        print(f"❌ Specs file not found: {specs_path}")
        return

    print("🔍 Connecting README.md specifications to implementation...")
    print()

    # Connect
    data, stats = connect_readme_specs(specs_path)

    # Report
    print(f"📊 Results:")
    print(f"   README specs: {stats['readme_specs']}")
    print(f"   Connections made: {stats['connections_made']}")
    print()

    if stats['connections_made'] > 0:
        print("🔗 Connections created:")
        for conn in stats['connections']:
            print(f"   [{conn['from']}] {conn['from_content']}")
            print(f"   → DerivesFrom [{conn['to']}] {conn['to_content']}")
            print(f"      (score: {conn['score']})")
            print()

        # Save
        with open(specs_path, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Saved changes to {specs_path}")
        print()
        print("📝 README documentation specs are now connected to implementation.")
    else:
        print("✅ No connections needed (all specs already connected or marked as examples)")

if __name__ == '__main__':
    main()
