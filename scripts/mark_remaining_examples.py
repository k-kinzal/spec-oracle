#!/usr/bin/env python3
"""
Mark remaining command examples and explanations as Definition.
"""

import json
from pathlib import Path

def mark_examples(specs_path: Path) -> dict:
    """Mark command examples and explanations as Definition."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    # Patterns for command examples and explanations
    example_patterns = [
        "cargo run --bin spec -- add-edge",  # Command example
        "constraint: Universal invariant",    # Explanation
        "scenario: Existential requirement",  # Explanation
    ]

    stats = {
        'total_nodes': len(data['graph']['nodes']),
        'changed': 0,
        'changed_ids': []
    }

    for node in data['graph']['nodes']:
        content = node.get('content', '')

        # Check if this is an example/explanation
        is_example = any(pattern in content for pattern in example_patterns)

        if is_example and node.get('kind') != 'Definition':
            old_kind = node.get('kind')
            node['kind'] = 'Definition'

            # Mark as example in metadata
            if 'metadata' not in node:
                node['metadata'] = {}
            node['metadata']['is_example'] = 'true'
            node['metadata']['example_source'] = 'command example or explanation'

            stats['changed'] += 1
            stats['changed_ids'].append({
                'id': node['id'][:8],
                'old_kind': old_kind,
                'content': content[:80]
            })

    return data, stats

def main():
    specs_path = Path('.spec/specs.json')

    if not specs_path.exists():
        print(f"❌ Specs file not found: {specs_path}")
        return

    print("🔍 Marking remaining examples as Definition...")
    print()

    # Mark
    data, stats = mark_examples(specs_path)

    # Report
    print(f"📊 Results:")
    print(f"   Total nodes: {stats['total_nodes']}")
    print(f"   Changed: {stats['changed']}")
    print()

    if stats['changed'] > 0:
        print("✏️  Changed specifications:")
        for spec in stats['changed_ids']:
            print(f"   - [{spec['id']}] {spec['old_kind']} → Definition")
            print(f"     {spec['content']}")
            print()

        # Save
        with open(specs_path, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Saved changes to {specs_path}")
    else:
        print("✅ No changes needed")

if __name__ == '__main__':
    main()
