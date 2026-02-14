#!/usr/bin/env python3
"""
Clean up example password specifications extracted from PROBLEM.md.

These are examples used to illustrate problems, not real requirements.
They should be marked as Definition (examples/meta-docs), not Constraint.
"""

import json
import sys
from pathlib import Path

def cleanup_example_specs(specs_path: Path) -> dict:
    """Mark example password specs as Definition kind."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    # Example password specs to mark as Definition
    example_patterns = [
        # Example constraints from PROBLEM.md
        "A: [a1087af9] Password must be at least 12 characters",
        "B: [334ebd1d] Password must be at most 10 characters",

        # Embedded specs in documentation
        '"Password must be at least 8 characters"',
        '"Password must be minimum 10 characters"',
        '"Password must be at least 8 characters long"',

        # Command examples
        'spec add "Password must be at least 8 characters"',
        'cargo run --bin spec -- add-node "Passwords must be >= 8 chars"',
        'spec add-node "Passwords must contain alphanumeric characters"',

        # Code examples
        '/// Password must be at least 8 characters',
        '"Password must be >= 8 chars" (natural language)',

        # Meta-documentation about PROBLEM.md examples
        'spec detect-omissions',  # Japanese text about password examples
        '+        "content": "Password must be at least 8 characters"',
        '対応パターン: password length',  # About Z3 patterns
    ]

    stats = {
        'total_nodes': len(data['graph']['nodes']),
        'changed': 0,
        'changed_ids': []
    }

    for node in data['graph']['nodes']:
        content = node.get('content', '')

        # Check if this is an example spec
        is_example = any(pattern in content for pattern in example_patterns)

        if is_example and node.get('kind') != 'Definition':
            old_kind = node.get('kind')
            node['kind'] = 'Definition'

            # Mark as example in metadata
            if 'metadata' not in node:
                node['metadata'] = {}
            node['metadata']['is_example'] = 'true'
            node['metadata']['example_source'] = 'PROBLEM.md documentation'

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
        sys.exit(1)

    print("🔍 Cleaning up example password specifications...")
    print()

    # Cleanup
    data, stats = cleanup_example_specs(specs_path)

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
        print()
        print("📝 These specs are now marked as Definition (examples/meta-documentation)")
        print("   They will be excluded from contradiction detection.")
    else:
        print("✅ No changes needed - all specs already correctly classified")

if __name__ == '__main__':
    main()
