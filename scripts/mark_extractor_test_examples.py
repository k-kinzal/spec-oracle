#!/usr/bin/env python3
"""
Mark specifications extracted from extractor test code as Definition (examples).

These are test examples used to verify extraction functionality,
not real requirements for the specORACLE system.
"""

import json
from pathlib import Path

def mark_test_examples(specs_path: Path) -> dict:
    """Mark extractor test examples as Definition kind."""

    with open(specs_path, 'r') as f:
        data = json.load(f)

    # Test example patterns
    test_example_patterns = [
        "user.is_authenticated()",
        "Amount must be greater than zero",
        "User must authenticate",
        "extract intent from test with ai",
        'Password must be >= 8 chars" (natural language)',
    ]

    stats = {
        'total_nodes': len(data['graph']['nodes']),
        'changed': 0,
        'changed_ids': []
    }

    for node in data['graph']['nodes']:
        content = node.get('content', '')

        # Check if this is a test example
        is_test_example = any(pattern in content for pattern in test_example_patterns)

        if is_test_example and node.get('kind') != 'Definition':
            old_kind = node.get('kind')
            node['kind'] = 'Definition'

            # Mark as test example in metadata
            if 'metadata' not in node:
                node['metadata'] = {}
            node['metadata']['is_example'] = 'true'
            node['metadata']['example_source'] = 'extractor test code'

            stats['changed'] += 1
            stats['changed_ids'].append({
                'id': node['id'][:8],
                'old_kind': old_kind,
                'content': content[:80],
                'source': node.get('metadata', {}).get('source_file', 'unknown')
            })

    return data, stats

def main():
    specs_path = Path('.spec/specs.json')

    if not specs_path.exists():
        print(f"❌ Specs file not found: {specs_path}")
        return

    print("🔍 Marking extractor test examples as Definition...")
    print()

    # Mark
    data, stats = mark_test_examples(specs_path)

    # Report
    print(f"📊 Results:")
    print(f"   Total nodes: {stats['total_nodes']}")
    print(f"   Changed: {stats['changed']}")
    print()

    if stats['changed'] > 0:
        print("✏️  Changed specifications:")
        for spec in stats['changed_ids']:
            print(f"   - [{spec['id']}] {spec['old_kind']} → Definition")
            print(f"     Source: {spec['source']}")
            print(f"     {spec['content']}")
            print()

        # Save
        with open(specs_path, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Saved changes to {specs_path}")
        print()
        print("📝 These specs are now marked as Definition (test examples)")
        print("   They will be excluded from contradiction detection.")
    else:
        print("✅ No changes needed")

if __name__ == '__main__':
    main()
