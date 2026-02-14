#!/usr/bin/env python3
"""
Mark password and authentication test examples to avoid false contradictions.
Session 105: Clean up test data that's being detected as real specifications.
"""

import json

def main():
    with open('.spec/specs.json') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']

    # Find test example nodes (password/authentication examples from extracted code)
    test_example_keywords = [
        'password must be >= 8',
        'user must authenticate',
        'user.is_authenticated()',
        'validate_password',
        'login(user,',
        'amount must be greater than zero',
    ]

    updated_count = 0

    for idx, node in enumerate(nodes):
        content = node.get('content', '').lower()

        # Skip the meta-specification about Z3 testing
        if 'session 103 verified' in content:
            continue

        # Check if this is a test example
        is_test_example = any(keyword in content for keyword in test_example_keywords)

        if is_test_example and node.get('kind') in ['Constraint', 'Scenario', 'Assertion']:
            # Mark as example
            if 'metadata' not in node:
                node['metadata'] = {}

            node['metadata']['is_example'] = 'true'
            node['metadata']['example_purpose'] = 'test_data'

            # Change kind to Definition (test definition)
            if node.get('kind') != 'Definition':
                print(f"Marking [{node['id'][:8]}] as test example:")
                print(f"  Content: {node.get('content', '')[:100]}")
                print(f"  Old kind: {node.get('kind')}")
                node['kind'] = 'Definition'
                print(f"  New kind: Definition")
                print()
                updated_count += 1

    with open('.spec/specs.json', 'w') as f:
        json.dump(data, f, indent=2)

    print(f"\n✅ Marked {updated_count} test examples as Definitions")
    print("These will no longer be checked for contradictions with real specifications.")

if __name__ == '__main__':
    main()
