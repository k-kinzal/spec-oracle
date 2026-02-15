#!/usr/bin/env python3
"""Analyze isolated specifications to determine their nature."""

import yaml
import subprocess
from pathlib import Path
from collections import defaultdict

def get_isolated_spec_ids():
    """Get list of isolated spec IDs from detect-omissions."""
    result = subprocess.run(
        ["./target/release/spec", "detect-omissions"],
        capture_output=True,
        text=True,
        cwd=Path.home() / "Projects/spec-oracle"
    )

    # Extract short IDs from output like "- [33912c9c] Scenario: ..."
    ids = []
    for line in result.stdout.split('\n') + result.stderr.split('\n'):
        if '[' in line and ']' in line:
            start = line.find('[') + 1
            end = line.find(']')
            short_id = line[start:end]
            if len(short_id) == 8:
                ids.append(short_id)

    return list(set(ids))

def analyze_isolated_specs():
    """Analyze isolated specifications."""
    nodes_dir = Path.home() / "Projects/spec-oracle/.spec/nodes"
    isolated_ids = get_isolated_spec_ids()

    print(f"📊 Found {len(isolated_ids)} isolated specifications\n")

    # Categorize by kind and metadata
    by_kind = defaultdict(list)
    test_data = []
    real_specs = []

    for short_id in isolated_ids:
        # Find full file
        matching_files = list(nodes_dir.glob(f"{short_id}*.yaml"))
        if not matching_files:
            print(f"  ⚠️  File not found for {short_id}")
            continue

        with open(matching_files[0], 'r') as f:
            spec = yaml.safe_load(f)

        kind = spec.get('kind', 'Unknown')
        is_example = spec.get('metadata', {}).get('is_example') == 'true'
        is_test_data = spec.get('metadata', {}).get('example_purpose') == 'test_data'
        content = spec.get('content', '')[:80]

        by_kind[kind].append(short_id)

        if is_example or is_test_data:
            test_data.append((short_id, kind, content))
        else:
            real_specs.append((short_id, kind, content))

    # Print results
    print("📋 By Kind:")
    for kind, specs in sorted(by_kind.items()):
        print(f"  {kind}: {len(specs)} specs")
    print()

    print(f"🧪 Test Data / Examples: {len(test_data)}")
    for short_id, kind, content in test_data:
        print(f"  [{short_id}] {kind}: {content}...")
    print()

    print(f"📝 Real Specifications: {len(real_specs)}")
    for short_id, kind, content in real_specs:
        print(f"  [{short_id}] {kind}: {content}...")
    print()

    return test_data, real_specs

if __name__ == "__main__":
    test_data, real_specs = analyze_isolated_specs()

    print("\n💡 Recommendation:")
    if test_data:
        print(f"  - {len(test_data)} test data specs are correctly isolated (Definition kind)")
        print("  - These should remain isolated as they are examples, not requirements")

    if real_specs:
        print(f"  - {len(real_specs)} real specs need connections")
        print("  - These should be connected to appropriate parent specifications")
