#!/usr/bin/env python3
"""
Connect isolated test specifications to their corresponding implementation specs.

This realizes specORACLE's essence as a reverse mapping engine by connecting
extracted U3 test specs to U3 implementation specs via Validates edges.
"""

import json
import uuid
from datetime import datetime

# Load specifications
with open('.spec/specs.json', 'r') as f:
    data = json.load(f)

nodes = data['graph']['nodes']
edges = data['graph']['edges']

# Build index: id_prefix -> full_node_index
node_index = {}
for idx, node in enumerate(nodes):
    prefix = node['id'][:8]
    node_index[prefix] = idx

# Helper function to add edge if not exists
def add_edge(source_prefix, target_prefix, kind, description):
    source_idx = node_index.get(source_prefix)
    target_idx = node_index.get(target_prefix)

    if source_idx is None or target_idx is None:
        print(f"⚠️  Skip: {source_prefix} -> {target_prefix} (node not found)")
        return False

    # Check if edge already exists
    for edge in edges:
        if edge[0] == source_idx and edge[1] == target_idx and edge[2]['kind'] == kind:
            print(f"✓ Skip: {source_prefix} -> {target_prefix} (already exists)")
            return False

    # Create edge
    edge_data = {
        "id": str(uuid.uuid4()),
        "kind": kind,
        "metadata": {"auto_connected": "true", "session": "96"},
        "created_at": int(datetime.now().timestamp())
    }
    edges.append([source_idx, target_idx, edge_data])

    source_content = nodes[source_idx]['content'][:60]
    target_content = nodes[target_idx]['content'][:60]
    print(f"✅ Connected: {source_prefix} -> {target_prefix}")
    print(f"   {source_content}")
    print(f"   {target_content}")
    print(f"   ({description})")
    return True

# Connection mappings
# Test specs (extracted) -> Implementation specs (extracted from code docs)

# Contradiction detection tests -> detect_contradictions function (386b1821)
detect_contradictions_impl = "386b1821"  # "The detect_contradictions function must check..."

contradiction_tests = [
    ("50acf4b7", "Test verifies contradiction count"),
    ("59ec9c22", "Test verifies explicit contradiction detection"),
    ("0ab6853c", "Test verifies duplicate specification detection"),
    ("cb2d1127", "Test verifies password length contradiction detection"),
    ("9db60408", "Test verifies no false positive duplicates"),
    ("e901ead6", "Scenario: detect explicit contradiction"),
    ("b6face50", "Scenario: detect semantic contradiction password length"),
]

# Omission detection tests -> detect_omissions function (194a46a7)
detect_omissions_impl = "194a46a7"  # "The detect_omissions function must identify..."

omission_tests = [
    ("5c533720", "Test verifies isolated node detection"),
    ("edf08e9b", "Test verifies domain without refinements detection"),
    ("7ead5420", "Test verifies scenario without assertions detection"),
    ("0d5c15ec", "Scenario: detect omission isolated node"),
    ("ca5d9013", "Scenario: detect omission domain without refinements"),
    ("c54e4333", "Scenario: detect omission scenario without assertions"),
]

# Coverage test specs -> Coverage calculation (need to find coverage spec)
# First, find coverage-related implementation spec
coverage_impl = None
for idx, node in enumerate(nodes):
    if node.get('metadata', {}).get('inferred') == 'true' and 'coverage' in node['content'].lower() and 'function' in node['content'].lower():
        coverage_impl = node['id'][:8]
        break

coverage_tests = [
    ("104537a8", "Scenario: coverage empty graph"),
    ("9a5e5a82", "Scenario: coverage no tests"),
    ("64d6cf39", "Scenario: coverage with tests"),
    ("862a1562", "Scenario: coverage ignores non testable nodes"),
]

# Apply connections
# Use "Refines" edge kind (test specs refine implementation specs by verifying them)
print("=" * 80)
print("CONNECTING CONTRADICTION TEST SPECS")
print("=" * 80)
created_count = 0
for test_id, description in contradiction_tests:
    if add_edge(test_id, detect_contradictions_impl, "Refines", description):
        created_count += 1

print("\n" + "=" * 80)
print("CONNECTING OMISSION TEST SPECS")
print("=" * 80)
for test_id, description in omission_tests:
    if add_edge(test_id, detect_omissions_impl, "Refines", description):
        created_count += 1

if coverage_impl:
    print("\n" + "=" * 80)
    print("CONNECTING COVERAGE TEST SPECS")
    print("=" * 80)
    for test_id, description in coverage_tests:
        if add_edge(test_id, coverage_impl, "Refines", description):
            created_count += 1
else:
    print("\n⚠️  Coverage implementation spec not found, skipping coverage tests")

# Save updated specifications
with open('.spec/specs.json', 'w') as f:
    json.dump(data, f, indent=2)

print("\n" + "=" * 80)
print(f"✅ COMPLETE: Created {created_count} new edges")
print(f"📊 Total edges: {len(edges)}")
print("=" * 80)
