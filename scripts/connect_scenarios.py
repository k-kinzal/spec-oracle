#!/usr/bin/env python3
"""
Connect semantic test scenarios to their corresponding implementation specs.

This script focuses on Scenario-type specs which are more semantic than raw
Invariant assertions.
"""

import json
import uuid
from datetime import datetime

# Load specifications
with open('.spec/specs.json', 'r') as f:
    data = json.load(f)

nodes = data['graph']['nodes']
edges = data['graph']['edges']

# Build indexes
node_index = {}  # id_prefix -> full_node_index
for idx, node in enumerate(nodes):
    prefix = node['id'][:8]
    node_index[prefix] = idx

# Helper to add edge
def add_edge(source_prefix, target_prefix, kind, description):
    source_idx = node_index.get(source_prefix)
    target_idx = node_index.get(target_prefix)

    if source_idx is None or target_idx is None:
        return False

    # Check if exists
    for edge in edges:
        if edge[0] == source_idx and edge[1] == target_idx:
            return False

    # Create edge
    edge_data = {
        "id": str(uuid.uuid4()),
        "kind": kind,
        "metadata": {"auto_connected": "true", "session": "96"},
        "created_at": int(datetime.now().timestamp())
    }
    edges.append([source_idx, target_idx, edge_data])

    source_content = nodes[source_idx]['content'][:70]
    target_content = nodes[target_idx]['content'][:70]
    print(f"✅ {source_prefix} -> {target_prefix}")
    print(f"   {source_content}")
    print(f"   → {target_content}")
    return True

# Find U2 RPC specs for common operations
add_node_rpc = "41052fda"  # "AddNode RPC accepts content, kind, and metadata..."
get_node_rpc = "3c7619aa"  # "RPC GetNode: Retrieves a specific specification node..."
list_nodes_rpc = "f2d3472b"  # "RPC ListNodes: Lists all specification nodes..."
remove_node_rpc = "c579b564"  # "RPC RemoveNode: Deletes a specification node..."

# Scenario connections
scenario_connections = [
    # Node operations scenarios
    ("f5b19310", add_node_rpc, "Scenario: empty scenario creation"),

    # Add more scenarios based on content patterns...
]

# Find scenarios to connect automatically based on content
created_count = 0

for idx, node in enumerate(nodes):
    if not node.get('metadata', {}).get('inferred') == 'true':
        continue
    if node.get('kind') != 'Scenario':
        continue

    content = node['content'].lower()
    node_id = node['id'][:8]

    # Skip if already connected
    has_edges = any(e[0] == idx or e[1] == idx for e in edges)
    if has_edges:
        continue

    # Pattern matching for connections
    target = None
    description = ""

    if 'add' in content and 'node' in content:
        target = add_node_rpc
        description = "Tests node addition functionality"
    elif 'get' in content and 'node' in content:
        target = get_node_rpc
        description = "Tests node retrieval functionality"
    elif 'list' in content and 'node' in content:
        target = list_nodes_rpc
        description = "Tests node listing functionality"
    elif 'remove' in content and 'node' in content:
        target = remove_node_rpc
        description = "Tests node removal functionality"

    if target:
        if add_edge(node_id, target, "Refines", description):
            created_count += 1

# Save
with open('.spec/specs.json', 'w') as f:
    json.dump(data, f, indent=2)

print(f"\n✅ Created {created_count} scenario connections")
print(f"📊 Total edges: {len(edges)}")
