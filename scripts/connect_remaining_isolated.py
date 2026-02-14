#!/usr/bin/env python3
"""
Connect remaining isolated specifications.
"""

import json
import uuid
from pathlib import Path

SPECS_PATH = Path('.spec/specs.json')

def load_specs():
    with open(SPECS_PATH) as f:
        return json.load(f)

def save_specs(data):
    with open(SPECS_PATH, 'w') as f:
        json.dump(data, f, indent=2)

def find_nodes_by_pattern(nodes, pattern):
    """Find all nodes matching pattern."""
    pattern = pattern.lower()
    matches = []
    for i, node in enumerate(nodes):
        if pattern in node['content'].lower():
            matches.append((i, node))
    return matches

def create_edge(source_idx, target_idx, kind="Formalizes"):
    """Create a new edge."""
    return [
        source_idx,
        target_idx,
        {
            "id": str(uuid.uuid4()),
            "kind": kind,
            "metadata": {"auto_connected": "true", "script": "connect_remaining_isolated.py"},
            "created_at": 1771086100
        }
    ]

def main():
    data = load_specs()
    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Build edge index
    node_edges = {}
    for edge in edges:
        src_idx, tgt_idx, _ = edge
        if src_idx not in node_edges:
            node_edges[src_idx] = []
        if tgt_idx not in node_edges:
            node_edges[tgt_idx] = []
        node_edges[src_idx].append(edge)
        node_edges[tgt_idx].append(edge)

    # Find isolated specs
    isolated = [(i, n) for i, n in enumerate(nodes) if i not in node_edges]
    print(f"Found {len(isolated)} isolated specs\n")

    new_edges = []

    # Connect each isolated spec
    for idx, node in isolated:
        content = node['content']
        layer = node.get('formality_layer', 0)
        print(f"[{idx}] [U{layer}] {content[:60]}...")

        # Pattern-based connections
        if "extraction engine must maintain idempotency" in content.lower():
            # Connect to extract command and construct-u0
            targets = find_nodes_by_pattern(nodes, "extract")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 2:
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "find_node_by_content()" in content:
            # Connect to deduplication
            targets = find_nodes_by_pattern(nodes, "duplicate")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 3:
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "ingest() method checks" in content.lower():
            # Connect to extraction
            targets = find_nodes_by_pattern(nodes, "ingest")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 3:
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "contradiction detection excludes composite" in content.lower():
            # Connect to contradiction detection
            targets = find_nodes_by_pattern(nodes, "detect contradictions")
            for t_idx, t_node in targets:
                if t_idx != idx and "must" in t_node['content'].lower():
                    edge = create_edge(idx, t_idx, "Refines")
                    new_edges.append(edge)
                    print(f"  → Refines [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "cli must provide a coherent" in content.lower():
            # Connect to CLI implementation
            targets = find_nodes_by_pattern(nodes, "cli")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 3:
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "human-friendly ux means" in content.lower():
            # This is a definition, connect to CLI requirements
            targets = find_nodes_by_pattern(nodes, "cli must")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 0:
                    edge = create_edge(t_idx, idx, "DependsOn")
                    new_edges.append(edge)
                    print(f"  ← DependsOn from [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "cli implementation must separate" in content.lower():
            # Connect to CLI structure
            targets = find_nodes_by_pattern(nodes, "main.rs")
            for t_idx, t_node in targets:
                if t_idx != idx:
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "all proto rpc definitions must" in content.lower():
            # Connect to proto extraction
            targets = find_nodes_by_pattern(nodes, "proto")
            for t_idx, t_node in targets:
                if t_idx != idx and "extract" in t_node['content'].lower():
                    edge = create_edge(idx, t_idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  → Formalizes [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "formality" in content.lower() and "reversed" in content.lower():
            # Doc about edge direction - connect to edge validation
            targets = find_nodes_by_pattern(nodes, "edge")
            for t_idx, t_node in targets:
                if t_idx != idx and "operations" in t_node['content'].lower():
                    edge = create_edge(idx, t_idx, "Refines")
                    new_edges.append(edge)
                    print(f"  → Refines [{t_idx}] {t_node['content'][:50]}")
                    break

        elif "scenario:" in content.lower() and "get node history" in content.lower():
            # Test scenario - connect to node history
            targets = find_nodes_by_pattern(nodes, "node history")
            for t_idx, t_node in targets:
                if t_idx != idx and t_node['formality_layer'] == 2:
                    edge = create_edge(t_idx, idx, "Formalizes")
                    new_edges.append(edge)
                    print(f"  ← Formalizes from [{t_idx}] {t_node['content'][:50]}")
                    break

    # Add new edges
    if new_edges:
        edges.extend(new_edges)
        data['graph']['edges'] = edges
        save_specs(data)
        print(f"\n✅ Added {len(new_edges)} edges")
        print(f"Total edges: {len(edges)}")
    else:
        print(f"\n⚠️ No new edges added")

if __name__ == '__main__':
    main()
