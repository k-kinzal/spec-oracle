#!/usr/bin/env python3
"""
Generate human-readable Markdown documentation from specifications.

This script reads .spec/specs.json and generates a structured Markdown document
organized by formality layers and specification kinds.

Usage:
    python3 scripts/export_specs_md.py > specs.md
    python3 scripts/export_specs_md.py --layer 0 > u0-specs.md
"""

import json
import sys
from pathlib import Path
from collections import defaultdict
from datetime import datetime
import argparse

def format_layer(layer: int) -> str:
    """Format formality layer as human-readable string."""
    layers = {
        0: "U0 (Natural Language Requirements)",
        1: "U1 (Formal Specifications)",
        2: "U2 (Interface Definitions)",
        3: "U3 (Executable Implementations)"
    }
    return layers.get(layer, f"U{layer}")

def format_kind(kind: str) -> str:
    """Format specification kind."""
    return kind.capitalize()

def format_timestamp(ts: int) -> str:
    """Format Unix timestamp as human-readable date."""
    return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")

def get_edge_descriptions(node_id: str, edges: list, nodes_by_id: dict) -> dict:
    """Get incoming and outgoing edges for a node."""
    incoming = []
    outgoing = []

    for edge_data in edges:
        if len(edge_data) != 3:
            continue
        source_idx, target_idx, edge_info = edge_data

        if target_idx < len(nodes_by_id['_list']):
            target_node = nodes_by_id['_list'][target_idx]
            if target_node['id'] == node_id:
                # Incoming edge
                if source_idx < len(nodes_by_id['_list']):
                    source_node = nodes_by_id['_list'][source_idx]
                    incoming.append({
                        'kind': edge_info.get('kind', 'unknown'),
                        'from': source_node['id'][:8],
                        'content': source_node['content'][:60]
                    })

        if source_idx < len(nodes_by_id['_list']):
            source_node = nodes_by_id['_list'][source_idx]
            if source_node['id'] == node_id:
                # Outgoing edge
                if target_idx < len(nodes_by_id['_list']):
                    target_node = nodes_by_id['_list'][target_idx]
                    outgoing.append({
                        'kind': edge_info.get('kind', 'unknown'),
                        'to': target_node['id'][:8],
                        'content': target_node['content'][:60]
                    })

    return {'incoming': incoming, 'outgoing': outgoing}

def main():
    parser = argparse.ArgumentParser(description='Export specifications to Markdown')
    parser.add_argument('--layer', type=int, help='Filter by formality layer (0-3)')
    parser.add_argument('--kind', type=str, help='Filter by specification kind')
    parser.add_argument('--with-edges', action='store_true', help='Include edge information')
    args = parser.parse_args()

    specs_path = Path.home() / "Projects/spec-oracle/.spec/specs.json"

    if not specs_path.exists():
        print(f"Error: {specs_path} not found", file=sys.stderr)
        sys.exit(1)

    with open(specs_path, 'r') as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph'].get('edges', [])

    # Index nodes by ID
    nodes_by_id = {'_list': nodes}
    for node in nodes:
        nodes_by_id[node['id']] = node

    # Group by layer and kind
    by_layer = defaultdict(lambda: defaultdict(list))
    for node in nodes:
        layer = node.get('formality_layer', 0)
        kind = node.get('kind', 'Unknown')

        # Apply filters
        if args.layer is not None and layer != args.layer:
            continue
        if args.kind and kind.lower() != args.kind.lower():
            continue

        by_layer[layer][kind].append(node)

    # Generate Markdown
    print("# specORACLE Specifications")
    print()
    print(f"**Generated**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"**Total Specifications**: {len(nodes)}")
    print()

    if args.layer is not None:
        print(f"**Filtered by Layer**: {format_layer(args.layer)}")
        print()
    if args.kind:
        print(f"**Filtered by Kind**: {format_kind(args.kind)}")
        print()

    print("---")
    print()

    # Output by layer
    for layer in sorted(by_layer.keys()):
        print(f"## {format_layer(layer)}")
        print()

        for kind in sorted(by_layer[layer].keys()):
            specs = by_layer[layer][kind]
            print(f"### {format_kind(kind)} ({len(specs)} specs)")
            print()

            for i, spec in enumerate(specs, 1):
                short_id = spec['id'][:8]
                content = spec['content']
                created = format_timestamp(spec.get('created_at', 0))

                print(f"#### {i}. [{short_id}] {content[:80]}{'...' if len(content) > 80 else ''}")
                print()

                if len(content) > 80:
                    print(f"**Full Content**: {content}")
                    print()

                print(f"- **ID**: `{spec['id']}`")
                print(f"- **Created**: {created}")

                metadata = spec.get('metadata', {})
                if metadata:
                    print(f"- **Metadata**:")
                    for key, value in metadata.items():
                        print(f"  - `{key}`: {value}")

                if args.with_edges:
                    edge_info = get_edge_descriptions(spec['id'], edges, nodes_by_id)
                    if edge_info['incoming'] or edge_info['outgoing']:
                        print(f"- **Relationships**:")
                        if edge_info['incoming']:
                            print(f"  - **Incoming**:")
                            for edge in edge_info['incoming']:
                                print(f"    - [{edge['from']}] --{edge['kind']}--> this spec")
                        if edge_info['outgoing']:
                            print(f"  - **Outgoing**:")
                            for edge in edge_info['outgoing']:
                                print(f"    - this spec --{edge['kind']}--> [{edge['to']}]")

                print()

        print("---")
        print()

    # Summary statistics
    print("## Summary Statistics")
    print()
    print(f"- **Total Specifications**: {len(nodes)}")
    print(f"- **Total Edges**: {len(edges)}")
    print()
    print("### By Layer")
    for layer in sorted(by_layer.keys()):
        count = sum(len(specs) for specs in by_layer[layer].values())
        print(f"- **{format_layer(layer)}**: {count} specifications")
    print()
    print("### By Kind (All Layers)")
    kind_counts = defaultdict(int)
    for layer_specs in by_layer.values():
        for kind, specs in layer_specs.items():
            kind_counts[kind] += len(specs)
    for kind in sorted(kind_counts.keys()):
        print(f"- **{format_kind(kind)}**: {kind_counts[kind]} specifications")

if __name__ == '__main__':
    main()
