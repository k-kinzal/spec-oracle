#!/usr/bin/env python3
"""
Export specORACLE specifications as DOT graph format for visualization.

Usage:
    python3 scripts/export_specs_dot.py [options] > specs.dot
    dot -Tpng specs.dot -o specs.png
    dot -Tsvg specs.dot -o specs.svg

Options:
    --layer N           Filter by formality layer (0-3)
    --kind TYPE         Filter by specification kind
    --max-content N     Limit node content length (default: 50)
    --layout ENGINE     Graphviz layout engine (dot, neato, fdp, sfdp, circo, twopi)
"""

import json
import sys
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Set

def escape_dot(text: str) -> str:
    """Escape special characters for DOT format."""
    return text.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')

def truncate_content(content: str, max_length: int) -> str:
    """Truncate content to max_length, adding ellipsis if needed."""
    if len(content) <= max_length:
        return content
    return content[:max_length - 3] + "..."

def get_layer_label(layer: int) -> str:
    """Get human-readable layer label."""
    labels = {0: "U0", 1: "U1", 2: "U2", 3: "U3"}
    return labels.get(layer, f"U{layer}")

def get_node_color(kind: str) -> str:
    """Get color for node based on kind."""
    colors = {
        "Assertion": "#E3F2FD",     # Light blue
        "Constraint": "#FFF3E0",    # Light orange
        "Scenario": "#F1F8E9",      # Light green
        "Definition": "#FCE4EC",    # Light pink
        "Domain": "#F3E5F5",        # Light purple
    }
    return colors.get(kind, "#F5F5F5")  # Light grey default

def get_layer_color(layer: int) -> str:
    """Get color for layer."""
    colors = {
        0: "#BBDEFB",  # Blue - Natural language
        1: "#C8E6C9",  # Green - Formal specs
        2: "#FFE0B2",  # Orange - Interface
        3: "#F8BBD0",  # Pink - Implementation
    }
    return colors.get(layer, "#E0E0E0")

def get_edge_style(kind: str) -> tuple:
    """Get style attributes for edge based on kind."""
    styles = {
        "Formalizes": ("blue", "normal", ""),
        "Refines": ("green", "normal", ""),
        "DerivesFrom": ("purple", "dashed", ""),
        "DependsOn": ("orange", "dotted", ""),
        "Synonym": ("grey", "dotted", 'style="dashed"'),
        "Relates": ("black", "solid", ""),
    }
    color, style, extra = styles.get(kind, ("black", "solid", ""))
    return (color, style, extra)

def export_dot(
    specs_path: Path,
    layer_filter: Optional[int] = None,
    kind_filter: Optional[str] = None,
    max_content: int = 50,
    layout: str = "dot"
) -> str:
    """Export specifications as DOT graph format."""

    # Load specifications
    with open(specs_path) as f:
        data = json.load(f)

    nodes = data["graph"]["nodes"]
    edges = data["graph"]["edges"]

    # Filter nodes
    filtered_nodes = nodes
    if layer_filter is not None:
        filtered_nodes = [n for n in filtered_nodes if n.get("formality_layer") == layer_filter]
    if kind_filter:
        filtered_nodes = [n for n in filtered_nodes if n.get("kind", "").lower() == kind_filter.lower()]

    # Create mapping of node ID to filtered node
    node_id_to_node = {n["id"]: n for n in filtered_nodes}
    node_ids = set(node_id_to_node.keys())

    # Build index to ID mapping for all nodes
    index_to_id = {i: node["id"] for i, node in enumerate(nodes)}

    # Filter edges to only include edges between filtered nodes
    # Edges are stored as [source_index, target_index, edge_data]
    filtered_edges = []
    for edge in edges:
        source_idx, target_idx, edge_data = edge
        source_id = index_to_id.get(source_idx)
        target_id = index_to_id.get(target_idx)

        if source_id in node_ids and target_id in node_ids:
            filtered_edges.append({
                "source": source_id,
                "target": target_id,
                "kind": edge_data.get("kind", "Relates"),
                "id": edge_data.get("id"),
            })

    # Build DOT output
    lines = []
    lines.append('digraph specORACLE {')
    lines.append('  // Graph attributes')
    lines.append(f'  layout="{layout}";')
    lines.append('  rankdir="TB";')  # Top to bottom
    lines.append('  node [shape=box, style="rounded,filled", fontname="Arial", fontsize=10];')
    lines.append('  edge [fontname="Arial", fontsize=9];')
    lines.append('  bgcolor="white";')
    lines.append('  splines="ortho";')  # Orthogonal edge routing
    lines.append('')

    # Add nodes
    lines.append('  // Nodes')
    for node in filtered_nodes:
        node_id = node["id"]
        short_id = node_id[:8]
        kind = node.get("kind", "Unknown")
        layer = node.get("formality_layer", 0)
        layer_label = get_layer_label(layer)
        content = node.get("content", "")
        truncated_content = truncate_content(content, max_content)

        # Node color based on kind
        color = get_node_color(kind)
        border_color = get_layer_color(layer)

        # Build label
        label = f"[{layer_label}] {short_id}\\n{kind}\\n\\n{escape_dot(truncated_content)}"

        lines.append(
            f'  "{node_id}" ['
            f'label="{label}", '
            f'fillcolor="{color}", '
            f'color="{border_color}", '
            f'penwidth=2'
            f'];'
        )

    lines.append('')

    # Add edges
    lines.append('  // Edges')
    for edge in filtered_edges:
        source = edge["source"]
        target = edge["target"]
        kind = edge.get("kind", "Relates")

        color, style, extra = get_edge_style(kind)

        edge_attrs = [
            f'label="{kind}"',
            f'color="{color}"',
            f'fontcolor="{color}"',
        ]
        if extra:
            edge_attrs.append(extra)

        attrs_str = ", ".join(edge_attrs)
        lines.append(f'  "{source}" -> "{target}" [{attrs_str}];')

    lines.append('}')

    return '\n'.join(lines)

def generate_stats(specs_path: Path) -> Dict:
    """Generate statistics about the specification graph."""
    with open(specs_path) as f:
        data = json.load(f)

    nodes = data["graph"]["nodes"]
    edges = data["graph"]["edges"]

    stats = {
        "total_nodes": len(nodes),
        "total_edges": len(edges),
        "by_layer": {},
        "by_kind": {},
    }

    for node in nodes:
        layer = node.get("formality_layer", 0)
        kind = node.get("kind", "Unknown")

        stats["by_layer"][layer] = stats["by_layer"].get(layer, 0) + 1
        stats["by_kind"][kind] = stats["by_kind"].get(kind, 0) + 1

    return stats

def main():
    parser = argparse.ArgumentParser(description="Export specORACLE specs as DOT graph")
    parser.add_argument("--layer", type=int, help="Filter by formality layer (0-3)")
    parser.add_argument("--kind", type=str, help="Filter by specification kind")
    parser.add_argument("--max-content", type=int, default=50, help="Max content length per node")
    parser.add_argument("--layout", type=str, default="dot",
                       choices=["dot", "neato", "fdp", "sfdp", "circo", "twopi"],
                       help="Graphviz layout engine")
    parser.add_argument("--stats", action="store_true", help="Print statistics instead of DOT")
    parser.add_argument("--specs", type=str, default=".spec/specs.json",
                       help="Path to specs.json file")

    args = parser.parse_args()

    specs_path = Path(args.specs)
    if not specs_path.exists():
        print(f"Error: Specifications file not found: {specs_path}", file=sys.stderr)
        sys.exit(1)

    if args.stats:
        # Print statistics
        stats = generate_stats(specs_path)
        print("# Specification Statistics")
        print(f"\nTotal Nodes: {stats['total_nodes']}")
        print(f"Total Edges: {stats['total_edges']}")
        print(f"\n## By Layer:")
        for layer in sorted(stats['by_layer'].keys()):
            label = get_layer_label(layer)
            count = stats['by_layer'][layer]
            print(f"  {label}: {count}")
        print(f"\n## By Kind:")
        for kind in sorted(stats['by_kind'].keys()):
            count = stats['by_kind'][kind]
            print(f"  {kind}: {count}")
    else:
        # Export DOT
        dot_output = export_dot(
            specs_path,
            layer_filter=args.layer,
            kind_filter=args.kind,
            max_content=args.max_content,
            layout=args.layout
        )
        print(dot_output)

if __name__ == "__main__":
    main()
