#!/usr/bin/env python3
"""Connect Session 119 specifications to existing graph."""

import json
import sys
from pathlib import Path

def main():
    specs_path = Path.home() / "Projects/spec-oracle/.spec/specs.json"

    if not specs_path.exists():
        print(f"Error: {specs_path} not found")
        sys.exit(1)

    with open(specs_path) as f:
        data = json.load(f)

    graph = data["graph"]
    nodes = graph["nodes"]
    edges = graph["edges"]

    # Find nodes by ID prefix
    def find_node(id_prefix):
        for node in nodes:
            if node["id"].startswith(id_prefix):
                return node
        return None

    # New specifications (Session 119)
    php_test_extractor = find_node("6fe50517")  # PHPTestExtractor implementation
    php_multi_layer = find_node("49b943da")     # f₀₃⁻¹ reverse mapping
    session_119_achievement = find_node("0d10ca75")  # Session 119 achievement
    core_concept_realized = find_node("bc5ad960")  # Core concept realization
    multi_project = find_node("692f54e3")       # Multi-project management

    # Existing specifications
    rust_extractor = find_node("436c0a62")      # RustExtractor
    beyond_dsl = find_node("d79603df")          # Beyond-DSL paradigm
    ztd_demo = find_node("fbf3767e")            # ztd-query-php demo
    ztd_details = find_node("e1d91fb4")         # ztd-query-php details
    motivation_solved = find_node("eb677d27")   # motivation.md problems solved

    # Edges to add
    new_edges = []

    # 1. PHPTestExtractor refines RustExtractor concept
    if php_test_extractor and rust_extractor:
        new_edges.append({
            "id": f"{php_test_extractor['id'][:8]}-refines-{rust_extractor['id'][:8]}",
            "source": php_test_extractor["id"],
            "target": rust_extractor["id"],
            "kind": "Refines",
            "metadata": {
                "description": "PHPTestExtractor extends extraction pattern to PHP language"
            }
        })

    # 2. PHPTestExtractor demonstrates beyond-DSL paradigm
    if php_multi_layer and beyond_dsl:
        new_edges.append({
            "id": f"{php_multi_layer['id'][:8]}-demonstrates-{beyond_dsl['id'][:8]}",
            "source": php_multi_layer["id"],
            "target": beyond_dsl["id"],
            "kind": "Refines",
            "metadata": {
                "description": "f₀₃⁻¹ for PHP demonstrates language-agnostic extraction"
            }
        })

    # 3. Session 119 achievement refines ztd-query-php demo
    if session_119_achievement and ztd_demo:
        new_edges.append({
            "id": f"{session_119_achievement['id'][:8]}-refines-{ztd_demo['id'][:8]}",
            "source": session_119_achievement["id"],
            "target": ztd_demo["id"],
            "kind": "Refines",
            "metadata": {
                "description": "Session 119 completed multi-layer extraction for ztd-query-php"
            }
        })

    # 4. Core concept realization refines motivation.md solved
    if core_concept_realized and motivation_solved:
        new_edges.append({
            "id": f"{core_concept_realized['id'][:8]}-refines-{motivation_solved['id'][:8]}",
            "source": core_concept_realized["id"],
            "target": motivation_solved["id"],
            "kind": "Refines",
            "metadata": {
                "description": "Core concept realization confirms motivation.md problems are solved"
            }
        })

    # 5. Multi-project management refines ztd-query-php details
    if multi_project and ztd_details:
        new_edges.append({
            "id": f"{multi_project['id'][:8]}-refines-{ztd_details['id'][:8]}",
            "source": multi_project["id"],
            "target": ztd_details["id"],
            "kind": "Refines",
            "metadata": {
                "description": "Multi-project capability demonstrated with ztd-query-php"
            }
        })

    # Add edges (edges format: [source_index, target_index, metadata])
    for edge in new_edges:
        # Find node indices
        source_idx = next((i for i, n in enumerate(nodes) if n["id"] == edge["source"]), None)
        target_idx = next((i for i, n in enumerate(nodes) if n["id"] == edge["target"]), None)

        if source_idx is None or target_idx is None:
            print(f"⊘ Could not find nodes for edge: {edge['source'][:8]} --> {edge['target'][:8]}")
            continue

        # Check if edge already exists
        existing = any(e[0] == source_idx and e[1] == target_idx and e[2]["kind"] == edge["kind"] for e in edges)
        if not existing:
            edge_data = [
                source_idx,
                target_idx,
                {
                    "id": edge["id"],
                    "kind": edge["kind"],
                    "metadata": edge.get("metadata", {}),
                    "created_at": 1739590000  # timestamp
                }
            ]
            edges.append(edge_data)
            print(f"✓ Added edge: {edge['source'][:8]} --{edge['kind']}--> {edge['target'][:8]}")
        else:
            print(f"⊘ Edge already exists: {edge['source'][:8]} --> {edge['target'][:8]}")

    # Save
    with open(specs_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"\n✅ Connected {len(new_edges)} specifications")
    print(f"   Total edges: {len(edges)}")

if __name__ == "__main__":
    main()
