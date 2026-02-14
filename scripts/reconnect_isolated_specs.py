#!/usr/bin/env python3
"""
Reconnect isolated extracted specs using the new layer-aware threshold.
This script applies the cross-layer threshold (0.15) to existing isolated specs.
"""

import json
import uuid
from datetime import datetime

def calculate_jaccard_similarity(text1: str, text2: str) -> float:
    words1 = set(text1.lower().split())
    words2 = set(text2.lower().split())
    if not words1 or not words2:
        return 0.0
    intersection = len(words1 & words2)
    union = len(words1 | words2)
    return intersection / union if union > 0 else 0.0

def infer_edge_kind(src_layer: int, tgt_layer: int) -> str:
    """Infer edge kind based on layer relationship"""
    if src_layer < tgt_layer:
        return "Formalizes"  # Higher layer formalizes lower layer
    elif src_layer > tgt_layer:
        return "DerivesFrom"  # Lower layer derives from higher layer
    else:
        return "Refines"  # Same layer refines

def main():
    with open('.spec/specs.json') as f:
        data = json.load(f)

    # Find connected node indices
    connected_indices = set()
    for edge in data['graph']['edges']:
        connected_indices.add(edge[0])
        connected_indices.add(edge[1])

    # Find isolated extracted specs
    isolated = []
    for i, node in enumerate(data['graph']['nodes']):
        if (i not in connected_indices
            and node.get('metadata', {}).get('inferred') == 'true'):
            isolated.append((i, node))

    print(f"Found {len(isolated)} isolated extracted specs")

    # Get all non-extracted specs (potential targets)
    targets = []
    for i, node in enumerate(data['graph']['nodes']):
        if not node.get('metadata', {}).get('inferred'):
            targets.append((i, node))

    print(f"Found {len(targets)} manual specs (potential targets)")

    # Find connections using layer-aware threshold
    new_edges = []
    edge_suggestions = []

    for iso_idx, iso_node in isolated:
        iso_layer = iso_node.get('formality_layer', 0)
        best_matches = []

        for tgt_idx, tgt_node in targets:
            tgt_layer = tgt_node.get('formality_layer', 0)

            # Calculate similarity
            sim = calculate_jaccard_similarity(iso_node['content'], tgt_node['content'])

            # Layer-aware threshold
            threshold = 0.15 if iso_layer != tgt_layer else 0.3

            if sim >= threshold:
                edge_kind = infer_edge_kind(iso_layer, tgt_layer)
                best_matches.append((sim, tgt_idx, tgt_node, edge_kind))

        # Sort by similarity and take top matches
        best_matches.sort(reverse=True, key=lambda x: x[0])

        for sim, tgt_idx, tgt_node, edge_kind in best_matches[:3]:  # Top 3 matches
            if sim >= 0.15:
                # Cross-layer threshold met: auto-create
                # (Analysis shows all pairs >= 0.15 are legitimate connections)
                new_edges.append((iso_idx, tgt_idx, edge_kind, sim))
            else:
                # Below threshold: suggest for review
                edge_suggestions.append((iso_idx, tgt_idx, edge_kind, sim, iso_node, tgt_node))

    print(f"\n{'='*80}")
    print(f"Results:")
    print(f"{'='*80}")
    print(f"High-confidence edges (auto-create, sim >= 0.15): {len(new_edges)}")
    print(f"Edge suggestions (review needed, sim < 0.15): {len(edge_suggestions)}")

    if new_edges:
        print(f"\nWill create {len(new_edges)} edges")

    if edge_suggestions:
        print(f"\nTop 10 edge suggestions for manual review:")
        print("-" * 80)
        for src_idx, tgt_idx, kind, sim, src, tgt in edge_suggestions[:10]:
            print(f"\nSimilarity: {sim:.3f}, Kind: {kind}")
            print(f"  Source [U{src.get('formality_layer', 0)}]: {src['content'][:60]}...")
            print(f"  Target [U{tgt.get('formality_layer', 0)}]: {tgt['content'][:60]}...")

    # Create edges
    if new_edges:
        print(f"\n{'='*80}")
        print(f"Creating {len(new_edges)} high-confidence edges...")
        print(f"{'='*80}")

        for src_idx, tgt_idx, kind, sim in new_edges:
            edge_id = str(uuid.uuid4())
            edge_data = {
                "id": edge_id,
                "kind": kind,
                "metadata": {
                    "similarity": str(sim),
                    "auto_generated": "true",
                    "reconnection": "true",
                    "date": datetime.now().strftime("%Y-%m-%d")
                },
                "created_at": int(datetime.now().timestamp())
            }
            data['graph']['edges'].append([src_idx, tgt_idx, edge_data])

            src_node = data['graph']['nodes'][src_idx]
            tgt_node = data['graph']['nodes'][tgt_idx]
            print(f"Created: {src_node['content'][:40]}... --{kind}-> {tgt_node['content'][:40]}... (sim={sim:.3f})")

        # Save updated graph
        with open('.spec/specs.json', 'w') as f:
            json.dump(data, f, indent=2)

        print(f"\n✅ Saved {len(new_edges)} new edges to .spec/specs.json")
    else:
        print("\n⚠️  No edges found meeting cross-layer threshold (>= 0.15)")
        print("    Review edge suggestions below threshold")

if __name__ == '__main__':
    main()
