#!/usr/bin/env python3
"""
Analyze why remaining proto specs are still isolated.
"""

import json

def calculate_jaccard_similarity(text1: str, text2: str) -> float:
    words1 = set(text1.lower().split())
    words2 = set(text2.lower().split())
    if not words1 or not words2:
        return 0.0
    intersection = len(words1 & words2)
    union = len(words1 | words2)
    return intersection / union if union > 0 else 0.0

def main():
    with open('.spec/specs.json') as f:
        data = json.load(f)

    # Find connected indices
    connected = set()
    for edge in data['graph']['edges']:
        connected.add(edge[0])
        connected.add(edge[1])

    # Find still-isolated proto specs
    isolated_proto_indices = []
    for i, node in enumerate(data['graph']['nodes']):
        if (i not in connected
            and node.get('metadata', {}).get('extractor') == 'proto_rpc'):
            isolated_proto_indices.append((i, node))

    # Get all manual specs
    manual_specs = [
        (i, node) for i, node in enumerate(data['graph']['nodes'])
        if not node.get('metadata', {}).get('extractor')
    ]

    print(f"Still isolated proto specs: {len(isolated_proto_indices)}")
    print(f"Manual specs (potential targets): {len(manual_specs)}")
    print()

    # Analyze each isolated spec
    low_similarity_count = 0
    for iso_idx, iso_node in isolated_proto_indices:
        best_sim = 0.0
        best_match = None

        for man_idx, man_node in manual_specs:
            sim = calculate_jaccard_similarity(iso_node['content'], man_node['content'])
            if sim > best_sim:
                best_sim = sim
                best_match = man_node

        if best_sim < 0.15:
            low_similarity_count += 1

        if best_sim < 0.10:
            print(f"Very low similarity (< 0.10): {iso_node['content'][:60]}...")
            print(f"  Best match (sim={best_sim:.3f}): {best_match['content'][:50] if best_match else 'none'}...")
            print()

    print(f"\nSummary:")
    print(f"  Isolated with max sim < 0.15: {low_similarity_count}/{len(isolated_proto_indices)}")
    print(f"  These specs may not have relevant requirements in U0")

if __name__ == '__main__':
    main()
