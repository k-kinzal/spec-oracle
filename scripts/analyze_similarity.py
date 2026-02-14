#!/usr/bin/env python3
"""
Analyze semantic similarity between proto RPC specs and requirement specs.
This helps understand why proto specs are isolated.
"""

import json
from typing import Set

def calculate_jaccard_similarity(text1: str, text2: str) -> float:
    """Calculate Jaccard similarity (word set intersection / union)"""
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

    # Get proto RPC specs
    proto_specs = [
        (i, node) for i, node in enumerate(data['graph']['nodes'])
        if node.get('metadata', {}).get('extractor') == 'proto_rpc'
    ]

    # Get U0 requirement specs (manual = no extractor, layer 0)
    requirement_specs = [
        (i, node) for i, node in enumerate(data['graph']['nodes'])
        if not node.get('metadata', {}).get('extractor')  # Manual = no extractor
        and node.get('formality_layer', 0) == 0
    ]

    print(f"Proto RPC specs: {len(proto_specs)}")
    print(f"U0 requirement specs: {len(requirement_specs)}")
    print()

    # Calculate similarity matrix
    print("Top 10 similar pairs:")
    print("=" * 80)

    similarities = []
    for proto_idx, proto_node in proto_specs:
        for req_idx, req_node in requirement_specs:
            sim = calculate_jaccard_similarity(
                proto_node['content'],
                req_node['content']
            )
            similarities.append((sim, proto_node, req_node))

    # Sort by similarity
    similarities.sort(reverse=True, key=lambda x: x[0])

    for sim, proto, req in similarities[:10]:
        print(f"Similarity: {sim:.3f}")
        print(f"  Proto: {proto['content'][:60]}...")
        print(f"  Req:   {req['content'][:60]}...")
        print()

    # Statistics
    print("\nSimilarity distribution:")
    print("=" * 80)
    above_03 = sum(1 for s, _, _ in similarities if s >= 0.3)
    above_02 = sum(1 for s, _, _ in similarities if s >= 0.2)
    above_01 = sum(1 for s, _, _ in similarities if s >= 0.1)
    total = len(similarities)

    print(f"Total pairs: {total}")
    print(f"Similarity >= 0.3 (current threshold): {above_03} ({above_03/total*100:.1f}%)")
    print(f"Similarity >= 0.2: {above_02} ({above_02/total*100:.1f}%)")
    print(f"Similarity >= 0.1: {above_01} ({above_01/total*100:.1f}%)")

    if above_03 == 0:
        print("\n⚠️  No proto-requirement pairs above current threshold (0.3)!")
        print("    This explains why all proto specs are isolated.")

if __name__ == '__main__':
    main()
