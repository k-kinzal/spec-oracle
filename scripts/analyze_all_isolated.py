#!/usr/bin/env python3
"""
Analyze all isolated extracted specs and their similarity to requirements.
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

    # Find connected node indices
    connected_indices = set()
    for edge in data['graph']['edges']:
        connected_indices.add(edge[0])
        connected_indices.add(edge[1])

    # Get U0 requirements
    u0_reqs = [
        node for node in data['graph']['nodes']
        if not node.get('metadata', {}).get('extractor')
        and node.get('formality_layer', 0) == 0
    ]

    # Analyze each extractor type
    extractors = ['proto_rpc', 'test', 'doc', 'assertion']

    for extractor in extractors:
        print(f"\n{'='*80}")
        print(f"Extractor: {extractor}")
        print(f"{'='*80}")

        # Get isolated specs for this extractor
        isolated = []
        for i, node in enumerate(data['graph']['nodes']):
            if (node.get('metadata', {}).get('extractor') == extractor
                and i not in connected_indices):
                isolated.append(node)

        print(f"Isolated specs: {len(isolated)}")

        if not isolated:
            continue

        # Find best matches with U0 requirements
        print(f"\nTop 5 potential connections:")
        print("-" * 80)

        matches = []
        for iso_node in isolated[:5]:  # Limit to first 5 isolated
            best_sim = 0.0
            best_req = None

            for req in u0_reqs:
                sim = calculate_jaccard_similarity(iso_node['content'], req['content'])
                if sim > best_sim:
                    best_sim = sim
                    best_req = req

            matches.append((best_sim, iso_node, best_req))

        matches.sort(reverse=True, key=lambda x: x[0])

        for sim, iso, req in matches:
            print(f"\nSimilarity: {sim:.3f}")
            print(f"  Isolated: {iso['content'][:60]}...")
            if req:
                print(f"  Best req: {req['content'][:60]}...")
            else:
                print(f"  Best req: (none found)")

        # Overall statistics
        print(f"\n{extractor} statistics:")
        all_similarities = []
        for iso_node in isolated:
            for req in u0_reqs:
                sim = calculate_jaccard_similarity(iso_node['content'], req['content'])
                all_similarities.append(sim)

        if all_similarities:
            above_015 = sum(1 for s in all_similarities if s >= 0.15)
            above_010 = sum(1 for s in all_similarities if s >= 0.10)
            total = len(all_similarities)
            print(f"  Similarity >= 0.15: {above_015}/{total} ({above_015/total*100:.1f}%)")
            print(f"  Similarity >= 0.10: {above_010}/{total} ({above_010/total*100:.1f}%)")
            print(f"  Max similarity: {max(all_similarities):.3f}")

if __name__ == '__main__':
    main()
