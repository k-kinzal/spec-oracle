#!/usr/bin/env python3
"""
Connect U0 requirements to U3 implementations via Formalizes edges.

This addresses the core problem: 54/74 U0 specs lack U3 connections.
"""

import json
import uuid
import time
import re
from pathlib import Path

def normalize(text: str) -> str:
    """Normalize text for matching."""
    return re.sub(r'[^a-z0-9]+', ' ', text.lower()).strip()

def keyword_match(u0_content: str, u3_content: str) -> float:
    """Calculate keyword match score (0.0-1.0)."""
    u0_words = set(normalize(u0_content).split())
    u3_words = set(normalize(u3_content).split())

    if not u0_words or not u3_words:
        return 0.0

    intersection = u0_words & u3_words
    union = u0_words | u3_words

    return len(intersection) / len(union) if union else 0.0

def semantic_relevance(u0_content: str, u3_content: str) -> float:
    """Calculate semantic relevance with domain-specific boost."""
    score = keyword_match(u0_content, u3_content)

    # Boost for command-function matching
    if 'check command' in u0_content.lower() and 'check' in u3_content.lower():
        score += 0.3
    if 'find command' in u0_content.lower() and 'find' in u3_content.lower():
        score += 0.3
    if 'trace command' in u0_content.lower() and 'trace' in u3_content.lower():
        score += 0.3
    if 'detect contradiction' in u0_content.lower() and 'detect_contradiction' in u3_content.lower():
        score += 0.3
    if 'detect omission' in u0_content.lower() and 'detect_omission' in u3_content.lower():
        score += 0.3

    # Boost for implementation patterns
    if 'must' in u0_content.lower() and ('fn ' in u3_content or 'function' in u3_content):
        score += 0.1

    return min(score, 1.0)

def main():
    specs_file = Path('.spec/specs.json')

    with open(specs_file) as f:
        data = json.load(f)

    nodes = data['graph']['nodes']
    edges = data['graph']['edges']

    # Build existing edge index
    existing_edges = set()
    for e in edges:
        existing_edges.add((e[0], e[1]))
        existing_edges.add((e[1], e[0]))  # bidirectional check

    # Find U0 and U3 specs
    u0_specs = [(i, n) for i, n in enumerate(nodes)
                if n['formality_layer'] == 0 and n.get('metadata', {}).get('inferred') != 'true']
    u3_specs = [(i, n) for i, n in enumerate(nodes)
                if n['formality_layer'] == 3]

    print(f"Found {len(u0_specs)} U0 specs and {len(u3_specs)} U3 specs")
    print("Matching U0 requirements to U3 implementations...\n")

    # Match U0 to U3
    matches = []
    for u0_idx, u0_node in u0_specs:
        best_match = None
        best_score = 0.0

        for u3_idx, u3_node in u3_specs:
            # Skip if already connected
            if (u0_idx, u3_idx) in existing_edges:
                continue

            score = semantic_relevance(u0_node['content'], u3_node['content'])

            if score > best_score and score >= 0.4:  # threshold
                best_score = score
                best_match = (u3_idx, u3_node)

        if best_match:
            u3_idx, u3_node = best_match
            matches.append({
                'u0_idx': u0_idx,
                'u0_content': u0_node['content'][:60],
                'u3_idx': u3_idx,
                'u3_content': u3_node['content'][:60],
                'score': best_score
            })

    print(f"Found {len(matches)} potential connections (score >= 0.4)\n")

    if not matches:
        print("No connections found. Try lowering threshold.")
        return

    # Show top matches
    matches.sort(key=lambda m: m['score'], reverse=True)
    print("Top 10 matches:")
    for m in matches[:10]:
        print(f"  {m['score']:.2f} | U0: {m['u0_content']}")
        print(f"       | U3: {m['u3_content']}")
        print()

    # Create edges for reasonable-confidence matches (>= 0.5)
    high_confidence = [m for m in matches if m['score'] >= 0.5]
    print(f"\nCreating {len(high_confidence)} Formalizes edges (score >= 0.5)...")

    edges_created = 0
    for m in high_confidence:
        edge = [
            m['u0_idx'],
            m['u3_idx'],
            {
                'id': str(uuid.uuid4()),
                'kind': 'Formalizes',
                'metadata': {
                    'auto_inferred': 'true',
                    'confidence': str(m['score']),
                    'method': 'semantic_keyword_match'
                },
                'created_at': int(time.time())
            }
        ]
        edges.append(edge)
        edges_created += 1

    # Save
    with open(specs_file, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"✅ Created {edges_created} Formalizes edges (U0 → U3)")
    print(f"   Total edges: {len(edges)}")

    # Verify
    print("\nVerifying...")
    with open(specs_file) as f:
        verified = json.load(f)
    print(f"   Edges in file: {len(verified['graph']['edges'])}")

if __name__ == '__main__':
    main()
