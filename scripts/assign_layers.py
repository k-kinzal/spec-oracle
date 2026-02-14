#!/usr/bin/env python3
"""
Automatically assign formality layers to specifications based on content analysis.

Layer assignment rules:
- U0: Natural language requirements (must, should, user can, system must)
- U1: Formal specifications (TLA+, Alloy, formal models) - rare
- U2: Interface definitions (RPC, proto, API, gRPC)
- U3: Implementation details (code, invariants, preconditions, postconditions)
"""

import json
import re
from pathlib import Path


def classify_layer(spec):
    """Classify specification into formality layer based on content."""
    content = spec['content'].lower()
    kind = spec['kind']

    # Already has layer in metadata
    if 'formality_layer' in spec.get('metadata', {}):
        layer = spec['metadata']['formality_layer']
        if layer != 'unknown':
            return layer

    # U3: Implementation layer - code invariants, preconditions, postconditions
    u3_patterns = [
        r'invariant:',
        r'precondition:',
        r'postcondition:',
        r'code must',
        r'implementation must',
        r'function must',
        r'method must',
        r'\.rs:',  # Rust file references
        r'spec-core/',
        r'src/',
    ]
    if any(re.search(pattern, content) for pattern in u3_patterns):
        return 'U3'

    # U2: Interface layer - gRPC, proto, RPC, API specifications
    u2_patterns = [
        r'\brpc\b',
        r'grpc',
        r'proto',
        r'api endpoint',
        r'service definition',
        r'interface',
        r'request.*response',
        r'addnode|listnode|getnode',  # RPC method names
        r'detectcontradiction|detectomission',
    ]
    if any(re.search(pattern, content) for pattern in u2_patterns):
        return 'U2'

    # U1: Formal specifications - TLA+, Alloy, formal models (rare in this project)
    u1_patterns = [
        r'tla\+',
        r'alloy',
        r'formal model',
        r'temporal logic',
        r'formal proof',
    ]
    if any(re.search(pattern, content) for pattern in u1_patterns):
        return 'U1'

    # U0: Natural language requirements (default for most specs)
    # - User-facing features
    # - System requirements
    # - Behavioral specifications
    return 'U0'


def main():
    spec_file = Path('.spec/specs.json')

    if not spec_file.exists():
        print(f"Error: {spec_file} not found")
        return 1

    # Load specifications
    with open(spec_file) as f:
        data = json.load(f)

    nodes = data['graph']['nodes']

    # Count changes
    updated = 0
    by_layer = {'U0': 0, 'U1': 0, 'U2': 0, 'U3': 0}

    for node in nodes:
        # Get current layer
        current_layer = node.get('metadata', {}).get('formality_layer')

        # Only update if missing or unknown
        if not current_layer or current_layer == 'unknown':
            # Classify
            new_layer = classify_layer(node)

            # Update metadata
            if 'metadata' not in node:
                node['metadata'] = {}
            node['metadata']['formality_layer'] = new_layer

            updated += 1
            by_layer[new_layer] += 1

    # Save updated data
    if updated > 0:
        with open(spec_file, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Updated {updated} specifications")
        print("\nLayer distribution:")
        for layer in ['U0', 'U1', 'U2', 'U3']:
            if by_layer[layer] > 0:
                print(f"  {layer}: {by_layer[layer]} specs")
    else:
        print("No specifications needed updating")

    return 0


if __name__ == '__main__':
    exit(main())
