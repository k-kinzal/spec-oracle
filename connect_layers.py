#!/usr/bin/env python3
"""
Connect U2 layer (gRPC RPC) specifications to U0 (natural language) and U3 (code) layers.
This implements the f (transform function) concept from the U/D/A/f model.
"""
import json
import subprocess
import re

def load_specs():
    """Load specifications from .spec/specs.json"""
    with open('.spec/specs.json', 'r') as f:
        data = json.load(f)
    return data['graph']

def get_node_by_id(graph, node_id):
    """Find node by ID"""
    for node in graph['nodes']:
        if node['id'] == node_id:
            return node
    return None

def get_node_index_by_id(graph, node_id):
    """Find node index by ID"""
    for i, node in enumerate(graph['nodes']):
        if node['id'] == node_id:
            return i
    return None

def find_u0_for_rpc(graph, rpc_content):
    """Find corresponding U0 specification for an RPC"""
    # Extract RPC name from content like "RPC AddNode: Creates a new..."
    match = re.match(r'RPC (\w+):', rpc_content)
    if not match:
        return None

    rpc_name = match.group(1)

    # Map RPC names to keywords in U0 specs
    keyword_map = {
        'AddNode': ['add', 'specifications'],
        'GetNode': ['get', 'retrieve', 'node'],
        'ListNodes': ['list', 'nodes'],
        'RemoveNode': ['remove', 'delete', 'node'],
        'AddEdge': ['edge', 'relationship'],
        'ListEdges': ['edge', 'relationship'],
        'RemoveEdge': ['remove', 'edge'],
        'Query': ['query', 'search', 'find'],
        'DetectContradictions': ['detect', 'contradiction'],
        'DetectOmissions': ['detect', 'omission'],
        'Check': ['check', 'command'],
        'DetectLayerInconsistencies': ['layer', 'inconsisten'],
        'ResolveTerminology': ['terminology', 'resolve'],
        'FilterByLayer': ['filter', 'layer'],
        'FindFormalizations': ['formalization', 'find'],
        'FindRelatedTerms': ['related', 'term'],
        'DetectPotentialSynonyms': ['synonym'],
        'GenerateContractTemplate': ['contract', 'template'],
        'GetTestCoverage': ['test', 'coverage'],
        'CalculateCompliance': ['compliance'],
        'GetComplianceReport': ['compliance', 'report'],
        'QueryAtTimestamp': ['timestamp', 'query'],
        'DiffTimestamps': ['diff', 'timestamp'],
        'GetNodeHistory': ['history', 'node'],
        'GetComplianceTrend': ['compliance', 'trend'],
        'DetectInterUniverseInconsistencies': ['universe', 'inconsisten'],
        'SetNodeUniverse': ['universe', 'node'],
        'InferAllRelationships': ['infer', 'relationship'],
        'InferAllRelationshipsWithAi': ['infer', 'relationship', 'ai'],
    }

    keywords = keyword_map.get(rpc_name, [])
    if not keywords:
        return None

    # Find U0 specs containing these keywords
    candidates = []
    for node in graph['nodes']:
        layer = node.get('metadata', {}).get('formality_layer')
        if layer != 'U0' and node.get('formality_layer', 0) != 0:
            continue

        content_lower = node['content'].lower()
        if all(any(kw.lower() in content_lower for kw in [k]) for k in keywords):
            candidates.append(node)

    # Return the most relevant candidate (first match for now)
    return candidates[0] if candidates else None

def add_edge(source_id, target_id, edge_kind):
    """Add edge using spec CLI"""
    cmd = [
        './target/release/spec',
        'add-edge',
        source_id,
        target_id,
        '--kind', edge_kind
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode == 0

def main():
    print("🔗 Connecting U2 layer specifications to U0 layer...")
    print()

    graph = load_specs()

    # Find all U2 RPC specifications
    u2_specs = []
    for node in graph['nodes']:
        layer = node.get('metadata', {}).get('formality_layer')
        if layer == 'U2' and node['content'].startswith('RPC '):
            u2_specs.append(node)

    print(f"Found {len(u2_specs)} U2 RPC specifications")
    print()

    # Connect each U2 spec to corresponding U0 spec
    connected = 0
    not_found = 0

    for u2_node in u2_specs:
        u0_node = find_u0_for_rpc(graph, u2_node['content'])

        if u0_node:
            # Create Formalizes edge: U0 --Formalizes--> U2
            # This means U2 formalizes the natural language requirement in U0
            success = add_edge(u0_node['id'], u2_node['id'], 'Formalizes')

            if success:
                print(f"✓ Connected: {u0_node['content'][:60]}...")
                print(f"  └─> {u2_node['content'][:70]}")
                connected += 1
            else:
                print(f"✗ Failed to connect: {u2_node['content'][:70]}")
        else:
            rpc_match = re.match(r'RPC (\w+):', u2_node['content'])
            rpc_name = rpc_match.group(1) if rpc_match else 'Unknown'
            print(f"⚠️  No U0 found for: RPC {rpc_name}")
            not_found += 1

    print()
    print("=" * 70)
    print(f"Summary:")
    print(f"  Connected: {connected}")
    print(f"  Not found: {not_found}")
    print(f"  Total U2:  {len(u2_specs)}")

if __name__ == '__main__':
    main()
