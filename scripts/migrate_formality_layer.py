#!/usr/bin/env python3
"""
Migrate formality_layer from metadata to proper field.

Problem: Specifications have both:
- formality_layer field (always 0, unused)
- metadata.formality_layer (actual value: "U0", "U1", "U2", "U3")

Solution: Consolidate into the formality_layer field with numeric values.

Mapping:
- "U0" -> 0 (natural language)
- "U1" -> 1 (formal specifications)
- "U2" -> 2 (interface definitions)
- "U3" -> 3 (executable implementation)
"""

import json
import sys
from pathlib import Path


def migrate_layer_value(metadata_value: str) -> int:
    """Convert metadata layer string to numeric value."""
    mapping = {
        "U0": 0,
        "U1": 1,
        "U2": 2,
        "U3": 3,
        "unknown": 0,  # Default to U0 for unknown
    }
    return mapping.get(metadata_value, 0)


def migrate_specs(specs_path: Path) -> tuple[int, int]:
    """
    Migrate formality_layer from metadata to field.

    Returns:
        (migrated_count, removed_metadata_count)
    """
    with open(specs_path, 'r') as f:
        data = json.load(f)

    migrated = 0
    removed_metadata = 0

    for node in data.get('graph', {}).get('nodes', []):
        metadata = node.get('metadata', {})

        # Check if metadata has formality_layer
        if 'formality_layer' in metadata:
            # Migrate to numeric field
            metadata_value = metadata['formality_layer']
            numeric_value = migrate_layer_value(metadata_value)

            # Update the field
            node['formality_layer'] = numeric_value
            migrated += 1

            # Remove from metadata
            del metadata['formality_layer']
            removed_metadata += 1

    # Write back
    with open(specs_path, 'w') as f:
        json.dump(data, f, indent=2)

    return migrated, removed_metadata


def verify_migration(specs_path: Path) -> dict:
    """Verify migration results."""
    with open(specs_path, 'r') as f:
        data = json.load(f)

    layer_counts = {0: 0, 1: 0, 2: 0, 3: 0}
    metadata_has_layer = 0

    for node in data.get('graph', {}).get('nodes', []):
        layer = node.get('formality_layer', 0)
        layer_counts[layer] = layer_counts.get(layer, 0) + 1

        if 'formality_layer' in node.get('metadata', {}):
            metadata_has_layer += 1

    return {
        'layer_counts': layer_counts,
        'metadata_has_layer': metadata_has_layer,
        'total_nodes': len(data.get('graph', {}).get('nodes', []))
    }


def main():
    specs_path = Path(__file__).parent.parent / '.spec' / 'specs.json'

    if not specs_path.exists():
        print(f"❌ Specs file not found: {specs_path}")
        sys.exit(1)

    print("🔄 Migrating formality_layer from metadata to field...")

    # Show before state
    before = verify_migration(specs_path)
    print(f"\n📊 Before migration:")
    print(f"  Total nodes: {before['total_nodes']}")
    print(f"  Nodes with metadata.formality_layer: {before['metadata_has_layer']}")
    print(f"  Layer distribution:")
    for layer, count in sorted(before['layer_counts'].items()):
        layer_name = ["U0", "U1", "U2", "U3"][layer]
        print(f"    {layer_name} (layer={layer}): {count}")

    # Migrate
    migrated, removed = migrate_specs(specs_path)

    # Show after state
    after = verify_migration(specs_path)
    print(f"\n✅ Migration complete!")
    print(f"  Migrated: {migrated} nodes")
    print(f"  Removed metadata: {removed} entries")
    print(f"\n📊 After migration:")
    print(f"  Total nodes: {after['total_nodes']}")
    print(f"  Nodes with metadata.formality_layer: {after['metadata_has_layer']}")
    print(f"  Layer distribution:")
    for layer, count in sorted(after['layer_counts'].items()):
        layer_name = ["U0", "U1", "U2", "U3"][layer]
        print(f"    {layer_name} (layer={layer}): {count}")

    if after['metadata_has_layer'] == 0:
        print("\n✅ All metadata.formality_layer entries removed successfully!")
    else:
        print(f"\n⚠️  Warning: {after['metadata_has_layer']} nodes still have metadata.formality_layer")


if __name__ == '__main__':
    main()
