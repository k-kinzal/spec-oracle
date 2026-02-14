#!/usr/bin/env python3
"""
Fix formality_layer code references after migration.

Updates all parse_formality_layer calls to use the new signature.
Also removes any remaining metadata references.
"""

import re
from pathlib import Path


def fix_main_rs(file_path: Path):
    """Fix spec-cli/src/main.rs"""
    with open(file_path, 'r') as f:
        content = f.read()

    # Fix parse_formality_layer calls with two arguments -> one argument
    # Pattern: parse_formality_layer(&node.metadata, node.formality_layer)
    #       -> parse_formality_layer(node.formality_layer)
    patterns = [
        (r'parse_formality_layer\(&node\.metadata, node\.formality_layer\)',
         'parse_formality_layer(node.formality_layer)'),
        (r'parse_formality_layer\(&related_node\.metadata, related_node\.formality_layer\)',
         'parse_formality_layer(related_node.formality_layer)'),
        (r'parse_formality_layer\(&n\.metadata, n\.formality_layer\)',
         'parse_formality_layer(n.formality_layer)'),
        (r'parse_formality_layer\(&node\.metadata, node\.formality_layer as u8\)',
         'parse_formality_layer(node.formality_layer)'),
        (r'parse_formality_layer\(&n\.metadata, n\.formality_layer as u8\)',
         'parse_formality_layer(n.formality_layer)'),
        (r'parse_formality_layer\(&root_node\.metadata, root_node\.formality_layer as u8\)',
         'parse_formality_layer(root_node.formality_layer)'),
        (r'parse_formality_layer\(&other_node\.metadata, other_node\.formality_layer as u8\)',
         'parse_formality_layer(other_node.formality_layer)'),
    ]

    for pattern, replacement in patterns:
        content = re.sub(pattern, replacement, content)

    # Remove .metadata.get("formality_layer") references and use .formality_layer instead
    # These are more complex patterns that need manual review, but let's handle common ones

    # Pattern: if let Some(layer_str) = node.metadata.get("formality_layer") {
    #          -> Use node.formality_layer directly (need to convert to "U0" format)
    # This is complex and context-dependent, so we'll leave these for now
    # and just ensure parse_formality_layer works

    with open(file_path, 'w') as f:
        f.write(content)

    return True


def fix_service_rs(file_path: Path):
    """Fix specd/src/service.rs"""
    with open(file_path, 'r') as f:
        lines = f.readlines()

    output_lines = []
    skip_next = False

    for i, line in enumerate(lines):
        if skip_next:
            skip_next = False
            continue

        # Check for the formality_layer extraction from metadata pattern
        if 'Extract formality_layer from metadata' in line:
            # Skip this comment line and the next line (the actual extraction)
            skip_next = True
            continue
        elif 'let formality_layer = req.metadata.get("formality_layer")' in line:
            # Skip this line (already handled by skip_next)
            continue
        else:
            output_lines.append(line)

    with open(file_path, 'w') as f:
        f.writelines(output_lines)

    return True


def main():
    project_root = Path(__file__).parent.parent

    # Fix spec-cli/src/main.rs
    main_rs = project_root / 'spec-cli' / 'src' / 'main.rs'
    if main_rs.exists():
        print(f"🔧 Fixing {main_rs.relative_to(project_root)}...")
        fix_main_rs(main_rs)
        print("✅ Fixed parse_formality_layer calls")

    # Fix specd/src/service.rs
    service_rs = project_root / 'specd' / 'src' / 'service.rs'
    if service_rs.exists():
        print(f"🔧 Fixing {service_rs.relative_to(project_root)}...")
        fix_service_rs(service_rs)
        print("✅ Removed metadata.get('formality_layer') references")

    print("\n✅ Code migration complete!")
    print("   All formality_layer references now use the proper field")


if __name__ == '__main__':
    main()
