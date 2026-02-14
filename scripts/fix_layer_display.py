#!/usr/bin/env python3
"""
Fix formality_layer display code to use the field instead of metadata.

Replaces patterns like:
  node.metadata.get("formality_layer")
with:
  format_formality_layer(node.formality_layer)
"""

import re
from pathlib import Path


def fix_layer_display(file_path: Path):
    """Fix layer display code in main.rs"""
    with open(file_path, 'r') as f:
        content = f.read()

    # Pattern: if let Some(layer_str) = node.metadata.get("formality_layer") {
    #       -> let layer_str = format_formality_layer(node.formality_layer);

    # More complex: let layer_str = if let Some(l) = node.metadata.get("formality_layer") { l.clone() } else { "U0".to_string() };
    #            -> let layer_str = format_formality_layer(node.formality_layer);

    replacements = [
        # Simple pattern: if let Some(layer_str) = X.metadata.get("formality_layer") {
        # We'll replace the whole if-let block with a simple assignment
        (r'if let Some\(layer_str\) = (\w+)\.metadata\.get\("formality_layer"\) \{',
         r'let layer_str = format_formality_layer(\1.formality_layer); {'),

        # Pattern: if let Some(l) = X.metadata.get("formality_layer")
        # This is trickier because it's part of a larger expression
        # Let's handle the common pattern:
        # let layer_str = if let Some(l) = node.metadata.get("formality_layer") { l.clone() } else { "U0".to_string() };
        (r'let (\w+) = if let Some\(l\) = (\w+)\.metadata\.get\("formality_layer"\) \{\s*l\.clone\(\)\s*\} else \{\s*"U0"\.to_string\(\)\s*\};',
         r'let \1 = format_formality_layer(\2.formality_layer);'),

        # Another pattern: X.metadata.get("formality_layer").map(...).unwrap_or(...)
        (r'(\w+)\.metadata\.get\("formality_layer"\)\s*\.map\([^)]+\)\s*\.unwrap_or\([^)]+\)',
         r'format_formality_layer(\1.formality_layer)'),

        # Simple: X.metadata.get("formality_layer") (without map/unwrap)
        # But be careful - only replace if it's being used as a string value
        (r'let (\w+) = (\w+)\.metadata\.get\("formality_layer"\)',
         r'let \1 = Some(format_formality_layer(\2.formality_layer))'),
    ]

    for pattern, replacement in replacements:
        content = re.sub(pattern, replacement, content)

    with open(file_path, 'w') as f:
        f.write(content)

    return True


def main():
    project_root = Path(__file__).parent.parent
    main_rs = project_root / 'spec-cli' / 'src' / 'main.rs'

    if main_rs.exists():
        print(f"🔧 Fixing layer display code in {main_rs.relative_to(project_root)}...")
        fix_layer_display(main_rs)
        print("✅ Fixed")

        # Count remaining metadata.get references
        with open(main_rs, 'r') as f:
            content = f.read()
        remaining = len(re.findall(r'metadata\.get\("formality_layer"\)', content))
        if remaining > 0:
            print(f"⚠️  {remaining} metadata.get('formality_layer') references remain (may need manual review)")
        else:
            print("✅ All metadata.get('formality_layer') references removed!")


if __name__ == '__main__':
    main()
