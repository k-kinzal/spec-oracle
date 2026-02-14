#!/usr/bin/env python3
"""
Update all command modules to use Store instead of FileStore
"""
import re
from pathlib import Path

def update_file(file_path: Path):
    """Update a single file to use Store instead of FileStore"""
    content = file_path.read_text()
    original = content

    # Replace import statements
    content = re.sub(
        r'use spec_core::FileStore;',
        'use spec_core::Store;',
        content
    )
    content = re.sub(
        r'use spec_core::\{([^}]*)\bFileStore\b([^}]*)\}',
        lambda m: f'use spec_core::{{{m.group(1)}Store{m.group(2)}}}',
        content
    )

    # Replace function signatures
    content = re.sub(r'\&mut FileStore\b', '&mut Store', content)
    content = re.sub(r'\&FileStore\b', '&Store', content)

    # Only write if changed
    if content != original:
        file_path.write_text(content)
        print(f"Updated: {file_path}")
        return True
    return False

def main():
    commands_dir = Path('spec-cli/src/commands')

    # Get all .rs files in commands directory
    rs_files = list(commands_dir.glob('*.rs'))

    updated_count = 0
    for rs_file in rs_files:
        if update_file(rs_file):
            updated_count += 1

    print(f"\nUpdated {updated_count} files")

if __name__ == '__main__':
    main()
