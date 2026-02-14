#!/usr/bin/env python3
"""
Reclassify specification kinds based on semantic patterns from conversation.md.

Classification rules (from conversation.md):
- Constraint (∀): Universal requirements - "must", "shall", "forbidden", "prohibited"
- Scenario (∃): Existential requirements - "can", "should be able to", "supports", "enables"
- Assertion: Specific claims about behavior or state
- Definition: Term definitions
- Domain: Domain boundary declarations
"""

import json
import re
from pathlib import Path


def classify_kind(spec):
    """Classify specification kind based on content patterns."""
    content = spec['content']
    content_lower = content.lower()

    # Constraint patterns (∀ - universal requirements)
    constraint_patterns = [
        # Strong modal verbs
        r'\bmust\b',
        r'\bshall\b',
        r'\brequired\b',
        r'\bmandatory\b',
        # Prohibitions
        r'\bforbidden\b',
        r'\bprohibited\b',
        r'\bcannot\b',
        r'\bmust not\b',
        r'\bshall not\b',
        # Invariants and pre/post conditions
        r'^invariant:',
        r'^precondition:',
        r'^postcondition:',
        # Always/never statements
        r'\balways\b',
        r'\bnever\b',
        # RPC/API behavior requirements (present tense = required behavior)
        r'\brpc (returns?|accepts?|provides?|invokes?)\b',
        r'^the .* (command|function|method|rpc) (returns?|accepts?|provides?|checks?|validates?|verifies?|detects?|displays?)\b',
        # System behavior requirements
        r'^the system (returns?|accepts?|provides?|checks?|validates?|verifies?|detects?)\b',
        # Function/check behavior
        r'^.+\(\) (converts?|checks?|traverses?|validates?|verifies?|detects?)\b',
        r'^(completeness|soundness|consistency) check\b',
    ]

    # Scenario patterns (∃ - existential requirements)
    scenario_patterns = [
        # Capability expressions
        r'\bcan\b',
        r'\bshould be able to\b',
        r'\benables?\b',
        r'\ballows?\b',
        r'\bsupports?\b',
        # User scenarios
        r'^users can\b',
        r'^a user can\b',
        r'^the system can\b',
        # Test scenarios
        r'^when .* then\b',
        r'^given .* when .* then\b',
    ]

    # Definition patterns
    definition_patterns = [
        r'^a .* is defined as\b',
        r'^the term .* refers to\b',
        r'^\w+ is a\b',
        r'^\w+ means\b',
    ]

    # Check patterns
    if any(re.search(pattern, content_lower) for pattern in constraint_patterns):
        return 'Constraint'

    if any(re.search(pattern, content_lower) for pattern in scenario_patterns):
        return 'Scenario'

    if any(re.search(pattern, content_lower) for pattern in definition_patterns):
        return 'Definition'

    # Default: keep as Assertion if none of the patterns match
    return 'Assertion'


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
    changes = {'Constraint': 0, 'Scenario': 0, 'Definition': 0, 'Assertion': 0}
    total_changed = 0

    for node in nodes:
        old_kind = node['kind']
        new_kind = classify_kind(node)

        if old_kind != new_kind:
            node['kind'] = new_kind
            changes[new_kind] += 1
            total_changed += 1

    # Save updated data
    if total_changed > 0:
        with open(spec_file, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"✅ Reclassified {total_changed} specifications\n")
        print("Changes by new kind:")
        for kind in ['Constraint', 'Scenario', 'Definition', 'Assertion']:
            if changes[kind] > 0:
                print(f"  → {kind}: {changes[kind]} specs")

        # Show final distribution
        print("\n📊 Final kind distribution:")
        kind_counts = {}
        for node in nodes:
            kind = node['kind']
            kind_counts[kind] = kind_counts.get(kind, 0) + 1

        for kind in sorted(kind_counts.keys()):
            count = kind_counts[kind]
            pct = (count / len(nodes)) * 100
            print(f"  {kind}: {count} specs ({pct:.1f}%)")

    else:
        print("No specifications needed reclassification")

    return 0


if __name__ == '__main__':
    exit(main())
