#!/usr/bin/env python3
import json

with open('.spec/specs.json', 'r') as f:
    data = json.load(f)

# Remove Validates edges
original_count = len(data['graph']['edges'])
data['graph']['edges'] = [e for e in data['graph']['edges'] if e[2]['kind'] != 'Validates']
removed = original_count - len(data['graph']['edges'])

with open('.spec/specs.json', 'w') as f:
    json.dump(data, f, indent=2)

print(f"Removed {removed} invalid Validates edges")
print(f"Remaining edges: {len(data['graph']['edges'])}")
