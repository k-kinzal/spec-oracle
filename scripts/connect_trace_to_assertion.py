#!/usr/bin/env python3
"""
Connect trace scenario to supporting assertion.

Node 17: "The trace command can visualize multi-layer specification chains..." (U0 Scenario)
Node 18: "Specifications at different formality layers are connected..." (U0 Assertion)

Adding DerivesFrom edge: 17 -> 18 (scenario derives from the assertion about formality layers)
"""

import json
import time

specs_file = ".spec/specs.json"

# Read current specs
with open(specs_file, "r") as f:
    data = json.load(f)

# Add edge from node 17 (Scenario) to node 18 (Assertion)
new_edge = [
    17,  # source: U0 Scenario
    18,  # target: U0 Assertion
    {
        "id": "scenario-derives-from-assertion-001",
        "kind": "DerivesFrom",
        "metadata": {
            "reason": "Trace scenario depends on formality layer connectivity assertion"
        },
        "created_at": int(time.time())
    }
]

# Check if edge already exists
existing_edges = data["graph"]["edges"]
edge_exists = any(
    e[0] == 17 and e[1] == 18
    for e in existing_edges
)

if edge_exists:
    print("Edge already exists")
else:
    data["graph"]["edges"].append(new_edge)
    print(f"Added DerivesFrom edge: 17 -> 18")

# Write back
with open(specs_file, "w") as f:
    json.dump(data, f, indent=2)

print(f"Saved to {specs_file}")
print("\nNode details:")
print("  17 (Scenario): The trace command can visualize multi-layer specification chains...")
print("  18 (Assertion): Specifications at different formality layers are connected via Formalizes edges...")
