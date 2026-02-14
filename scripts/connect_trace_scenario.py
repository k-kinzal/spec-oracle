#!/usr/bin/env python3
"""
Connect isolated trace command scenario to its implementation.

Node 17: "The trace command can visualize multi-layer specification chains..." (U0 Scenario)
Node 29: "The trace command must traverse relationships recursively..." (U3 Constraint)

Adding Formalizes edge: 17 -> 29
"""

import json
import time

specs_file = ".spec/specs.json"

# Read current specs
with open(specs_file, "r") as f:
    data = json.load(f)

# Add edge from node 17 (U0 Scenario) to node 29 (U3 implementation)
new_edge = [
    17,  # source: U0 Scenario
    29,  # target: U3 Constraint
    {
        "id": "connect-trace-scenario-001",
        "kind": "Formalizes",
        "metadata": {
            "reason": "U0 scenario formalized by U3 implementation constraint"
        },
        "created_at": int(time.time())
    }
]

# Check if edge already exists
existing_edges = data["graph"]["edges"]
edge_exists = any(
    e[0] == 17 and e[1] == 29 and e[2]["kind"] == "Formalizes"
    for e in existing_edges
)

if edge_exists:
    print("Edge already exists")
else:
    data["graph"]["edges"].append(new_edge)
    print(f"Added Formalizes edge: 17 -> 29")

# Write back
with open(specs_file, "w") as f:
    json.dump(data, f, indent=2)

print(f"Saved to {specs_file}")
