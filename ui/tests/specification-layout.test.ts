import assert from "node:assert/strict";
import test from "node:test";
import {
  createSpecificationEvidenceSimulation,
  resumeSpecificationEvidenceSimulation,
  updateSpecificationEvidenceSimulation,
} from "../lib/specification-evidence-layout";
import {layoutSpecificationGraph} from "../lib/specification-layout";
import {
  deriveSpecificationProximity,
  isCompleteDefaultTopology,
  normalizedIncidenceWeight,
  normalizedInverseDocumentFrequency,
  selectDefaultSpecificationGraph,
  statementLexicalFeatures,
} from "../lib/specification-proximity";
import type {GraphEdge, GraphNode} from "../lib/types";

function node(
  id: string,
  nodeKind: GraphNode["nodeKind"] = "specification",
  statement = id,
): GraphNode {
  return {
    id,
    nodeKind,
    statement,
    speechAct: "unknown",
    evidenceCount: 0,
    evidenceRequestCount: 0,
    current: true,
    policyVersion: "",
    supportScore: 0,
    evidenceScore: 0,
    relationScore: 0,
    contributions: [],
    exclusions: [],
  };
}

test("completion status requires the declared complete Specification population", () => {
  assert.equal(isCompleteDefaultTopology(true, 5_000, 5_161), false);
  assert.equal(isCompleteDefaultTopology(false, 5_161, 5_161), false);
  assert.equal(isCompleteDefaultTopology(true, 5_161, 5_161), true);
});

function edge(
  id: string,
  source: string,
  target: string,
  family: GraphEdge["family"] = "lexical",
  current = true,
): GraphEdge {
  return {
    id,
    source,
    target,
    kind:
      family === "semantic"
        ? "refines"
        : family === "selection"
          ? "supports"
          : family === "projection"
            ? "has_guarantee"
            : "mentions_term",
    family,
    sourceRole: family === "semantic" ? "refiner" : "mentioner",
    targetRole: family === "semantic" ? "refined" : "mentioned_term",
    sourceAnchor: null,
    targetAnchor: null,
    reliedSpecId: null,
    current,
    derivationMethod: "test",
    derivationVersion: "test",
  };
}

function layout(nodes: GraphNode[], edges: GraphEdge[]) {
  return layoutSpecificationGraph(
    nodes.map((value) => ({
      id: value.id,
      nodeKind: value.nodeKind,
      statement: value.statement,
      radius: value.nodeKind === "specification" ? 4 : 3,
      visible: value.nodeKind === "specification",
    })),
    edges,
  );
}

function positions(result: ReturnType<typeof layoutSpecificationGraph>) {
  return new Map(
    result.ids.map(
      (id, index) =>
        [
          id,
          {
            x: result.positions[index * 3],
            y: result.positions[index * 3 + 1],
            z: result.positions[index * 3 + 2],
          },
        ] as const,
    ),
  );
}

function distance(
  coordinates: ReturnType<typeof positions>,
  left: string,
  right: string,
) {
  const a = coordinates.get(left);
  const b = coordinates.get(right);
  assert.ok(a && b);
  return Math.hypot(a.x - b.x, a.y - b.y);
}

function meanPairDistance(
  coordinates: ReturnType<typeof positions>,
  left: string[],
  right = left,
) {
  const distances: number[] = [];
  for (let leftIndex = 0; leftIndex < left.length; leftIndex += 1) {
    for (let rightIndex = 0; rightIndex < right.length; rightIndex += 1) {
      if (left === right && rightIndex <= leftIndex) continue;
      distances.push(distance(coordinates, left[leftIndex], right[rightIndex]));
    }
  }
  return distances.reduce((sum, value) => sum + value, 0) / distances.length;
}

test("two local vocabularies form two dense regions despite one global Term", () => {
  const a = ["a1", "a2", "a3", "a4", "a5"];
  const b = ["b1", "b2", "b3", "b4", "b5"];
  const nodes = [
    ...a.map((id, index) =>
      node(id, "specification", `intake request appends durable candidate ${index}`),
    ),
    ...b.map((id, index) =>
      node(id, "specification", `graph viewport renders visible topology ${index}`),
    ),
    node("global", "term", "system"),
  ];
  const edges = [...a, ...b].map((id) => edge(`global-${id}`, id, "global"));
  const coordinates = positions(layout(nodes, edges));
  const within = (meanPairDistance(coordinates, a) + meanPairDistance(coordinates, b)) / 2;
  const between = meanPairDistance(coordinates, a, b);

  assert.ok(within < between * 0.7, `within=${within}, between=${between}`);
});

test("one global Term remains factual without manufacturing subgroup signals", () => {
  const specifications = Array.from({length: 12}, (_, index) =>
    node(`s${index}`, "specification", `unique${index}`),
  );
  const nodes = [...specifications, node("global", "term", "system")];
  const edges = specifications.map((value) =>
    edge(`global-${value.id}`, value.id, "global"),
  );
  const model = deriveSpecificationProximity(nodes, edges);
  const termLinks = model.links.filter((link) => link.signal === "shared_term");

  assert.equal(model.hyperedges.length, 1);
  assert.equal(model.hyperedges[0].signal, "shared_term");
  assert.equal(model.hyperedges[0].degree, specifications.length);
  assert.equal(termLinks.length, specifications.length);
  assert.equal(new Set(termLinks.map((link) => link.weight)).size, 1);
  assert.equal(termLinks[0].weight, 1.35 * 0.35 * normalizedIncidenceWeight(12));
  assert.equal("membership" in model, false);
});

test("independent shared routes make Specifications closer", () => {
  const specifications = [
    node("single-a", "specification", "uniqueone"),
    node("single-b", "specification", "uniquetwo"),
    node("repeated-a", "specification", "uniquethree"),
    node("repeated-b", "specification", "uniquefour"),
  ];
  const connectors = ["single", "repeated-1", "repeated-2", "repeated-3"].map(
    (id) => node(id, "term"),
  );
  const edges = [
    edge("single-a-route", "single-a", "single"),
    edge("single-b-route", "single-b", "single"),
    ...["repeated-1", "repeated-2", "repeated-3"].flatMap((connector) => [
      edge(`${connector}-a`, "repeated-a", connector),
      edge(`${connector}-b`, "repeated-b", connector),
    ]),
  ];
  const coordinates = positions(layout([...specifications, ...connectors], edges));

  const repeatedDistance = distance(coordinates, "repeated-a", "repeated-b");
  const singleDistance = distance(coordinates, "single-a", "single-b");
  assert.ok(
    repeatedDistance < singleDistance,
    `repeated=${repeatedDistance}, single=${singleDistance}`,
  );
});

test("a persisted semantic Edge pulls more strongly than lexical candidate proximity", () => {
  const nodes = [
    node("semantic-a", "specification", "uniquealpha"),
    node("semantic-b", "specification", "uniquebeta"),
    node("lexical-a", "specification", "nexus leftalpha"),
    node("lexical-b", "specification", "nexus rightbeta"),
  ];
  const semantic = edge("semantic", "semantic-a", "semantic-b", "semantic");
  const model = deriveSpecificationProximity(nodes, [semantic]);
  const semanticWeight = model.links.find((link) => link.id === "semantic")?.weight ?? 0;
  const lexicalWeight = Math.max(
    ...model.hyperedges.flatMap((feature) =>
      feature.members.map((member) => member.weight),
    ),
  );
  const coordinates = positions(layout(nodes, [semantic]));

  assert.ok(semanticWeight > lexicalWeight);
  const semanticDistance = distance(coordinates, "semantic-a", "semantic-b");
  const lexicalDistance = distance(coordinates, "lexical-a", "lexical-b");
  assert.ok(
    semanticDistance < lexicalDistance,
    `semantic=${semanticDistance}, lexical=${lexicalDistance}`,
  );
});

test("the top Assumption contributes no default proximity route", () => {
  const nodes = [
    node("s1", "specification", "uniquealpha"),
    node("s2", "specification", "uniquebeta"),
    node("top", "assumption", "⊤"),
  ];
  const model = deriveSpecificationProximity(nodes, [
    edge("top-1", "s1", "top", "projection"),
    edge("top-2", "s2", "top", "projection"),
  ]);

  assert.equal(model.links.length, 0);
  assert.equal(model.hyperedges.length, 0);
});

test("the default input retains every Specification and removes top completely", () => {
  const nodes = [
    node("s1", "specification", "alpha"),
    node("s2", "specification", "beta"),
    node("isolated", "specification", "gamma"),
    node("top", "assumption", "⊤"),
    node("shared", "term", "shared"),
    node("degree-one", "term", "unique"),
  ];
  const selected = selectDefaultSpecificationGraph(nodes, [
    edge("top-1", "s1", "top", "projection"),
    edge("top-2", "s2", "top", "projection"),
    edge("shared-1", "s1", "shared"),
    edge("shared-2", "s2", "shared"),
    edge("degree-one", "isolated", "degree-one"),
  ]);

  assert.deepEqual(
    selected.nodes
      .filter((value) => value.nodeKind === "specification")
      .map((value) => value.id),
    ["s1", "s2", "isolated"],
  );
  assert.equal(selected.nodes.some((value) => value.id === "top"), false);
  assert.equal(selected.edges.some((value) => value.id.startsWith("top-")), false);
  assert.equal(selected.nodes.some((value) => value.id === "degree-one"), false);
});

test("one complete layout is deterministic, includes every Specification, and fixes Z at zero", () => {
  const nodes = [
    node("s1", "specification", "shared phrase alpha"),
    node("s2", "specification", "shared phrase beta"),
    node("s3", "specification", "isolated gamma"),
    node("term", "term", "shared"),
  ];
  const edges = [edge("e1", "s1", "term"), edge("e2", "s2", "term")];
  const first = layout(nodes, edges);
  const second = layout(nodes, edges);

  assert.deepEqual(first.ids, nodes.map((value) => value.id));
  assert.deepEqual([...first.positions], [...second.positions]);
  assert.equal(first.ids.filter((id) => id.startsWith("s")).length, 3);
  for (let index = 2; index < first.positions.length; index += 3) {
    assert.equal(first.positions[index], 0);
  }
});

test("streaming appends preserve one simulation and every existing Node state", () => {
  const state = createSpecificationEvidenceSimulation();
  const simulation = state.simulation;
  const first = {
    id: "stream-first",
    nodeKind: "specification" as const,
    statement: "append specification candidate",
    radius: 4,
    visible: true,
  };
  const second = {
    id: "stream-second",
    nodeKind: "specification" as const,
    statement: "append specification evidence",
    radius: 4,
    visible: true,
  };

  const initialUpdate = updateSpecificationEvidenceSimulation(state, [first], []);
  assert.equal(initialUpdate.changed, true);
  assert.equal(resumeSpecificationEvidenceSimulation(state), 1);
  simulation.stop().tick(4);
  const existingNode = state.simulationNodes[0];
  const before = {
    x: existingNode.x,
    y: existingNode.y,
    vx: existingNode.vx,
    vy: existingNode.vy,
    alpha: simulation.alpha(),
  };

  const appendUpdate = updateSpecificationEvidenceSimulation(state, [second], []);

  assert.equal(appendUpdate.addedSpecifications, 1);
  assert.equal(state.simulation, simulation);
  assert.equal(state.simulationNodes[0], existingNode);
  assert.deepEqual(
    {
      x: existingNode.x,
      y: existingNode.y,
      vx: existingNode.vx,
      vy: existingNode.vy,
      alpha: simulation.alpha(),
    },
    before,
  );
  simulation.alpha(0.01);
  assert.equal(resumeSpecificationEvidenceSimulation(state), 0.16);
  simulation.stop();
});

test("a status-only update cannot rebuild, reheat, or move the objective", () => {
  const input = {
    id: "status-only",
    nodeKind: "specification" as const,
    statement: "display specification graph",
    radius: 4,
    visible: true,
  };
  const state = createSpecificationEvidenceSimulation([input], []);
  const simulation = state.simulation;
  simulation.tick(3);
  const model = state.model;
  const node = state.simulationNodes[0];
  const updateCount = state.objectiveUpdates;
  const before = {
    x: node.x,
    y: node.y,
    vx: node.vx,
    vy: node.vy,
    alpha: simulation.alpha(),
  };

  const update = updateSpecificationEvidenceSimulation(state, [], []);

  assert.equal(update.changed, false);
  assert.equal(state.simulation, simulation);
  assert.equal(state.model, model);
  assert.equal(state.simulationNodes[0], node);
  assert.equal(state.objectiveUpdates, updateCount);
  assert.deepEqual(
    {
      x: node.x,
      y: node.y,
      vx: node.vx,
      vy: node.vy,
      alpha: simulation.alpha(),
    },
    before,
  );
});

test("lexical extraction and IDF contain no authored context label", () => {
  const features = statementLexicalFeatures(
    "The AddSpecification command shall display the specification graph.",
  );
  assert.ok(features.unigrams.has("add"));
  assert.ok(features.unigrams.has("specification"));
  assert.ok(features.bigrams.has("specification\u0001graph"));
  assert.ok(
    normalizedInverseDocumentFrequency(100, 2) >
      normalizedInverseDocumentFrequency(100, 80),
  );
});
