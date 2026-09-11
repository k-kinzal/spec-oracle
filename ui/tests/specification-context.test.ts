import assert from "node:assert/strict";
import test from "node:test";
import {
  buildSupportContextBoundaries,
  deriveSupportContextLinks,
  deriveSupportContexts,
  supportContextLayoutEdges,
} from "../lib/specification-context";
import type {GraphNode, ScoreContribution} from "../lib/types";

function contribution(
  kind: string,
  sourceNodeId: string | null,
  points = 3,
  edgeId = `${kind}-${sourceNodeId ?? "none"}`,
): ScoreContribution {
  return {
    kind,
    points,
    edgeId,
    sourceNodeId,
    evidenceNodeId: null,
    pathEdgeIds: [],
    detail: "",
  };
}

function node(
  id: string,
  contributions: ScoreContribution[] = [],
  current = true,
): GraphNode {
  return {
    id,
    nodeKind: "specification",
    statement: `Specification ${id}`,
    speechAct: "description",
    evidenceCount: 0,
    evidenceRequestCount: 0,
    current,
    evaluationState: current ? "current" : "receded",
    policyVersion: "selection/fitness-test",
    supportScore: 0,
    structuralScore: 0,
    evidenceScore: 0,
    relationScore: 0,
    conflictPressure: 0,
    contributions,
    exclusions: [],
  };
}

test("only positive current structural and realization contributions establish support links", () => {
  const nodes = [
    node("root"),
    node("target", [
      contribution("structural_support", "root", 4, "logical"),
      contribution("realization_support", "root", 2, "realization"),
      contribution("constitutive_evidence", "root", 10, "evidence"),
      contribution("structural_support", "root", -1, "negative"),
      contribution("structural_support", null, 3, "multi-root"),
    ]),
    node("retired"),
    node(
      "retired-target",
      [contribution("structural_support", "retired", 4)],
      false,
    ),
  ];

  assert.deepEqual(
    deriveSupportContextLinks(nodes).map((link) => ({
      source: link.source,
      target: link.target,
      kind: link.kind,
      points: link.points,
    })),
    [
      {
        source: "root",
        target: "target",
        kind: "realization_support",
        points: 2,
      },
      {
        source: "root",
        target: "target",
        kind: "structural_support",
        points: 4,
      },
    ],
  );
});

test("a transitive support chain forms one basin anchored by the supported sink", () => {
  const model = deriveSupportContexts([
    node("foundation"),
    node("middle", [
      contribution("structural_support", "foundation", 3, "foundation-middle"),
    ]),
    node("policy", [
      contribution("realization_support", "middle", 5, "middle-policy"),
    ]),
    node("unrelated"),
  ]);

  assert.equal(model.contexts.length, 1);
  assert.deepEqual(model.contexts[0].anchorIds, ["policy"]);
  assert.deepEqual(model.contexts[0].memberIds, [
    "foundation",
    "middle",
    "policy",
  ]);
  assert.equal(model.contexts[0].totalPoints, 8);
  assert.equal(model.contextualizedNodeCount, 3);
  assert.equal(model.sharedFoundationCount, 0);
});

test("one foundation may belong to overlapping basins without merging their anchors", () => {
  const model = deriveSupportContexts([
    node("foundation"),
    node("left", [
      contribution("structural_support", "foundation", 4, "left-support"),
    ]),
    node("right", [
      contribution("realization_support", "foundation", 6, "right-support"),
    ]),
  ]);

  assert.equal(model.contexts.length, 2);
  assert.deepEqual(
    model.contexts.map((context) => context.anchorIds),
    [["left"], ["right"]],
  );
  assert.deepEqual(
    model.contexts.map((context) => context.memberIds),
    [
      ["foundation", "left"],
      ["foundation", "right"],
    ],
  );
  assert.equal(model.membership.get("foundation")?.length, 2);
  assert.equal(model.sharedFoundationCount, 1);
});

test("support cycles are condensed and remain a total deterministic context", () => {
  const input = [
    node("a", [contribution("structural_support", "b", 2, "b-a")]),
    node("b", [contribution("structural_support", "a", 2, "a-b")]),
  ];
  const first = deriveSupportContexts(input);
  const second = deriveSupportContexts([...input].reverse());

  assert.deepEqual(first.contexts, second.contexts);
  assert.equal(first.contexts.length, 1);
  assert.deepEqual(first.contexts[0].anchorIds, ["a", "b"]);
  assert.deepEqual(first.contexts[0].memberIds, ["a", "b"]);
});

test("support links become invisible selection-weighted layout inputs", () => {
  const model = deriveSupportContexts([
    node("source"),
    node("target", [
      contribution("realization_support", "source", 5, "proof-edge"),
    ]),
  ]);
  const edges = supportContextLayoutEdges(model);

  assert.equal(edges.length, 1);
  assert.deepEqual(
    {
      source: edges[0].source,
      target: edges[0].target,
      family: edges[0].family,
      current: edges[0].current,
    },
    {
      source: "source",
      target: "target",
      family: "selection",
      current: true,
    },
  );
});

test("boundary envelopes are closed-ready, padded, and deterministic", () => {
  const model = deriveSupportContexts([
    node("a"),
    node("b", [contribution("structural_support", "a", 2, "a-b")]),
    node("c", [contribution("structural_support", "b", 2, "b-c")]),
  ]);
  const positions = new Map([
    ["a", {x: 0, y: 0}],
    ["b", {x: 20, y: 0}],
    ["c", {x: 10, y: 20}],
  ]);
  const first = buildSupportContextBoundaries(model.contexts, positions, 5);
  const second = buildSupportContextBoundaries(model.contexts, positions, 5);

  assert.deepEqual(first, second);
  assert.equal(first.length, 1);
  assert.equal(first[0].points.length, 6);
  assert.ok(Math.min(...first[0].points.map((point) => point.x)) < 0);
  assert.ok(Math.max(...first[0].points.map((point) => point.y)) > 20);

  const pairPositions = new Map([
    ["a", {x: 0, y: 0}],
    ["b", {x: 20, y: 0}],
  ]);
  const pair = buildSupportContextBoundaries(
    [
      {
        ...model.contexts[0],
        memberIds: ["a", "b"],
      },
    ],
    pairPositions,
    5,
  );
  assert.equal(pair[0].points.length, 24);
});
