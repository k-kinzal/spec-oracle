import assert from "node:assert/strict";
import test from "node:test";
import {
  contextNeighborPurity,
  contextSeparationAuc,
  densityBasinCounts,
  meanNeighborhoodJaccard,
  overlapCoverage,
} from "../benchmarks/metrics";
import {
  cleanContextFixture,
  nullFixture,
  overlapAndBridgeFixture,
} from "../benchmarks/fixtures";
import type {LayoutCoordinates} from "../benchmarks/types";
import {buildSparseAffinity} from "../benchmarks/affinity";
import {
  degreePreservingShuffle,
  densityAffinityEnrichment,
} from "../benchmarks/actual-metrics";
import {
  omitHighestDegreeFeatures,
  omitNonSemanticRoutes,
} from "../benchmarks/perturbations";
import {deriveSpecificationProximity} from "../lib/specification-proximity";

function separatedCoordinates(
  fixture: ReturnType<typeof cleanContextFixture>,
): LayoutCoordinates {
  const contextIndex = new Map(
    fixture.contextIds.map((context, index) => [context, index]),
  );
  const positions = new Map<string, {x: number; y: number}>();
  const withinIndex = new Map<string, number>();
  for (const id of fixture.specificationIds) {
    const role = fixture.roles.get(id);
    assert.equal(role?.kind, "context");
    if (role?.kind !== "context") continue;
    const index = withinIndex.get(role.context) ?? 0;
    withinIndex.set(role.context, index + 1);
    positions.set(id, {
      x: (contextIndex.get(role.context) ?? 0) * 1_000 + (index % 10) * 3,
      y: Math.floor(index / 10) * 3,
    });
  }
  return positions;
}

test("benchmark separation and purity recognize an unambiguous layout", () => {
  const fixture = cleanContextFixture(7, [20, 20, 20], false);
  const coordinates = separatedCoordinates(fixture);
  assert.ok(contextSeparationAuc(fixture, coordinates) > 0.99);
  assert.ok(contextNeighborPurity(fixture, coordinates, 5) > 0.99);
});

test("neighborhood Jaccard is invariant to rotation and translation", () => {
  const fixture = cleanContextFixture(8, [20, 20], false);
  const left = separatedCoordinates(fixture);
  const right = new Map(
    [...left].map(([id, point]) => [id, {x: -point.y + 25, y: point.x - 80}]),
  );
  assert.equal(
    meanNeighborhoodJaccard(
      fixture.specificationIds,
      left,
      right,
      10,
      1_000,
      fixture.seed,
    ),
    1,
  );
});

test("density basin evaluator reports one connected uniform body", () => {
  const fixture = nullFixture(9, 100);
  const coordinates = new Map<string, {x: number; y: number}>();
  for (let index = 0; index < fixture.specificationIds.length; index += 1) {
    coordinates.set(fixture.specificationIds[index], {
      x: index % 10,
      y: Math.floor(index / 10),
    });
  }
  assert.deepEqual(
    densityBasinCounts(fixture.specificationIds, coordinates).map(
      (value) => value.count,
    ),
    [1, 1, 1],
  );
});

test("degree-preserving null keeps every affinity degree", () => {
  const fixture = cleanContextFixture(10, [24, 28, 32], false);
  const model = buildSparseAffinity(fixture.nodes, fixture.edges);
  const shuffled = degreePreservingShuffle(model, 12345);
  assert.deepEqual(
    shuffled.adjacency.map((neighbors) => neighbors.size),
    model.adjacency.map((neighbors) => neighbors.size),
  );
  assert.equal(
    new Set(shuffled.edges.map((edge) => `${edge.source}:${edge.target}`)).size,
    shuffled.edges.length,
  );
  assert.equal(
    shuffled.edges.some((edge) => edge.source === edge.target),
    false,
  );
});

test("highest-degree ablation removes the universal feature", () => {
  const fixture = cleanContextFixture(11, [20, 24, 28], true);
  const perturbed = omitHighestDegreeFeatures(fixture.nodes, fixture.edges);
  const globalId = `term-${fixture.seed}-global`;
  assert.ok(
    perturbed.omittedFeatureIds.some((id) => id.endsWith(globalId)),
  );
  assert.equal(perturbed.nodes.some((node) => node.id === globalId), false);
  assert.equal(
    perturbed.edges.some(
      (edge) => edge.source === globalId || edge.target === globalId,
    ),
    false,
  );
});

test("feature ablation does not erase adjacent unselected bigrams", () => {
  const nodes = [
    {id: "s1", statement: "global localpair"},
    {id: "s2", statement: "global localpair"},
    {id: "s3", statement: "global other"},
    {id: "s4", statement: "unrelated fourth"},
  ].map((node) => ({
    ...node,
    nodeKind: "specification" as const,
    radius: 4,
    visible: true,
  }));
  const perturbed = omitHighestDegreeFeatures(nodes, []);
  assert.deepEqual(perturbed.omittedFeatureIds, ["lexical_unigram:global"]);
  const features = deriveSpecificationProximity(perturbed.nodes, []).hyperedges;
  assert.equal(
    features.some(
      (feature) => feature.id === "lexical_bigram:global\u0001localpair",
    ),
    true,
  );
});

test("route dropout masks each lexical feature incidence independently", () => {
  const nodes = Array.from({length: 1_000}, (_, index) => ({
    id: `dropout-${index}`,
    nodeKind: "specification" as const,
    statement: "common stable",
    radius: 4,
    visible: true,
  }));
  const perturbed = omitNonSemanticRoutes(nodes, [], 0, 0.1);
  const features = deriveSpecificationProximity(perturbed.nodes, []).hyperedges;
  for (const id of [
    "lexical_unigram:common",
    "lexical_unigram:stable",
    "lexical_bigram:common\u0001stable",
  ]) {
    const degree = features.find((feature) => feature.id === id)?.degree ?? 0;
    assert.ok(degree >= 850 && degree <= 950, `${id} degree=${degree}`);
  }
});

test("coordinate basins enrich source affinity over equal-size permutations", () => {
  const fixture = cleanContextFixture(12, [80, 80, 80, 80, 80], false);
  const model = buildSparseAffinity(fixture.nodes, fixture.edges);
  const coordinates = separatedCoordinates(fixture);
  const enrichment = densityAffinityEnrichment(
    model,
    coordinates,
    [10],
    12,
  );
  assert.ok(enrichment.results[0].basinCount >= fixture.contextIds.length);
  assert.ok(enrichment.results[0].z >= 3);
});

test("overlap neighbors represent both contexts they belong to", () => {
  const fixture = overlapAndBridgeFixture(13);
  const coordinates = new Map<string, {x: number; y: number}>();
  let overlapIndex = 0;
  for (const id of fixture.specificationIds) {
    const role = fixture.roles.get(id);
    if (role?.kind === "overlap") {
      coordinates.set(id, {x: overlapIndex % 5, y: Math.floor(overlapIndex / 5)});
      overlapIndex += 1;
    } else if (role?.kind === "context") {
      const contextIndex = fixture.contextIds.indexOf(role.context);
      coordinates.set(id, {x: 1_000 + contextIndex * 1_000, y: 0});
    } else {
      coordinates.set(id, {x: 5_000, y: 5_000});
    }
  }
  assert.equal(overlapCoverage(fixture, coordinates), 1);
});
