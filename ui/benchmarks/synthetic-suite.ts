import {performance} from "node:perf_hooks";
import {
  cleanContextFixture,
  disconnectedFixture,
  hierarchicalFixture,
  noisyIncompleteFixture,
  nullFixture,
  overlapAndBridgeFixture,
  scaleContextFixture,
} from "./fixtures";
import {
  bridgeCoverage,
  contextNeighborPurity,
  contextSeparationAuc,
  coordinateIntegrity,
  densityBasinCounts,
  disconnectedGapRatio,
  hierarchyOrder,
  meanNeighborhoodJaccard,
  overlapCoverage,
} from "./metrics";
import {resultCoordinates, type LayoutCandidate} from "./types";

type Diagnostic = {
  id: string;
  value: unknown;
  interpretation: string;
};

function timedLayout(
  candidate: LayoutCandidate,
  fixture: ReturnType<typeof cleanContextFixture>,
) {
  const started = performance.now();
  const result = candidate.layout(fixture.nodes, fixture.edges);
  return {
    result,
    coordinates: resultCoordinates(result),
    elapsedMs: performance.now() - started,
  };
}

function byteIdentical(left: Float32Array, right: Float32Array) {
  if (left.byteLength !== right.byteLength) return false;
  const leftBytes = new Uint8Array(left.buffer, left.byteOffset, left.byteLength);
  const rightBytes = new Uint8Array(
    right.buffer,
    right.byteOffset,
    right.byteLength,
  );
  for (let index = 0; index < leftBytes.length; index += 1) {
    if (leftBytes[index] !== rightBytes[index]) return false;
  }
  return true;
}

export function runSyntheticSeed(
  candidate: LayoutCandidate,
  seed: number,
  options: {includeScale?: boolean} = {},
) {
  const cleanWithGlobal = cleanContextFixture(seed);
  const cleanWithoutGlobal = cleanContextFixture(
    seed,
    [36, 52, 68, 84, 100],
    false,
  );
  const hierarchy = hierarchicalFixture(seed);
  const overlapBridge = overlapAndBridgeFixture(seed);
  const noisy = noisyIncompleteFixture(seed);
  const nullGraph = nullFixture(seed);
  const disconnected = disconnectedFixture(seed);

  const cleanGlobalLayout = timedLayout(candidate, cleanWithGlobal);
  const cleanLocalLayout = timedLayout(candidate, cleanWithoutGlobal);
  const hierarchyLayout = timedLayout(candidate, hierarchy);
  const overlapLayout = timedLayout(candidate, overlapBridge);
  const noisyLayout = timedLayout(candidate, noisy);
  const nullLayout = timedLayout(candidate, nullGraph);
  const disconnectedLayout = timedLayout(candidate, disconnected);
  const scaleFixtures = options.includeScale
    ? [100, 1_000, 10_000].map((count) => scaleContextFixture(seed, count))
    : [];
  const scaleLayouts = scaleFixtures.map((fixture) => ({
    fixture,
    ...timedLayout(candidate, fixture),
  }));

  const cleanAuc = contextSeparationAuc(
    cleanWithGlobal,
    cleanGlobalLayout.coordinates,
  );
  const cleanPurity = contextNeighborPurity(
    cleanWithGlobal,
    cleanGlobalLayout.coordinates,
  );
  const globalJaccard = meanNeighborhoodJaccard(
    cleanWithGlobal.specificationIds,
    cleanGlobalLayout.coordinates,
    cleanLocalLayout.coordinates,
    20,
    1_000,
    seed,
  );
  const hierarchyResult = hierarchyOrder(
    hierarchy,
    hierarchyLayout.coordinates,
  );
  const overlapResult = overlapCoverage(
    overlapBridge,
    overlapLayout.coordinates,
  );
  const bridgeResult = bridgeCoverage(
    overlapBridge,
    overlapLayout.coordinates,
  );
  const noisyAuc = contextSeparationAuc(noisy, noisyLayout.coordinates);
  const noisyPurity = contextNeighborPurity(noisy, noisyLayout.coordinates);
  const nullBasins = densityBasinCounts(
    nullGraph.specificationIds,
    nullLayout.coordinates,
  );
  const gapRatio = disconnectedGapRatio(
    disconnected,
    disconnectedLayout.coordinates,
  );
  const integrity = coordinateIntegrity(
    cleanWithGlobal,
    cleanGlobalLayout.result,
  );
  const deterministicSecond = candidate.layout(
    cleanWithGlobal.nodes,
    cleanWithGlobal.edges,
  );
  const deterministicThird = candidate.layout(
    cleanWithGlobal.nodes,
    cleanWithGlobal.edges,
  );
  const deterministic =
    byteIdentical(
      cleanGlobalLayout.result.positions,
      deterministicSecond.positions,
    ) &&
    byteIdentical(
      cleanGlobalLayout.result.positions,
      deterministicThird.positions,
    );
  const scaleMetrics = scaleLayouts.map(({fixture, coordinates, elapsedMs}) => ({
    specifications: fixture.specificationIds.length,
    separationAuc: contextSeparationAuc(fixture, coordinates),
    neighborPurity: contextNeighborPurity(fixture, coordinates),
    elapsedMs,
  }));
  const scaleTenThousand = scaleMetrics.find(
    (metric) => metric.specifications === 10_000,
  );

  const diagnostics: Diagnostic[] = [
    {
      id: "clean-separation-auc",
      value: cleanAuc,
      interpretation: "Same-generated-context versus cross-context distance ordering.",
    },
    {
      id: "clean-neighbor-purity",
      value: cleanPurity,
      interpretation: "Local recovery of the fixture's hidden generating contexts.",
    },
    {
      id: "global-hub-neighborhood-preservation",
      value: globalJaccard,
      interpretation: "Change in geometric neighbors when universal evidence is added.",
    },
    {
      id: "hierarchy-distance-order",
      value: hierarchyResult,
      interpretation: "Distances within subcontexts, across siblings, and across parents.",
    },
    {
      id: "overlap-two-sided-neighborhood",
      value: overlapResult,
      interpretation: "How often overlapping Specifications remain near both generating contexts.",
    },
    {
      id: "bridge-two-sided-position",
      value: bridgeResult,
      interpretation: "How often bridge Specifications lie nearer both linked contexts than unrelated ones.",
    },
    {
      id: "noisy-separation-auc",
      value: noisyAuc,
      interpretation: "Context distance ordering after evidence omission and misleading cross-links.",
    },
    {
      id: "noisy-neighbor-purity",
      value: noisyPurity,
      interpretation: "Local hidden-context recovery under incomplete and misleading evidence.",
    },
    {
      id: "null-honesty",
      value: nullBasins,
      interpretation: "Density subdivisions manufactured when the generating graph has no local structure.",
    },
    {
      id: "disconnected-gap",
      value: gapRatio,
      interpretation: "Separation of disconnected components in local-radius units.",
    },
    {
      id: "coordinate-integrity",
      value: {
        ...integrity,
        invariantSatisfied:
          integrity.missing.length === 0 &&
          integrity.nonFinite === 0 &&
          integrity.nonzeroZ === 0,
      },
      interpretation: "Required all-Specification finite XY and z=0 invariant.",
    },
    {
      id: "three-run-determinism",
      value: {byteIdentical: deterministic, invariantSatisfied: deterministic},
      interpretation: "Required deterministic-output invariant.",
    },
    ...(options.includeScale
      ? [
          {
            id: "scale-quality-preservation",
            value: scaleMetrics,
            interpretation: "How hidden-context recovery changes from 100 to 10,000 Specifications.",
          },
          {
            id: "scale-absolute-clean-quality",
            value: scaleMetrics,
            interpretation: "Absolute hidden-context recovery at each generated graph size.",
          },
          {
            id: "scale-ten-thousand-runtime",
            value: {
              elapsedMs: scaleTenThousand?.elapsedMs ?? Number.NaN,
              engineeringLimitMs: 20_000,
              withinLimit:
                scaleTenThousand !== undefined &&
                scaleTenThousand.elapsedMs <= 20_000,
            },
            interpretation: "Production-feasibility constraint at 10,000 Specifications.",
          },
        ]
      : []),
  ];
  return {
    candidate: candidate.id,
    seed,
    diagnostics,
    elapsedMs: {
      cleanGlobal: cleanGlobalLayout.elapsedMs,
      cleanLocal: cleanLocalLayout.elapsedMs,
      hierarchy: hierarchyLayout.elapsedMs,
      overlapBridge: overlapLayout.elapsedMs,
      noisy: noisyLayout.elapsedMs,
      null: nullLayout.elapsedMs,
      disconnected: disconnectedLayout.elapsedMs,
      scale: scaleMetrics,
    },
  };
}
