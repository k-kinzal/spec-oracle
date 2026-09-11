import {performance} from "node:perf_hooks";
import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
} from "../lib/specification-layout";
import {
  actualRelationAucs,
  densityAffinityEnrichment,
  independentSignalDistanceOrder,
  shuffledRecallNull,
  weightedNeighborhoodRecall,
} from "./actual-metrics";
import {buildSparseAffinity} from "./affinity";
import {FAILED_ACTUAL_NEIGHBORHOOD_RECALL} from "./baselines";
import {meanNeighborhoodJaccard} from "./metrics";
import {
  omitHighestDegreeFeatures,
  omitNonSemanticRoutes,
} from "./perturbations";
import {resultCoordinates, type LayoutCandidate} from "./types";

type Diagnostic = {
  id: string;
  value: unknown;
  interpretation: string;
};

function timedLayout(
  candidate: LayoutCandidate,
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
) {
  const started = performance.now();
  const result = candidate.layout(nodes, edges);
  return {
    result,
    coordinates: resultCoordinates(result),
    elapsedMs: performance.now() - started,
  };
}

function percentile(values: readonly number[], fraction: number) {
  const sorted = [...values].sort((left, right) => left - right);
  return sorted[
    Math.min(
      sorted.length - 1,
      Math.max(0, Math.ceil(sorted.length * fraction) - 1),
    )
  ];
}

export function runActualGraphSuite(
  candidate: LayoutCandidate,
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {full?: boolean; robustnessTrials?: number} = {},
) {
  const model = buildSparseAffinity(nodes, edges);
  const base = timedLayout(candidate, nodes, edges);
  const relationAuc = actualRelationAucs(model, base.coordinates);
  const recall = shuffledRecallNull(
    model,
    base.coordinates,
    FAILED_ACTUAL_NEIGHBORHOOD_RECALL,
  );
  const independentSignals = independentSignalDistanceOrder(
    model,
    base.coordinates,
    {bootstrap: true},
  );
  const density = densityAffinityEnrichment(model, base.coordinates);
  const specificationIds = model.specificationNodes.map((node) => node.id);
  const integrity = {
    missingSpecifications: specificationIds.filter(
      (id) => !base.coordinates.has(id),
    ).length,
    nonFinite: 0,
    nonzeroZ: 0,
  };
  for (let index = 0; index < base.result.ids.length; index += 1) {
    const x = base.result.positions[index * 3];
    const y = base.result.positions[index * 3 + 1];
    const z = base.result.positions[index * 3 + 2];
    if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) {
      integrity.nonFinite += 1;
    }
    if (z !== 0) integrity.nonzeroZ += 1;
  }

  let highDegree: unknown = {evaluated: false};
  let dropout: unknown = {evaluated: false};
  let performanceResult: unknown = {evaluated: false};
  const perturbationDiagnostics: Diagnostic[] = [];
  if (options.full || (options.robustnessTrials ?? 0) > 0) {
    const ablatedInput = omitHighestDegreeFeatures(nodes, edges);
    const ablated = timedLayout(
      candidate,
      ablatedInput.nodes,
      ablatedInput.edges,
    );
    const highDegreeJaccard = meanNeighborhoodJaccard(
      specificationIds,
      base.coordinates,
      ablated.coordinates,
      20,
      1_000,
      0xa81a7e,
    );
    highDegree = {
      omittedFeatureCount: ablatedInput.omittedFeatureIds.length,
      jaccard: highDegreeJaccard,
      baseAffinityRecall: weightedNeighborhoodRecall(
        model,
        ablated.coordinates,
      ),
      baseDensityEnrichment: densityAffinityEnrichment(
        model,
        ablated.coordinates,
      ),
      elapsedMs: ablated.elapsedMs,
    };
    perturbationDiagnostics.push({
      id: "actual-high-degree-feature-ablation",
      value: highDegree,
      interpretation:
        "Shows which spatial and factual neighborhoods depend on the broadest one percent of view features. Exact geometric order is descriptive only.",
    });

    const dropoutTrials = Array.from(
      {length: options.full ? 10 : (options.robustnessTrials ?? 0)},
      (_, trial) => {
      const perturbed = omitNonSemanticRoutes(nodes, edges, trial);
      const layout = timedLayout(candidate, perturbed.nodes, perturbed.edges);
      return {
        trial,
        jaccard: meanNeighborhoodJaccard(
          specificationIds,
          base.coordinates,
          layout.coordinates,
          20,
          1_000,
          0xd00 + trial,
        ),
        baseAffinityRecall: weightedNeighborhoodRecall(
          model,
          layout.coordinates,
        ),
        baseDensityEnrichment: densityAffinityEnrichment(
          model,
          layout.coordinates,
        ),
        elapsedMs: layout.elapsedMs,
      };
      },
    );
    const meanDropoutJaccard =
      dropoutTrials.reduce((sum, trial) => sum + trial.jaccard, 0) /
      dropoutTrials.length;
    dropout = {meanJaccard: meanDropoutJaccard, trials: dropoutTrials};
    perturbationDiagnostics.push({
      id: "actual-ten-percent-route-dropout",
      value: dropout,
      interpretation:
        "Shows how incomplete non-semantic evidence changes spatial order, factual recall, and density structure.",
    });

    if (options.full) {
      const freshRunTimes = [base.elapsedMs];
      while (freshRunTimes.length < 5) {
        freshRunTimes.push(timedLayout(candidate, nodes, edges).elapsedMs);
      }
      const p95 = percentile(freshRunTimes, 0.95);
      performanceResult = {freshRunTimes, p95};
      perturbationDiagnostics.push({
        id: "actual-worker-p95-runtime",
        value: {
          freshRunTimes,
          p95,
          engineeringLimitMs: 8_000,
          withinLimit: p95 <= 8_000,
        },
        interpretation:
          "Production-feasibility constraint; it does not measure whether specification subsets are visible.",
      });
    }
  }

  const diagnostics: Diagnostic[] = [
    {
      id: "actual-direct-relation-auc",
      value: relationAuc.direct,
      interpretation:
        "How strongly direct persisted semantic or selection relations shorten distance relative to degree-matched unrelated pairs.",
    },
    {
      id: "actual-strongest-factual-quartile-auc",
      value: relationAuc.strongestQuartile,
      interpretation:
        "How strongly the most supported factual affinities shorten distance relative to degree-matched unrelated pairs.",
    },
    {
      id: "actual-weighted-neighborhood-recall",
      value: recall,
      interpretation:
        "Fraction of source-graph affinity recovered by geometric neighborhoods, shown beside the failed layout and shuffled-graph nulls.",
    },
    {
      id: "actual-independent-signal-order",
      value: independentSignals,
      interpretation:
        "Whether distance generally falls as independent supporting signals accumulate.",
    },
    {
      id: "actual-density-affinity-enrichment",
      value: density,
      interpretation:
        "Whether coordinate-derived dense regions contain more source affinity than equal-size spatial permutations.",
    },
    {
      id: "actual-coordinate-integrity",
      value: {
        ...integrity,
        invariantSatisfied:
          integrity.missingSpecifications === 0 &&
          integrity.nonFinite === 0 &&
          integrity.nonzeroZ === 0,
      },
      interpretation: "Required all-Specification finite XY and z=0 invariant.",
    },
    ...perturbationDiagnostics,
  ];
  return {
    candidate: candidate.id,
    mode: options.full ? "full" : "screening",
    diagnostics,
    input: {
      specifications: model.specificationNodes.length,
      affinityEdges: model.edges.length,
      features: model.featureCount,
      routes: model.routeCount,
    },
    performance: {baseLayoutMs: base.elapsedMs, full: performanceResult},
    perturbations: {highDegree, dropout},
  };
}
