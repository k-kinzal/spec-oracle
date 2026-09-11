import {runActualGraphSuite} from "../benchmarks/actual-suite";
import {performance} from "node:perf_hooks";
import {layoutCandidates} from "../benchmarks/candidates";
import {buildSparseAffinity, type SparseAffinityModel} from "../benchmarks/affinity";
import {diagnoseSpatialLandscape} from "../benchmarks/landscape-diagnostics";
import {resultCoordinates} from "../benchmarks/types";
import {
  omitHighestDegreeFeatures,
  omitNonSemanticRoutes,
} from "../benchmarks/perturbations";
import {selectDefaultSpecificationGraph} from "../lib/specification-proximity";
import {deriveSpecificationProximity} from "../lib/specification-proximity";
import type {GraphEdge, GraphNode} from "../lib/types";

const endpoint = process.env.GRAPH_ENDPOINT ?? "http://127.0.0.1:3000/api/graph";

function argument(name: string) {
  const prefix = `--${name}=`;
  return process.argv.find((value) => value.startsWith(prefix))?.slice(prefix.length);
}

async function loadGraph() {
  const nodes = new Map<string, GraphNode>();
  const edges = new Map<string, GraphEdge>();
  let pageToken = "";
  do {
    const url = new URL(endpoint);
    url.searchParams.set("pageSize", "1000");
    if (pageToken) url.searchParams.set("pageToken", pageToken);
    const response = await fetch(url);
    if (!response.ok) throw new Error(`${response.status} ${await response.text()}`);
    const page = await response.json();
    for (const node of page.nodes as GraphNode[]) nodes.set(node.id, node);
    for (const edge of page.edges as GraphEdge[]) edges.set(edge.id, edge);
    pageToken = page.nextPageToken;
  } while (pageToken);
  return {nodes: [...nodes.values()], edges: [...edges.values()]};
}

async function main() {
const candidateId = argument("candidate") ?? "failed-baseline";
const candidate = layoutCandidates.get(candidateId);
if (!candidate) throw new Error(`Unknown candidate ${candidateId}`);
const loaded = await loadGraph();
const graph = selectDefaultSpecificationGraph(loaded.nodes, loaded.edges);
const inputNodes = graph.nodes.map((node) => ({
  id: node.id,
  nodeKind: node.nodeKind,
  statement: node.statement,
  radius:
    node.nodeKind === "specification"
      ? 4 + Math.min(Math.max(node.supportScore, 0), 24) * 0.24
      : 3,
  visible: node.nodeKind === "specification",
}));
if (process.argv.includes("--affinity-profile")) {
  const model = buildSparseAffinity(inputNodes, graph.edges);
  const proximity = deriveSpecificationProximity(inputNodes, graph.edges);
  const quantiles = (values: readonly number[]) => {
    const sorted = [...values].sort((left, right) => left - right);
    const at = (fraction: number) =>
      sorted[
        Math.min(
          sorted.length - 1,
          Math.max(0, Math.floor(fraction * Math.max(0, sorted.length - 1))),
        )
      ] ?? 0;
    return {
      minimum: at(0),
      p25: at(0.25),
      median: at(0.5),
      p75: at(0.75),
      p90: at(0.9),
      p99: at(0.99),
      maximum: at(1),
    };
  };
  const visited = new Uint8Array(model.specificationNodes.length);
  const componentSizes: number[] = [];
  for (let start = 0; start < visited.length; start += 1) {
    if (visited[start]) continue;
    const stack = [start];
    visited[start] = 1;
    let size = 0;
    while (stack.length > 0) {
      const current = stack.pop();
      if (current === undefined) break;
      size += 1;
      for (const neighbor of model.adjacency[current]) {
        if (visited[neighbor]) continue;
        visited[neighbor] = 1;
        stack.push(neighbor);
      }
    }
    componentSizes.push(size);
  }
  const featureDegreeBySignal = Object.fromEntries(
    [...new Set(proximity.hyperedges.map((feature) => feature.signal))].map(
      (signal) => {
        const degrees = proximity.hyperedges
          .filter((feature) => feature.signal === signal)
          .map((feature) => feature.degree);
        return [signal, {count: degrees.length, degree: quantiles(degrees)}];
      },
    ),
  );
  const factualDegree = new Uint32Array(model.specificationNodes.length);
  const factualParent = Int32Array.from(
    {length: model.specificationNodes.length},
    (_, index) => index,
  );
  const factualFind = (value: number) => {
    let root = value;
    while (factualParent[root] !== root) root = factualParent[root];
    while (factualParent[value] !== value) {
      const next = factualParent[value];
      factualParent[value] = root;
      value = next;
    }
    return root;
  };
  const factualUnion = (left: number, right: number) => {
    const leftRoot = factualFind(left);
    const rightRoot = factualFind(right);
    if (leftRoot !== rightRoot) factualParent[rightRoot] = leftRoot;
  };
  for (const edge of model.edges) {
    if (!edge.factual && !edge.semantic && !edge.selection) continue;
    factualDegree[edge.source] += 1;
    factualDegree[edge.target] += 1;
    factualUnion(edge.source, edge.target);
  }
  for (const hyperedge of model.factualHyperedges) {
    for (const member of hyperedge.members) {
      factualDegree[member] += 1;
      factualUnion(hyperedge.members[0], member);
    }
  }
  const factualComponentSizes = new Map<number, number>();
  for (let index = 0; index < factualParent.length; index += 1) {
    const root = factualFind(index);
    factualComponentSizes.set(root, (factualComponentSizes.get(root) ?? 0) + 1);
  }
  console.log(
    JSON.stringify(
      {
        specifications: model.specificationNodes.length,
        affinityEdges: model.edges.length,
        candidatePairsBeforeSparsification: model.candidatePairCount,
        affinityDegree: quantiles(model.adjacency.map((neighbors) => neighbors.size)),
        factualDegree: {
          distribution: quantiles([...factualDegree]),
          specificationsWithoutFactualAffinity: [...factualDegree].filter(
            (degree) => degree === 0,
          ).length,
          components: {
            count: factualComponentSizes.size,
            sizes: quantiles([...factualComponentSizes.values()]),
            largest: [...factualComponentSizes.values()]
              .sort((left, right) => right - left)
              .slice(0, 20),
          },
        },
        independentSignals: quantiles(
          model.edges.map((edge) => edge.independentSignals),
        ),
        affinityWeight: {
          raw: quantiles(model.edges.map((edge) => edge.rawWeight)),
          localRaw: quantiles(model.edges.map((edge) => edge.localRawWeight)),
          broadRaw: quantiles(model.edges.map((edge) => edge.broadRawWeight)),
          normalized: quantiles(model.edges.map((edge) => edge.weight)),
          featureDegree: quantiles(model.edges.map((edge) => edge.featureDegree)),
        },
        edgeKinds: {
          semantic: model.edges.filter((edge) => edge.semantic).length,
          selection: model.edges.filter((edge) => edge.selection).length,
          factual: model.edges.filter((edge) => edge.factual).length,
          broadFactual: model.edges.filter((edge) => edge.broadFactual).length,
        },
        components: {
          count: componentSizes.length,
          sizes: quantiles(componentSizes),
          largest: [...componentSizes].sort((left, right) => right - left).slice(0, 20),
        },
        featureDegreeBySignal,
      },
      null,
      2,
    ),
  );
  return;
}
if (process.argv.includes("--affinity-stability")) {
  const rankedNeighbors = (model: SparseAffinityModel, count = 20) => {
    const incident = Array.from({length: model.specificationNodes.length}, () =>
      [] as Array<{target: number; weight: number}>,
    );
    for (const edge of model.edges) {
      incident[edge.source].push({target: edge.target, weight: edge.rawWeight});
      incident[edge.target].push({target: edge.source, weight: edge.rawWeight});
    }
    return new Map(
      model.specificationNodes.map((node, index) => [
        node.id,
        new Set(
          incident[index]
            .sort(
              (left, right) =>
                right.weight - left.weight || left.target - right.target,
            )
            .slice(0, count)
            .map((value) => model.specificationNodes[value.target].id),
        ),
      ]),
    );
  };
  const compare = (
    left: ReturnType<typeof rankedNeighbors>,
    right: ReturnType<typeof rankedNeighbors>,
  ) => {
    const ids = [...left.keys()];
    const sampled = Array.from(
      {length: Math.min(1_000, ids.length)},
      (_, index) => ids[Math.floor((index * ids.length) / Math.min(1_000, ids.length))],
    );
    return (
      sampled.reduce((sum, id) => {
        const leftSet = left.get(id) ?? new Set<string>();
        const rightSet = right.get(id) ?? new Set<string>();
        let intersection = 0;
        for (const value of leftSet) if (rightSet.has(value)) intersection += 1;
        const union = leftSet.size + rightSet.size - intersection;
        return sum + (union > 0 ? intersection / union : 1);
      }, 0) / sampled.length
    );
  };
  const analyze = (
    baseNodes: Parameters<typeof buildSparseAffinity>[0],
    baseEdges: Parameters<typeof buildSparseAffinity>[1],
    changed: {
      nodes: Parameters<typeof buildSparseAffinity>[0];
      edges: Parameters<typeof buildSparseAffinity>[1];
    },
    retention: "strongest" | "multiscale",
    reserve: number,
  ) => {
    const baseModel = buildSparseAffinity(baseNodes, baseEdges, 32, retention, reserve);
    const changedModel = buildSparseAffinity(
      changed.nodes,
      changed.edges,
      32,
      retention,
      reserve,
    );
    return compare(rankedNeighbors(baseModel), rankedNeighbors(changedModel));
  };
  const highDegree = omitHighestDegreeFeatures(inputNodes, graph.edges);
  const dropout = omitNonSemanticRoutes(inputNodes, graph.edges, 0);
  const rankedFeatures = deriveSpecificationProximity(inputNodes, graph.edges)
    .hyperedges.sort(
      (left, right) => right.degree - left.degree || left.id.localeCompare(right.id),
    );
  const omittedCount = Math.max(1, Math.ceil(rankedFeatures.length * 0.01));
  const omittedFeatures = rankedFeatures.slice(0, omittedCount);
  console.log(
    JSON.stringify(
      {
        strongest: {
          highDegree: analyze(inputNodes, graph.edges, highDegree, "strongest", 4),
          dropout: analyze(inputNodes, graph.edges, dropout, "strongest", 4),
        },
        multiscale: {
          highDegree: analyze(inputNodes, graph.edges, highDegree, "multiscale", 16),
          dropout: analyze(inputNodes, graph.edges, dropout, "multiscale", 16),
        },
        omittedFeatureDegrees: {
          count: omittedFeatures.length,
          minimum: omittedFeatures.at(-1)?.degree,
          median: omittedFeatures[Math.floor(omittedFeatures.length / 2)]?.degree,
          maximum: omittedFeatures[0]?.degree,
          bySignal: Object.fromEntries(
            [...new Set(omittedFeatures.map((feature) => feature.signal))].map(
              (signal) => [
                signal,
                omittedFeatures.filter((feature) => feature.signal === signal).length,
              ],
            ),
          ),
        },
      },
      null,
      2,
    ),
  );
  return;
}
if (process.argv.includes("--landscape")) {
  const model = buildSparseAffinity(inputNodes, graph.edges);
  const proximity = deriveSpecificationProximity(inputNodes, graph.edges);
  const nodesById = new Map(graph.nodes.map((node) => [node.id, node]));
  const started = performance.now();
  const result = candidate.layout(inputNodes, graph.edges);
  const coordinates = resultCoordinates(result);
  const requestedScale = Number(argument("scale"));
  const scales = Number.isFinite(requestedScale) && requestedScale > 0
    ? [requestedScale]
    : [10, 20, 40];
  console.log(
    JSON.stringify(
      {
        candidate: candidate.id,
        layoutMs: performance.now() - started,
        landscape: diagnoseSpatialLandscape(
          model,
          proximity,
          coordinates,
          nodesById,
          scales,
        ),
      },
      null,
      2,
    ),
  );
  return;
}
if (process.argv.includes("--outliers")) {
  const model = buildSparseAffinity(inputNodes, graph.edges);
  const started = performance.now();
  const result = candidate.layout(inputNodes, graph.edges);
  const coordinates = resultCoordinates(result);
  const radii = model.specificationNodes
    .map((node, index) => {
      const point = coordinates.get(node.id) ?? {x: 0, y: 0};
      return {
        id: node.id,
        statement: node.statement,
        affinityDegree: model.adjacency[index].size,
        x: point.x,
        y: point.y,
        radius: Math.hypot(point.x, point.y),
      };
    })
    .sort((left, right) => right.radius - left.radius);
  console.log(
    JSON.stringify(
      {
        candidate: candidate.id,
        layoutMs: performance.now() - started,
        radius: {
          p50: radii[Math.floor(radii.length * 0.5)]?.radius,
          p90: radii[Math.floor(radii.length * 0.1)]?.radius,
          p99: radii[Math.floor(radii.length * 0.01)]?.radius,
          maximum: radii[0]?.radius,
        },
        farthest: radii.slice(0, 20),
      },
      null,
      2,
    ),
  );
  return;
}
if (process.argv.includes("--layout-only")) {
  const started = performance.now();
  const result = candidate.layout(inputNodes, graph.edges);
  console.log(JSON.stringify({
    candidate: candidate.id,
    specifications: inputNodes.filter((node) => node.nodeKind === "specification").length,
    positioned: result.ids.length,
    layoutMs: performance.now() - started,
  }, null, 2));
  return;
}
const report = runActualGraphSuite(candidate, inputNodes, graph.edges, {
  full: process.argv.includes("--full"),
  robustnessTrials: process.argv.includes("--robustness-smoke") ? 1 : 0,
});
console.log(JSON.stringify({...report, loaded: {
  nodes: loaded.nodes.length,
  edges: loaded.edges.length,
  layoutNodes: graph.nodes.length,
}}, null, 2));
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
