import {performance} from "node:perf_hooks";
import {createHash} from "node:crypto";
import {layoutSpecificationGraph} from "../lib/specification-layout";
import {
  deriveSpecificationProximity,
  selectDefaultSpecificationGraph,
  type SpecificationProximityModel,
} from "../lib/specification-proximity";
import type {GraphEdge, GraphNode} from "../lib/types";

const endpoint =
  process.env.GRAPH_ENDPOINT ?? "http://127.0.0.1:3000/api/graph";
// Fifty neighbors are still below one percent of the current corpus. Keeping
// the scale explicit makes the enrichment comparable as the fixture changes.
const neighborCount = Number(process.env.NEIGHBOR_COUNT ?? 50);

type Point = {x: number; y: number};

async function loadGraph() {
  const nodes = new Map<string, GraphNode>();
  const edges = new Map<string, GraphEdge>();
  let pageToken = "";
  do {
    const url = new URL(endpoint);
    url.searchParams.set("pageSize", "1000");
    if (pageToken) url.searchParams.set("pageToken", pageToken);
    const response = await fetch(url);
    if (!response.ok) {
      throw new Error(`${response.status} ${await response.text()}`);
    }
    const page = await response.json();
    for (const node of page.nodes as GraphNode[]) nodes.set(node.id, node);
    for (const edge of page.edges as GraphEdge[]) edges.set(edge.id, edge);
    pageToken = page.nextPageToken;
    process.stderr.write(
      `\rloaded ${nodes.size.toLocaleString()} Nodes / ${edges.size.toLocaleString()} Edges`,
    );
  } while (pageToken);
  process.stderr.write("\n");
  return {nodes: [...nodes.values()], edges: [...edges.values()]};
}

function quantile(sorted: number[], fraction: number) {
  if (sorted.length === 0) return null;
  return sorted[Math.min(sorted.length - 1, Math.floor(fraction * sorted.length))];
}

function distribution(values: number[]) {
  if (values.length === 0) return null;
  const sorted = [...values].sort((left, right) => left - right);
  const mean = values.reduce((sum, value) => sum + value, 0) / values.length;
  const variance =
    values.reduce((sum, value) => sum + Math.pow(value - mean, 2), 0) /
    values.length;
  return {
    min: sorted[0],
    p25: quantile(sorted, 0.25),
    median: quantile(sorted, 0.5),
    p75: quantile(sorted, 0.75),
    max: sorted[sorted.length - 1],
    mean,
    standardDeviation: Math.sqrt(variance),
    coefficientOfVariation: mean > 0 ? Math.sqrt(variance) / mean : 0,
  };
}

function nearest(
  id: string,
  points: Map<string, Point>,
  count: number,
  eligible?: Set<string>,
) {
  const origin = points.get(id);
  if (!origin) return [];
  const candidates: Array<{id: string; distance: number}> = [];
  for (const [candidateId, point] of points) {
    if (candidateId === id || (eligible && !eligible.has(candidateId))) continue;
    const candidate = {
      id: candidateId,
      distance: Math.hypot(point.x - origin.x, point.y - origin.y),
    };
    let insertion = candidates.findIndex(
      (current) => candidate.distance < current.distance,
    );
    if (insertion < 0) insertion = candidates.length;
    if (insertion < count) candidates.splice(insertion, 0, candidate);
    if (candidates.length > count) candidates.pop();
  }
  return candidates;
}

function cohortReport(
  name: string,
  pattern: RegExp,
  specifications: GraphNode[],
  points: Map<string, Point>,
  proximity: SpecificationProximityModel,
  nodesById: Map<string, GraphNode>,
) {
  const cohort = specifications.filter((node) => pattern.test(node.statement));
  const cohortIds = new Set(cohort.map((node) => node.id));
  const expectedShare =
    specifications.length > 1
      ? Math.max(0, cohort.length - 1) / (specifications.length - 1)
      : 0;
  const localShares = cohort.map((node) => {
    const neighbors = nearest(node.id, points, neighborCount);
    return neighbors.length > 0
      ? neighbors.filter((neighbor) => cohortIds.has(neighbor.id)).length /
          neighbors.length
      : 0;
  });
  const observedShare =
    localShares.length > 0
      ? localShares.reduce((sum, value) => sum + value, 0) / localShares.length
      : 0;
  const withinNearestDistances = cohort.flatMap((node) => {
    const match = nearest(node.id, points, 1, cohortIds)[0];
    return match ? [match.distance] : [];
  });
  const featureExplanations = proximity.hyperedges
    .map((feature) => {
      const overlap = feature.members.filter((member) =>
        cohortIds.has(member.specificationId),
      ).length;
      const connectorId = feature.id.replace(
        /^(shared_term|shared_projection):/,
        "",
      );
      return {
        feature:
          nodesById.get(connectorId)?.statement ??
          feature.id.split("\u0001").join(" "),
        signal: feature.signal,
        overlap,
        cohortShare: cohort.length > 0 ? overlap / cohort.length : 0,
        corpusDegree: feature.degree,
      };
    })
    .filter((feature) => feature.overlap >= 2)
    .sort(
      (left, right) =>
        right.cohortShare - left.cohortShare ||
        right.overlap - left.overlap ||
        left.corpusDegree - right.corpusDegree ||
        left.feature.localeCompare(right.feature),
    )
    .slice(0, 12);

  return {
    name,
    matchingSpecifications: cohort.length,
    neighborsPerSpecification: neighborCount,
    observedCohortNeighborShare: observedShare,
    chanceCohortNeighborShare: expectedShare,
    enrichment: expectedShare > 0 ? observedShare / expectedShare : null,
    withinCohortNearestDistance: distribution(withinNearestDistances),
    featureExplanations,
  };
}

async function main() {
  const loaded = await loadGraph();
  const graph = selectDefaultSpecificationGraph(loaded.nodes, loaded.edges);
  const proximity = deriveSpecificationProximity(graph.nodes, graph.edges);
  const nodesById = new Map(graph.nodes.map((node) => [node.id, node]));
  const specifications = graph.nodes.filter(
    (node) => node.nodeKind === "specification",
  );
  const startedAt = performance.now();
  const result = layoutSpecificationGraph(
    graph.nodes.map((node) => ({
      id: node.id,
      nodeKind: node.nodeKind,
      statement: node.statement,
      radius:
        node.nodeKind === "specification"
          ? 4 + Math.min(Math.max(node.supportScore, 0), 24) * 0.24
          : 3,
      visible: node.nodeKind === "specification",
    })),
    graph.edges,
  );
  const elapsedMs = performance.now() - startedAt;
  const coordinateHash = createHash("sha256")
    .update(
      Buffer.from(
        result.positions.buffer,
        result.positions.byteOffset,
        result.positions.byteLength,
      ),
    )
    .digest("hex");
  const points = new Map<string, Point>();
  let nonzeroZ = 0;
  for (let index = 0; index < result.ids.length; index += 1) {
    points.set(result.ids[index], {
      x: result.positions[index * 3],
      y: result.positions[index * 3 + 1],
    });
    if (result.positions[index * 3 + 2] !== 0) nonzeroZ += 1;
  }
  const positionedSpecifications = specifications.filter((node) =>
    points.has(node.id),
  );
  const missingSpecificationIds = specifications
    .filter((node) => !points.has(node.id))
    .map((node) => node.id);

  console.log(
    JSON.stringify(
      {
        input: {
          loadedNodes: loaded.nodes.length,
          loadedEdges: loaded.edges.length,
          defaultLayoutNodes: graph.nodes.length,
          defaultLayoutEdges: graph.edges.length,
          specifications: specifications.length,
        },
        output: {
          positionedNodes: result.ids.length,
          positionedSpecifications: positionedSpecifications.length,
          missingSpecificationIds,
          nonzeroZ,
          proximityFeatures: result.featureCount,
          explanatoryRoutes: result.routeCount,
          iterations: result.iterations,
          elapsedMs,
          coordinateHash,
        },
        cohorts: [
          cohortReport(
            "add specification",
            /(spec add|add (?:a )?specification|add operation|add command)/i,
            specifications,
            points,
            proximity,
            nodesById,
          ),
          cohortReport(
            "graph display",
            /(graph view|graph renderer|graph canvas|graph json|graph subcommand|display(?:s|ing)? (?:the )?(?:specification )?graph)/i,
            specifications,
            points,
            proximity,
            nodesById,
          ),
          cohortReport(
            "reasoning crate",
            /reasoning crate/i,
            specifications,
            points,
            proximity,
            nodesById,
          ),
        ],
      },
      null,
      2,
    ),
  );
}

void main();
