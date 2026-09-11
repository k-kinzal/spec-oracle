import {
  forceCenter,
  forceLink,
  forceSimulation,
  forceX,
  forceY,
  type SimulationLinkDatum,
  type SimulationNodeDatum,
} from "d3-force-3d";
import type {GraphEdge, GraphNode} from "@/lib/types";
import {
  deriveSpecificationProximity,
  type SpecificationProximityModel,
  type ProximityHyperedge,
  type ProximitySignal,
} from "@/lib/specification-proximity";

export type SpecificationLayoutInputNode = {
  id: string;
  nodeKind: GraphNode["nodeKind"];
  statement: string;
  radius: number;
  visible: boolean;
  /** Evaluation-only masks for view-derived features; production leaves empty. */
  excludedViewFeatureIds?: readonly string[];
};

export type SpecificationLayoutInputEdge = Pick<
  GraphEdge,
  "id" | "source" | "target" | "current" | "family"
>;

export type SpecificationLayoutResult = {
  ids: string[];
  positions: Float32Array;
  featureCount: number;
  routeCount: number;
  iterations: number;
};

type LayoutNode = SimulationNodeDatum & SpecificationLayoutInputNode & {
  x: number;
  y: number;
  z: number;
  degree: number;
  ordinal: number;
};

type LayoutLink = SimulationLinkDatum<LayoutNode> & {
  id: string;
  signal: ProximitySignal;
  weight: number;
  distance: number;
};

type BoundHyperedge = {
  signal: ProximityHyperedge["signal"];
  members: Array<{node: LayoutNode; weight: number}>;
};

type HyperedgeForce = ((alpha: number) => void) & {
  initialize: (_nodes: LayoutNode[]) => void;
};

type NodeForce = ((alpha: number) => void) & {
  initialize: (nodes: LayoutNode[]) => void;
};

function stableHash(value: string): number {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function pairIndex(left: number, right: number, population: number) {
  return left < right
    ? left * population + right
    : right * population + left;
}

function initialPosition(id: string, spread: number): {x: number; y: number} {
  const hash = stableHash(id);
  const angle = ((hash % 65536) / 65536) * Math.PI * 2;
  const radius =
    spread * 0.16 +
    Math.sqrt(((hash >>> 16) % 65536) / 65536) * spread * 0.84;
  return {x: Math.cos(angle) * radius, y: Math.sin(angle) * radius};
}

type SpectralRoute = {members: number[]; weight: number};

function normalizeVector(vector: Float64Array, active: number[]) {
  let norm = 0;
  for (const index of active) norm += vector[index] * vector[index];
  norm = Math.sqrt(norm);
  if (norm <= 1e-12) return false;
  for (const index of active) vector[index] /= norm;
  return true;
}

function removeBasis(
  vector: Float64Array,
  active: number[],
  basis: Float64Array[],
) {
  for (const direction of basis) {
    let projection = 0;
    for (const index of active) projection += vector[index] * direction[index];
    for (const index of active) vector[index] -= projection * direction[index];
  }
}

/**
 * Solve the two strongest non-constant axes of the normalized proximity
 * hypergraph. This is a deterministic, relation-derived initialization of the
 * same Node-level force objective, not a partition or a displayed first stage.
 */
function spectralSpecificationPositions(
  inputNodes: SpecificationLayoutInputNode[],
  proximity: SpecificationProximityModel,
  fallbackSpread: number,
) {
  const specifications = inputNodes.filter(
    (node) => node.nodeKind === "specification",
  );
  const specificationIndex = new Map(
    specifications.map((node, index) => [node.id, index]),
  );
  const routes: SpectralRoute[] = [];

  for (const hyperedge of proximity.hyperedges) {
    const members = hyperedge.members.flatMap((member) => {
      const index = specificationIndex.get(member.specificationId);
      return index === undefined ? [] : [index];
    });
    if (members.length < 2) continue;
    const weight =
      hyperedge.members.reduce((sum, member) => sum + member.weight, 0) /
      hyperedge.members.length;
    if (weight > 0) routes.push({members, weight});
  }
  for (const link of proximity.links) {
    if (link.signal !== "semantic" && link.signal !== "selection") continue;
    const source = specificationIndex.get(link.source);
    const target = specificationIndex.get(link.target);
    if (source === undefined || target === undefined || source === target) continue;
    routes.push({members: [source, target], weight: link.weight});
  }

  const degree = new Float64Array(specifications.length);
  for (const route of routes) {
    for (const index of route.members) degree[index] += route.weight;
  }
  const active = Array.from({length: specifications.length}, (_, index) => index)
    .filter((index) => degree[index] > 1e-12);
  const result = new Map<string, {x: number; y: number}>();
  if (active.length < 3 || routes.length === 0) {
    for (const specification of specifications) {
      result.set(
        specification.id,
        initialPosition(specification.id, fallbackSpread),
      );
    }
    return result;
  }

  const inverseSqrtDegree = new Float64Array(specifications.length);
  const constant = new Float64Array(specifications.length);
  let totalDegree = 0;
  for (const index of active) totalDegree += degree[index];
  for (const index of active) {
    inverseSqrtDegree[index] = 1 / Math.sqrt(degree[index]);
    constant[index] = Math.sqrt(degree[index] / totalDegree);
  }

  const multiply = (vector: Float64Array) => {
    const output = new Float64Array(specifications.length);
    for (const route of routes) {
      let mean = 0;
      for (const index of route.members) {
        mean += vector[index] * inverseSqrtDegree[index];
      }
      mean = (mean / route.members.length) * route.weight;
      for (const index of route.members) {
        output[index] += mean * inverseSqrtDegree[index];
      }
    }
    return output;
  };

  const solveAxis = (channel: string, previous: Float64Array[]) => {
    let vector = new Float64Array(specifications.length);
    for (const index of active) {
      vector[index] =
        ((stableHash(`${channel}\u0000${specifications[index].id}`) % 1048576) /
          524288) -
        1;
    }
    const basis = [constant, ...previous];
    removeBasis(vector, active, basis);
    normalizeVector(vector, active);
    for (let iteration = 0; iteration < 72; iteration += 1) {
      const next = multiply(vector);
      removeBasis(next, active, basis);
      if (!normalizeVector(next, active)) break;
      vector = next;
    }
    return vector;
  };

  const xAxis = solveAxis("x", []);
  const yAxis = solveAxis("y", [xAxis]);
  const activeScale = Math.sqrt(active.length);
  const coordinateScale = Math.max(150, Math.sqrt(active.length) * 3.2);
  for (let index = 0; index < specifications.length; index += 1) {
    if (degree[index] <= 1e-12) {
      result.set(
        specifications[index].id,
        initialPosition(specifications[index].id, fallbackSpread),
      );
      continue;
    }
    result.set(specifications[index].id, {
      x:
        Math.max(-4, Math.min(4, xAxis[index] * activeScale)) *
        coordinateScale,
      y:
        Math.max(-4, Math.min(4, yAxis[index] * activeScale)) *
        coordinateScale,
    });
  }
  return result;
}

function makeHyperedgeForce(hyperedges: BoundHyperedge[]): HyperedgeForce {
  const force = ((alpha: number) => {
    for (const hyperedge of hyperedges) {
      let x = 0;
      let y = 0;
      let totalWeight = 0;
      for (const member of hyperedge.members) {
        x += member.node.x * member.weight;
        y += member.node.y * member.weight;
        totalWeight += member.weight;
      }
      if (totalWeight <= 0) continue;
      x /= totalWeight;
      y /= totalWeight;
      const averageWeight = totalWeight / hyperedge.members.length;
      const signalScale =
        hyperedge.signal === "lexical_bigram"
          ? 1.25
          : hyperedge.signal === "lexical_unigram"
            ? 0.5
            : hyperedge.signal === "shared_projection"
              ? 0.8
              : 0.65;
      const strength =
        Math.min(0.09, Math.pow(averageWeight, 1.1) * 0.1) * signalScale;
      for (const member of hyperedge.members) {
        member.node.vx =
          (member.node.vx ?? 0) + (x - member.node.x) * strength * alpha;
        member.node.vy =
          (member.node.vy ?? 0) + (y - member.node.y) * strength * alpha;
      }
    }
  }) as HyperedgeForce;
  force.initialize = () => {};
  return force;
}

function deriveLocalPairAffinity(
  proximity: SpecificationProximityModel,
  specificationCount: number,
  nodeOrdinal: ReadonlyMap<string, number>,
  nodeCount: number,
) {
  const affinity = new Map<number, number>();
  const add = (left: string, right: string, weight: number) => {
    if (left === right || weight <= 0) return;
    const leftOrdinal = nodeOrdinal.get(left);
    const rightOrdinal = nodeOrdinal.get(right);
    if (leftOrdinal === undefined || rightOrdinal === undefined) return;
    const key = pairIndex(leftOrdinal, rightOrdinal, nodeCount);
    affinity.set(key, (affinity.get(key) ?? 0) + weight);
  };

  for (const link of proximity.links) {
    if (link.signal !== "semantic" && link.signal !== "selection") continue;
    add(link.source, link.target, link.weight);
  }
  for (const hyperedge of proximity.hyperedges) {
    // Expanding only features whose one-mode pair count is below the
    // Specification population keeps the operation sparse by construction.
    // Broader features remain centroid forces and never become pair affinity.
    if (hyperedge.degree * hyperedge.degree > specificationCount) continue;
    for (let left = 0; left < hyperedge.members.length; left += 1) {
      for (let right = left + 1; right < hyperedge.members.length; right += 1) {
        add(
          hyperedge.members[left].specificationId,
          hyperedge.members[right].specificationId,
          Math.min(
            hyperedge.members[left].weight,
            hyperedge.members[right].weight,
          ),
        );
      }
    }
  }
  return affinity;
}

/**
 * Deterministic local repulsion and collision for visible Specifications.
 * A uniform XY index avoids rebuilding a global octree containing thousands
 * of invisible connector Nodes on every convergence tick.
 */
function makeVisibleSeparationForce(
  localPairAffinity: ReadonlyMap<number, number>,
  nodeCount: number,
): NodeForce {
  let visible: LayoutNode[] = [];
  const interactionRange = 32;
  const cellSize = interactionRange;
  const force = ((alpha: number) => {
    const cells = new Map<string, LayoutNode[]>();
    for (const node of visible) {
      const cellX = Math.floor(node.x / cellSize);
      const cellY = Math.floor(node.y / cellSize);
      const key = `${cellX}:${cellY}`;
      const cell = cells.get(key) ?? [];
      cell.push(node);
      cells.set(key, cell);
    }

    for (const node of visible) {
      const cellX = Math.floor(node.x / cellSize);
      const cellY = Math.floor(node.y / cellSize);
      for (let offsetX = -1; offsetX <= 1; offsetX += 1) {
        for (let offsetY = -1; offsetY <= 1; offsetY += 1) {
          const neighbors = cells.get(`${cellX + offsetX}:${cellY + offsetY}`);
          if (!neighbors) continue;
          for (const other of neighbors) {
            if ((other.index ?? 0) <= (node.index ?? 0)) continue;
            let dx = node.x - other.x;
            let dy = node.y - other.y;
            let distance = Math.hypot(dx, dy);
            if (distance >= interactionRange) continue;
            if (distance < 0.0001) {
              const angle =
                ((stableHash(`${node.id}\u0000${other.id}`) % 65536) / 65536) *
                Math.PI *
                2;
              dx = Math.cos(angle);
              dy = Math.sin(angle);
              distance = 1;
            }
            const minimumDistance =
              ((node.radius + other.radius) * 1.28 + 1.4) *
              Math.max(
                0.48,
                1 /
                  Math.sqrt(
                    1 +
                      (localPairAffinity.get(
                        pairIndex(node.ordinal, other.ordinal, nodeCount),
                      ) ?? 0) *
                        0.9,
                  ),
              );
            const overlap = Math.max(0, minimumDistance - distance);
            const impulse =
              alpha * 0.9 * (1 - distance / interactionRange) +
              overlap * 0.32;
            const x = (dx / distance) * impulse;
            const y = (dy / distance) * impulse;
            node.vx = (node.vx ?? 0) + x;
            node.vy = (node.vy ?? 0) + y;
            other.vx = (other.vx ?? 0) - x;
            other.vy = (other.vy ?? 0) - y;
          }
        }
      }
    }
  }) as NodeForce;
  force.initialize = (nodes) => {
    visible = nodes.filter((node) => node.visible);
  };
  return force;
}

/**
 * The complete default layout algorithm: all input Nodes and real Edges become
 * one deterministic XY coordinate result. There is no provisional layout,
 * partition, upper graph, or post-layout correction.
 */
export function layoutSpecificationGraph(
  inputNodes: SpecificationLayoutInputNode[],
  inputEdges: SpecificationLayoutInputEdge[],
  iterations = 132,
): SpecificationLayoutResult {
  const visibleCount = inputNodes.filter((node) => node.visible).length;
  const nodeOrdinal = new Map(
    inputNodes.map((node, index) => [node.id, index]),
  );
  const initialSpread = Math.max(220, Math.sqrt(Math.max(1, visibleCount)) * 10);
  const proximity = deriveSpecificationProximity(
    inputNodes.map((node) => ({
      id: node.id,
      nodeKind: node.nodeKind,
      statement: node.statement,
      excludedViewFeatureIds: node.excludedViewFeatureIds,
    })),
    inputEdges,
  );
  const specificationPositions = spectralSpecificationPositions(
    inputNodes,
    proximity,
    initialSpread,
  );
  const localPairAffinity = deriveLocalPairAffinity(
    proximity,
    inputNodes.filter((node) => node.nodeKind === "specification").length,
    nodeOrdinal,
    inputNodes.length,
  );
  const incidentSpecificationPositions = new Map<
    string,
    Array<{x: number; y: number}>
  >();
  for (const route of proximity.links) {
    const sourcePosition = specificationPositions.get(route.source);
    const targetPosition = specificationPositions.get(route.target);
    if (sourcePosition && !targetPosition) {
      const incident = incidentSpecificationPositions.get(route.target) ?? [];
      incident.push(sourcePosition);
      incidentSpecificationPositions.set(route.target, incident);
    }
    if (targetPosition && !sourcePosition) {
      const incident = incidentSpecificationPositions.get(route.source) ?? [];
      incident.push(targetPosition);
      incidentSpecificationPositions.set(route.source, incident);
    }
  }
  const nodes: LayoutNode[] = inputNodes.map((input, ordinal) => {
    const incident = incidentSpecificationPositions.get(input.id) ?? [];
    const fallback = initialPosition(input.id, initialSpread);
    const connectorOffset = initialPosition(input.id, 8);
    const position =
      specificationPositions.get(input.id) ??
      (incident.length > 0
        ? {
            x:
              incident.reduce((sum, value) => sum + value.x, 0) /
                incident.length +
              connectorOffset.x,
            y:
              incident.reduce((sum, value) => sum + value.y, 0) /
                incident.length +
              connectorOffset.y,
          }
        : fallback);
    return {
      ...input,
      x: position.x,
      y: position.y,
      z: 0,
      vx: 0,
      vy: 0,
      vz: 0,
      degree: 0,
      ordinal,
    };
  });
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const links: LayoutLink[] = [];
  for (const route of proximity.links) {
    const source = nodeById.get(route.source);
    const target = nodeById.get(route.target);
    if (!source || !target) continue;
    source.degree += 1;
    target.degree += 1;
    links.push({...route});
  }
  const boundHyperedges: BoundHyperedge[] = [];
  for (const hyperedge of proximity.hyperedges) {
    const members = hyperedge.members.flatMap((member) => {
      const node = nodeById.get(member.specificationId);
      if (!node) return [];
      node.degree += 1;
      return [{node, weight: member.weight}];
    });
    if (members.length >= 2) {
      boundHyperedges.push({signal: hyperedge.signal, members});
    }
  }

  const linkForce = forceLink<LayoutNode, LayoutLink>(links)
    .id((node) => node.id)
    .distance((link) => link.distance)
    .strength((link) =>
      link.signal === "selection"
        ? 1.05
        : link.signal === "semantic"
          ? 0.9
          : Math.min(0.32, link.weight * 0.12),
    );
  const simulation = forceSimulation<LayoutNode>(nodes, 2)
    .stop()
    .alphaMin(0.001)
    .alphaDecay(0.052)
    .velocityDecay(0.4)
    .force("links", linkForce)
    .force("lexical-proximity", makeHyperedgeForce(boundHyperedges))
    .force(
      "visible-separation",
      makeVisibleSeparationForce(localPairAffinity, inputNodes.length),
    )
    .force("center", forceCenter<LayoutNode>(0, 0, 0).strength(0.024))
    .force("x", forceX<LayoutNode>(0).strength(0.001))
    .force("y", forceY<LayoutNode>(0).strength(0.001));

  simulation.tick(iterations);
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    positions[index * 3] = Number.isFinite(nodes[index].x) ? nodes[index].x : 0;
    positions[index * 3 + 1] = Number.isFinite(nodes[index].y) ? nodes[index].y : 0;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: nodes.map((node) => node.id),
    positions,
    featureCount: proximity.featureCount,
    routeCount: proximity.routeCount,
    iterations,
  };
}
