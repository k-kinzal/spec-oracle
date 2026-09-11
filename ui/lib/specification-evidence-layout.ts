import {
  forceCenter,
  forceCollide,
  forceManyBody,
  forceSimulation,
  forceX,
  forceY,
  type Simulation,
  type SimulationLinkDatum,
  type SimulationNodeDatum,
} from "d3-force-3d";
import {
  buildSparseAffinity,
  type AffinityEdge,
  type SparseAffinityModel,
} from "./specification-affinity";
import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "./specification-layout";

type EvidenceNode = SimulationNodeDatum & {
  id: string;
  radius: number;
  x: number;
  y: number;
};

type EvidenceLink = SimulationLinkDatum<EvidenceNode> & {
  edge: AffinityEdge;
  weight: number;
  normalizedWeight: number;
  confidence: number;
  restDistance: number;
  strength: number;
  bias: number;
};

type BroadHyperedgeForce = ((alpha: number) => void) & {
  initialize: (nodes: EvidenceNode[]) => void;
  update: (model: SparseAffinityModel) => void;
};

type RobustLinkForce = ((alpha: number) => void) & {
  initialize: (_nodes: EvidenceNode[]) => void;
  update: (links: EvidenceLink[]) => void;
};

const ITERATIONS = 80;
const AFFINITY_EXPONENT = 1.8;
const VIEW_EVIDENCE_SCALE = 1;
const VIEW_EVIDENCE_EXPONENT = 3;
const LOCAL_STRENGTH = 0.35;
const LOCAL_STRENGTH_CEILING = 0.6;
const VIEW_CONCENTRATION_STRENGTH = 18;
const ROBUST_LOSS_SCALE = 30;
const BROAD_HYPEREDGE_STRENGTH = 0.12;
const REPULSION_STRENGTH = -50;
const RADIAL_STRENGTH = 0.0008;
const APPEND_ALPHA = 0.16;

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function stableUniformCoordinates(model: SparseAffinityModel) {
  const population = model.specificationNodes.length;
  const x = new Float64Array(population);
  const y = new Float64Array(population);
  const order = Array.from({length: population}, (_, index) => index).sort(
    (left, right) =>
      stableHash(`uniform\u0000${model.specificationNodes[left].id}`) -
      stableHash(`uniform\u0000${model.specificationNodes[right].id}`),
  );
  const goldenAngle = Math.PI * (3 - Math.sqrt(5));
  const radiusScale = Math.sqrt(Math.max(1, population)) * 5;
  for (let rank = 0; rank < order.length; rank += 1) {
    const radius =
      Math.sqrt((rank + 0.5) / Math.max(1, population)) * radiusScale;
    const angle = rank * goldenAngle;
    x[order[rank]] = Math.cos(angle) * radius;
    y[order[rank]] = Math.sin(angle) * radius;
  }
  return {x, y};
}

function evidenceWeight(edge: AffinityEdge) {
  const directScale = edge.selection ? 36 : edge.semantic ? 24 : 1;
  const independentSupport =
    1 + Math.log2(Math.max(1, edge.independentSignals));
  const factual = edge.factual || edge.semantic || edge.selection;
  if (factual) {
    return Math.pow(
      edge.rawWeight * independentSupport * directScale,
      AFFINITY_EXPONENT,
    );
  }
  // A single common word is too weak to shape the graph. Repeated, independent
  // local vocabulary is still evidence when persisted relationships have not
  // yet caught up, so its contribution rises nonlinearly instead of being
  // treated as either a hard edge or no edge at all.
  return Math.pow(
    edge.rawWeight * independentSupport * VIEW_EVIDENCE_SCALE,
    VIEW_EVIDENCE_EXPONENT,
  );
}

function evidenceDistance(edge: AffinityEdge) {
  if (edge.selection) return 8;
  if (edge.semantic) return 10;
  const evidenceScale = Math.log2(Math.max(2, edge.featureDegree));
  const independentSupport =
    1 + Math.log2(Math.max(1, edge.independentSignals));
  const independentCompression =
    1 + 1.4 * Math.log1p(edge.rawWeight * independentSupport);
  return (8 + evidenceScale * 3.2) / independentCompression;
}

function evidenceConfidence(edge: AffinityEdge) {
  const directScale = edge.selection ? 36 : edge.semantic ? 24 : 1;
  const independentSupport =
    1 + Math.log2(Math.max(1, edge.independentSignals));
  return (
    1 - Math.exp(-4 * edge.rawWeight * independentSupport * directScale)
  );
}

function evidenceLinkStrength(link: EvidenceLink) {
  if (link.edge.factual || link.edge.semantic || link.edge.selection) {
    return Math.min(
      LOCAL_STRENGTH_CEILING,
      Math.log1p(link.weight) * LOCAL_STRENGTH,
    );
  }
  const concentration = link.normalizedWeight * link.normalizedWeight;
  return Math.min(
    LOCAL_STRENGTH_CEILING,
    concentration *
      link.confidence *
      LOCAL_STRENGTH *
      VIEW_CONCENTRATION_STRENGTH,
  );
}

/**
 * Gradient of a log-cosh finite-rest loss. It is quadratic close to the rest
 * distance, while the pull of a long cross-cutting relation is bounded. This
 * lets dense local evidence settle without allowing one weak bridge to drag
 * whole neighborhoods through each other.
 */
function robustEvidenceLinkForce(
  initialLinks: EvidenceLink[] = [],
): RobustLinkForce {
  let links = initialLinks;
  const force = ((alpha: number) => {
    for (const link of links) {
      const source = link.source as EvidenceNode;
      const target = link.target as EvidenceNode;
      const dx = target.x + (target.vx ?? 0) - source.x - (source.vx ?? 0);
      const dy = target.y + (target.vy ?? 0) - source.y - (source.vy ?? 0);
      const distance = Math.max(1e-6, Math.hypot(dx, dy));
      const scale = Math.max(1, link.restDistance);
      const residual = distance - link.restDistance;
      const gradient =
        scale * ROBUST_LOSS_SCALE * Math.tanh(residual / scale);
      const magnitude =
        (alpha * link.strength * gradient) / distance;
      const x = dx * magnitude;
      const y = dy * magnitude;
      target.vx = (target.vx ?? 0) - x * link.bias;
      target.vy = (target.vy ?? 0) - y * link.bias;
      source.vx = (source.vx ?? 0) + x * (1 - link.bias);
      source.vy = (source.vy ?? 0) + y * (1 - link.bias);
    }
  }) as RobustLinkForce;
  force.initialize = () => {};
  force.update = (nextLinks) => {
    links = nextLinks;
  };
  return force;
}

function broadHyperedgeForce(): BroadHyperedgeForce {
  let nodes: EvidenceNode[] = [];
  let hyperedges: SparseAffinityModel["factualHyperedges"] = [];
  const force = ((alpha: number) => {
    for (const hyperedge of hyperedges) {
      if (hyperedge.members.length < 2) continue;
      let centerX = 0;
      let centerY = 0;
      for (const member of hyperedge.members) {
        centerX += nodes[member].x;
        centerY += nodes[member].y;
      }
      centerX /= hyperedge.members.length;
      centerY /= hyperedge.members.length;
      const coefficient = Math.min(
        0.035,
        alpha * BROAD_HYPEREDGE_STRENGTH * hyperedge.weight,
      );
      for (const member of hyperedge.members) {
        const node = nodes[member];
        node.vx = (node.vx ?? 0) + (centerX - node.x) * coefficient;
        node.vy = (node.vy ?? 0) + (centerY - node.y) * coefficient;
      }
    }
  }) as BroadHyperedgeForce;
  force.initialize = (nextNodes) => {
    nodes = nextNodes;
  };
  force.update = (model) => {
    hyperedges = model.factualHyperedges;
  };
  return force;
}

function deterministicRandom(seed: number) {
  let state = seed >>> 0;
  return () => {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    return state / 4294967296;
  };
}

export type SpecificationEvidenceSimulation = {
  simulation: Simulation<EvidenceNode>;
  simulationNodes: EvidenceNode[];
  model: SparseAffinityModel;
  inputNodes: SpecificationLayoutInputNode[];
  inputEdges: SpecificationLayoutInputEdge[];
  inputNodeIds: Set<string>;
  inputEdgeIds: Set<string>;
  nodeById: Map<string, EvidenceNode>;
  linkForce: RobustLinkForce;
  hyperedgeForce: BroadHyperedgeForce;
  objectiveUpdates: number;
};

export type SpecificationEvidenceUpdate = {
  changed: boolean;
  addedSpecifications: number;
  objectiveUpdate: number;
};

function buildEvidenceLinks(
  model: SparseAffinityModel,
  simulationNodes: EvidenceNode[],
) {
  const weightedDegree = new Float64Array(simulationNodes.length);
  const weightedEdges = model.edges.flatMap((edge) => {
    const weight = evidenceWeight(edge);
    if (weight <= 0 || edge.broadFactual) return [];
    weightedDegree[edge.source] += weight;
    weightedDegree[edge.target] += weight;
    return [{edge, weight}];
  });
  const simulationLinks: EvidenceLink[] = weightedEdges.flatMap(
    ({edge, weight}) => {
      const normalization = Math.sqrt(
        weightedDegree[edge.source] * weightedDegree[edge.target],
      );
      if (normalization <= 0) return [];
      return [
        {
          source: simulationNodes[edge.source],
          target: simulationNodes[edge.target],
          edge,
          weight,
          normalizedWeight: weight / normalization,
          confidence: evidenceConfidence(edge),
          restDistance: evidenceDistance(edge),
          strength: 0,
          bias: 0.5,
        },
      ];
    },
  );
  const linkCounts = new Uint32Array(simulationNodes.length);
  for (const link of simulationLinks) {
    linkCounts[link.edge.source] += 1;
    linkCounts[link.edge.target] += 1;
  }
  for (const link of simulationLinks) {
    const total = linkCounts[link.edge.source] + linkCounts[link.edge.target];
    link.bias = total > 0 ? linkCounts[link.edge.source] / total : 0.5;
    link.strength = evidenceLinkStrength(link);
  }
  return simulationLinks;
}

/**
 * Create the one long-lived production simulation. The Worker keeps this
 * instance from the first append through the last; accumulated evidence is
 * updated in place by updateSpecificationEvidenceSimulation.
 */
export function createSpecificationEvidenceSimulation(
  nodes: SpecificationLayoutInputNode[] = [],
  edges: SpecificationLayoutInputEdge[] = [],
): SpecificationEvidenceSimulation {
  const model = buildSparseAffinity([], [], 12, "multiscale", 6);
  const simulationNodes: EvidenceNode[] = [];
  const linkForce = robustEvidenceLinkForce();
  const hyperedgeForce = broadHyperedgeForce();
  const simulation = forceSimulation<EvidenceNode>(simulationNodes, 2)
    .randomSource(deterministicRandom(0x5eec7a55))
    .alpha(1)
    .alphaMin(0.001)
    .alphaDecay(1 - Math.pow(0.001, 1 / ITERATIONS))
    .velocityDecay(0.6)
    .force("evidence-links", linkForce)
    .force("broad-factual-hyperedges", hyperedgeForce)
    .force(
      "repulsion",
      forceManyBody<EvidenceNode>()
        .strength(REPULSION_STRENGTH)
        .distanceMin(2)
        .distanceMax(2_000)
        .theta(0.9),
    )
    .force(
      "collision",
      forceCollide<EvidenceNode>()
        .radius((node) => node.radius * 1.08 + 1)
        .strength(0.7),
    )
    .force("center", forceCenter<EvidenceNode>(0, 0, 0).strength(0.015))
    .force("bounded-x", forceX<EvidenceNode>(0).strength(RADIAL_STRENGTH))
    .force("bounded-y", forceY<EvidenceNode>(0).strength(RADIAL_STRENGTH))
    .stop();

  const state: SpecificationEvidenceSimulation = {
    simulation,
    simulationNodes,
    model,
    inputNodes: [],
    inputEdges: [],
    inputNodeIds: new Set(),
    inputEdgeIds: new Set(),
    nodeById: new Map(),
    linkForce,
    hyperedgeForce,
    objectiveUpdates: 0,
  };
  updateSpecificationEvidenceSimulation(state, nodes, edges);
  return state;
}

/**
 * Append graph facts to the existing objective without replacing its
 * simulation or any existing simulation Node. Rebuilding the sparse evidence
 * weights is an in-place force update: x/y, velocity, alpha and elapsed
 * simulation history remain intact.
 */
export function updateSpecificationEvidenceSimulation(
  state: SpecificationEvidenceSimulation,
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
): SpecificationEvidenceUpdate {
  let changed = false;
  for (const node of nodes) {
    if (state.inputNodeIds.has(node.id)) continue;
    state.inputNodeIds.add(node.id);
    state.inputNodes.push(node);
    changed = true;
  }
  for (const edge of edges) {
    if (state.inputEdgeIds.has(edge.id)) continue;
    state.inputEdgeIds.add(edge.id);
    state.inputEdges.push(edge);
    changed = true;
  }
  if (!changed) {
    return {
      changed: false,
      addedSpecifications: 0,
      objectiveUpdate: state.objectiveUpdates,
    };
  }

  const model = buildSparseAffinity(
    state.inputNodes,
    state.inputEdges,
    12,
    "multiscale",
    6,
  );
  const initial = stableUniformCoordinates(model);
  let addedSpecifications = 0;
  for (let index = 0; index < model.specificationNodes.length; index += 1) {
    const input = model.specificationNodes[index];
    if (state.nodeById.has(input.id)) continue;
    const node: EvidenceNode = {
      id: input.id,
      radius: input.radius,
      x: initial.x[index],
      y: initial.y[index],
      z: 0,
      vx: 0,
      vy: 0,
      vz: 0,
    };
    state.nodeById.set(input.id, node);
    state.simulationNodes.push(node);
    addedSpecifications += 1;
  }

  // Specification input is append-only, so model indices and simulation Node
  // indices remain identical. Existing objects carry their position and
  // velocity through simulation.nodes(...); D3 only reinitializes bound forces.
  if (
    state.simulationNodes.some(
      (node, index) => model.specificationNodes[index]?.id !== node.id,
    )
  ) {
    throw new Error("Specification evidence input ceased to be append-only");
  }

  state.model = model;
  state.linkForce.update(buildEvidenceLinks(model, state.simulationNodes));
  state.hyperedgeForce.update(model);
  if (addedSpecifications > 0) {
    state.simulation.nodes(state.simulationNodes);
  }
  state.objectiveUpdates += 1;
  return {
    changed: true,
    addedSpecifications,
    objectiveUpdate: state.objectiveUpdates,
  };
}

/** Restart the same simulation after a real append, with only a small reheat. */
export function resumeSpecificationEvidenceSimulation(
  state: SpecificationEvidenceSimulation,
) {
  const alpha =
    state.objectiveUpdates === 1
      ? 1
      : Math.max(state.simulation.alpha(), APPEND_ALPHA);
  state.simulation.alpha(alpha).restart();
  return alpha;
}

export function readSpecificationEvidenceSimulation(
  state: SpecificationEvidenceSimulation,
  iterations: number,
  visibleOnly = false,
): SpecificationLayoutResult {
  const {simulationNodes, model, inputNodes: nodes, inputEdges: edges} = state;
  const specificationCoordinates = new Map(
    simulationNodes.map((node) => [node.id, {x: node.x, y: node.y}]),
  );
  const outputNodes = visibleOnly ? nodes.filter((node) => node.visible) : nodes;
  const needsConnectorCoordinates = outputNodes.some(
    (node) => node.nodeKind !== "specification",
  );
  const incident = new Map<string, string[]>();
  if (needsConnectorCoordinates) {
    for (const edge of edges) {
      const sourceSpecification = model.specificationIndex.has(edge.source);
      const targetSpecification = model.specificationIndex.has(edge.target);
      if (sourceSpecification === targetSpecification) continue;
      const connector = sourceSpecification ? edge.target : edge.source;
      const specification = sourceSpecification ? edge.source : edge.target;
      const members = incident.get(connector) ?? [];
      members.push(specification);
      incident.set(connector, members);
    }
  }
  const positions = new Float32Array(outputNodes.length * 3);
  for (let index = 0; index < outputNodes.length; index += 1) {
    const direct = specificationCoordinates.get(outputNodes[index].id);
    const members = incident.get(outputNodes[index].id) ?? [];
    const point =
      direct ??
      (members.length > 0
        ? {
            x:
              members.reduce(
                (sum, id) => sum + (specificationCoordinates.get(id)?.x ?? 0),
                0,
              ) / members.length,
            y:
              members.reduce(
                (sum, id) => sum + (specificationCoordinates.get(id)?.y ?? 0),
                0,
              ) / members.length,
          }
        : {x: 0, y: 0});
    positions[index * 3] = Number.isFinite(point.x) ? point.x : 0;
    positions[index * 3 + 1] = Number.isFinite(point.y) ? point.y : 0;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: outputNodes.map((node) => node.id),
    positions,
    featureCount: model.featureCount,
    routeCount: model.routeCount,
    iterations,
  };
}

/**
 * The synchronous form used by tests and offline diagnostics. Production uses
 * the same state and forces incrementally in the Worker as Nodes arrive.
 */
export function layoutSpecificationEvidenceGraph(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
): SpecificationLayoutResult {
  const state = createSpecificationEvidenceSimulation(nodes, edges);
  state.simulation.tick(ITERATIONS);
  return readSpecificationEvidenceSimulation(state, ITERATIONS);
}
