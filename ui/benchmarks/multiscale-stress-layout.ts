import {
  forceCenter,
  forceCollide,
  forceLink,
  forceManyBody,
  forceSimulation,
  forceX,
  forceY,
  type SimulationLinkDatum,
  type SimulationNodeDatum,
} from "d3-force-3d";
import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {buildSparseAffinity, type AffinityEdge} from "./affinity";
import {initialAffinityCoordinates, type ObjectiveSettings} from "./objective-layout";
import {deterministicRandom} from "./random";

type StressNode = SimulationNodeDatum & {
  id: string;
  radius: number;
  ordinal: number;
  x: number;
  y: number;
  anchorX: number;
  anchorY: number;
};

type StressLink = SimulationLinkDatum<StressNode> & {
  edge: AffinityEdge;
  weight: number;
  restDistance: number;
};

type BroadHyperedgeForce = ((alpha: number) => void) & {
  initialize: (_nodes: StressNode[]) => void;
};

const INITIAL_SETTINGS: ObjectiveSettings = {
  epochs: 0,
  learningRate: 0,
  negativeSamples: 0,
  negativeWeight: 0,
  distanceScale: 1,
  semanticBoost: 24,
  selectionBoost: 36,
  positiveTargetBase: 0,
  optimizer: "adam",
};

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function stableUniformCoordinates(
  model: ReturnType<typeof buildSparseAffinity>,
) {
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

function objectiveWeight(
  edge: AffinityEdge,
  affinityExponent = 1.08,
  viewEvidenceScale = 1,
  viewEvidenceExponent = affinityExponent,
) {
  const directScale = edge.selection ? 36 : edge.semantic ? 24 : 1;
  const independentSupport = 1 + Math.log2(Math.max(1, edge.independentSignals));
  const factual = edge.factual || edge.semantic || edge.selection;
  return factual
    ? Math.pow(
        edge.rawWeight * independentSupport * directScale,
        affinityExponent,
      )
    : Math.pow(
        edge.rawWeight * independentSupport * viewEvidenceScale,
        viewEvidenceExponent,
      );
}

function objectiveDistance(edge: AffinityEdge) {
  if (edge.selection) return 8;
  if (edge.semantic) return 10;
  const evidenceScale = Math.log2(Math.max(2, edge.featureDegree));
  const independentCompression =
    1 + 0.18 * Math.max(0, edge.independentSignals - 1);
  return (8 + evidenceScale * 3.2) / independentCompression;
}

function makeBroadHyperedgeForce(
  model: ReturnType<typeof buildSparseAffinity>,
  nodes: StressNode[],
  strength: number,
): BroadHyperedgeForce {
  const hyperedges = model.factualHyperedges.filter(
    (hyperedge) => hyperedge.members.length > 1,
  );
  const force = ((alpha: number) => {
    for (const hyperedge of hyperedges) {
      let centerX = 0;
      let centerY = 0;
      for (const member of hyperedge.members) {
        centerX += nodes[member].x;
        centerY += nodes[member].y;
      }
      centerX /= hyperedge.members.length;
      centerY /= hyperedge.members.length;
      // hyperedge.weight already includes corpus-relative information and
      // inverse-degree incidence normalization. The centroid formulation is
      // the exact quadratic all-member relation, not a sampled pair topology.
      const coefficient = Math.min(
        0.035,
        alpha * strength * hyperedge.weight,
      );
      for (const member of hyperedge.members) {
        const node = nodes[member];
        node.vx = (node.vx ?? 0) + (centerX - node.x) * coefficient;
        node.vy = (node.vy ?? 0) + (centerY - node.y) * coefficient;
      }
    }
  }) as BroadHyperedgeForce;
  force.initialize = () => {};
  return force;
}

export function layoutWithMultiscaleStress(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {
    iterations?: number;
    broadStrength?: number;
    localStrength?: number;
    statementGridAnchorStrength?: number;
    radialStrength?: number;
    broadHyperedgeStrength?: number;
    removeSyntheticBroadPairs?: boolean;
    stableInitialization?: boolean;
    localStrengthCeiling?: number;
    velocityDecay?: number;
    repulsionStrength?: number;
    affinityExponent?: number;
    viewEvidenceScale?: number;
    viewEvidenceExponent?: number;
  } = {},
): SpecificationLayoutResult {
  const iterations = options.iterations ?? 180;
  const model = buildSparseAffinity(nodes, edges, 24, "multiscale", 10);
  const initial = options.stableInitialization
    ? stableUniformCoordinates(model)
    : initialAffinityCoordinates(model, INITIAL_SETTINGS, {
        edgeWeight: (edge) =>
          objectiveWeight(
            edge,
            options.affinityExponent ?? 1.08,
            options.viewEvidenceScale ?? 1,
            options.viewEvidenceExponent ?? options.affinityExponent ?? 1.08,
          ),
        includeFactualHyperedges: false,
      });
  const anchors = new Map<number, {x: number; y: number}>();
  if (options.statementGridAnchorStrength !== undefined) {
    const order = model.specificationNodes
      .map((_, index) => index)
      .sort((left, right) => {
        const statementOrder = model.specificationNodes[
          left
        ].statement.localeCompare(model.specificationNodes[right].statement);
        return (
          statementOrder ||
          model.specificationNodes[left].id.localeCompare(
            model.specificationNodes[right].id,
          )
        );
      });
    const width = Math.max(1, Math.ceil(Math.sqrt(order.length)));
    for (let rank = 0; rank < order.length; rank += 1) {
      const row = Math.floor(rank / width);
      const columnInRow = rank % width;
      const column = row % 2 === 0 ? columnInRow : width - 1 - columnInRow;
      anchors.set(order[rank], {
        x: (column - (width - 1) / 2) * 10,
        y: (row - Math.floor((order.length - 1) / width) / 2) * 10,
      });
    }
  }
  const simulationNodes: StressNode[] = model.specificationNodes.map(
    (node, ordinal) => {
      const anchor = anchors.get(ordinal) ?? {
        x: initial.x[ordinal],
        y: initial.y[ordinal],
      };
      return {
        id: node.id,
        radius: node.radius,
        ordinal,
        anchorX: anchor.x,
        anchorY: anchor.y,
        x: anchor.x,
        y: anchor.y,
        z: 0,
      };
    },
  );
  const objectiveEdges = model.edges.filter(
    (edge) =>
      (options.removeSyntheticBroadPairs !== true || !edge.broadFactual) &&
      objectiveWeight(
        edge,
        options.affinityExponent ?? 1.08,
        options.viewEvidenceScale ?? 1,
        options.viewEvidenceExponent ?? options.affinityExponent ?? 1.08,
      ) > 0,
  );
  const simulationLinks: StressLink[] = objectiveEdges.map((edge) => ({
    source: simulationNodes[edge.source],
    target: simulationNodes[edge.target],
    edge,
    weight: objectiveWeight(
      edge,
      options.affinityExponent ?? 1.08,
      options.viewEvidenceScale ?? 1,
      options.viewEvidenceExponent ?? options.affinityExponent ?? 1.08,
    ),
    restDistance: objectiveDistance(edge),
  }));
  const link = forceLink<StressNode, StressLink>(simulationLinks)
    .id((node) => node.id)
    .distance((value) => value.restDistance)
    .strength((value) => {
      if (value.weight <= 0) return 0;
      const scale = value.edge.broadFactual
        ? (options.broadStrength ?? 0.025)
        : (options.localStrength ?? 0.22);
      const ceiling = value.edge.broadFactual
        ? 0.3
        : (options.localStrengthCeiling ?? 1);
      return Math.max(
        0.0001,
        Math.min(ceiling, Math.log1p(value.weight) * scale),
      );
    });
  const random = deterministicRandom(0x5eec7a55);
  const simulation = forceSimulation(simulationNodes, 2)
    .randomSource(random.next)
    .alpha(1)
    .alphaMin(0.001)
    .alphaDecay(1 - Math.pow(0.001, 1 / iterations))
    .velocityDecay(options.velocityDecay ?? 0.28)
    .force("links", link)
    .force(
      "repulsion",
      forceManyBody<StressNode>()
        .strength(options.repulsionStrength ?? -28)
        .distanceMin(2)
        .distanceMax(2_000)
        .theta(0.9),
    )
    .force(
      "collision",
      forceCollide<StressNode>()
        .radius((node) => node.radius * 1.08 + 1)
        .strength(0.7),
    )
    .force(
      "broad-factual-hyperedges",
      makeBroadHyperedgeForce(
        model,
        simulationNodes,
        options.broadHyperedgeStrength ?? 0,
      ),
    )
    .force("center", forceCenter<StressNode>(0, 0, 0).strength(0.015))
    .force(
      "bounded-x",
      forceX<StressNode>(0).strength(options.radialStrength ?? 0),
    )
    .force(
      "bounded-y",
      forceY<StressNode>(0).strength(options.radialStrength ?? 0),
    );
  if (options.statementGridAnchorStrength !== undefined) {
    simulation
      .force(
        "anchor-x",
        forceX<StressNode>((node) => node.anchorX).strength(
          options.statementGridAnchorStrength,
        ),
      )
      .force(
        "anchor-y",
        forceY<StressNode>((node) => node.anchorY).strength(
          options.statementGridAnchorStrength,
        ),
      );
  }
  simulation.stop();
  simulation.tick(iterations);

  const specificationCoordinates = new Map(
    simulationNodes.map((node) => [node.id, {x: node.x, y: node.y}]),
  );
  const incident = new Map<string, string[]>();
  for (const edge of edges) {
    const sourceSpecification = model.specificationIndex.has(edge.source);
    const targetSpecification = model.specificationIndex.has(edge.target);
    if (sourceSpecification === targetSpecification) continue;
    const connector = sourceSpecification ? edge.target : edge.source;
    const specification = sourceSpecification ? edge.source : edge.target;
    const values = incident.get(connector) ?? [];
    values.push(specification);
    incident.set(connector, values);
  }
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const direct = specificationCoordinates.get(nodes[index].id);
    const members = incident.get(nodes[index].id) ?? [];
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
    positions[index * 3] = point.x;
    positions[index * 3 + 1] = point.y;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: nodes.map((node) => node.id),
    positions,
    featureCount: model.featureCount,
    routeCount: model.routeCount,
    iterations,
  };
}
