import {UndirectedGraph} from "graphology";
import forceAtlas2 from "graphology-layout-forceatlas2";
import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {buildSparseAffinity} from "./affinity";
import {initialAffinityCoordinates, type ObjectiveSettings} from "./objective-layout";

export function layoutWithForceAtlas2(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {
    linLogMode?: boolean;
    iterations?: number;
    scalingRatio?: number;
    semanticBoost?: number;
    selectionBoost?: number;
    slowDown?: number;
    gravity?: number;
    includeFactualHyperedges?: boolean;
    broadFactualBoost?: number;
    strongGravityMode?: boolean;
    edgeWeightInfluence?: number;
    neighborBudget?: number;
    exactFactualBoost?: number;
    broadDegreeExponent?: number;
    multiscaleRetention?: boolean;
    strongestReserve?: number;
    localAffinityBoost?: number;
    stableInitialization?: boolean | "statement-grid" | "uniform-grid";
    scaffoldWeight?: number;
  } = {},
): SpecificationLayoutResult {
  const model = buildSparseAffinity(
    nodes,
    edges,
    options.neighborBudget ?? 32,
    options.multiscaleRetention ? "multiscale" : "strongest",
    options.strongestReserve ?? 4,
  );
  const graph = new UndirectedGraph();
  const initialSettings: ObjectiveSettings = {
    epochs: 0,
    learningRate: 0,
    negativeSamples: 0,
    negativeWeight: 0,
    distanceScale: 1,
    semanticBoost: 12,
    selectionBoost: 16,
    positiveTargetBase: 0,
    optimizer: "adam",
  };
  const edgeWeight = (edge: (typeof model.edges)[number]) =>
    Math.pow(
      edge.rawWeight *
        (edge.broadFactual ? (options.broadFactualBoost ?? 1) : 1) *
        (edge.broadFactual
          ? Math.pow(
              edge.broadDegree,
              Math.min(0.5, Math.max(0, options.broadDegreeExponent ?? 0)),
            )
          : 1) *
        (!edge.broadFactual ? (options.localAffinityBoost ?? 1) : 1) *
        (edge.factual && !edge.broadFactual
          ? (options.exactFactualBoost ?? 1)
          : 1) *
        (edge.selection
          ? (options.selectionBoost ?? 16)
          : edge.semantic
            ? (options.semanticBoost ?? 12)
            : 1),
      options.edgeWeightInfluence ?? 1,
    );
  const initial = initialAffinityCoordinates(model, initialSettings, {
    edgeWeight,
    includeFactualHyperedges: options.includeFactualHyperedges !== false,
  });
  let scaffoldOrder: number[] | undefined;
  let scaffoldWidth = 0;
  if (options.stableInitialization) {
    const order = model.specificationNodes
      .map((_, index) => index)
      .sort((left, right) => {
        if (options.stableInitialization === "statement-grid") {
          const statementOrder = model.specificationNodes[
            left
          ].statement.localeCompare(model.specificationNodes[right].statement);
          if (statementOrder !== 0) return statementOrder;
        }
        if (options.stableInitialization === "uniform-grid") {
          const leftHash = stableNodeHash(
            `uniform-grid\u0000${model.specificationNodes[left].id}`,
          );
          const rightHash = stableNodeHash(
            `uniform-grid\u0000${model.specificationNodes[right].id}`,
          );
          if (leftHash !== rightHash) return leftHash - rightHash;
        }
        return model.specificationNodes[left].id.localeCompare(
          model.specificationNodes[right].id,
        );
      });
    const width = Math.max(1, Math.ceil(Math.sqrt(order.length)));
    if (
      options.stableInitialization === "uniform-grid" ||
      (options.stableInitialization === "statement-grid" &&
        (options.scaffoldWeight ?? 0) > 0)
    ) {
      scaffoldOrder = order;
      scaffoldWidth = width;
    }
    const goldenAngle = Math.PI * (3 - Math.sqrt(5));
    for (let rank = 0; rank < order.length; rank += 1) {
      const index = order[rank];
      if (
        options.stableInitialization === "statement-grid" ||
        options.stableInitialization === "uniform-grid"
      ) {
        const row = Math.floor(rank / width);
        const columnInRow = rank % width;
        const column = row % 2 === 0 ? columnInRow : width - 1 - columnInRow;
        initial.x[index] = (column - (width - 1) / 2) * 10;
        initial.y[index] =
          (row - Math.floor((order.length - 1) / width) / 2) * 10;
        continue;
      }
      const radius =
        Math.sqrt((rank + 0.5) / Math.max(1, order.length)) *
        Math.max(30, Math.sqrt(order.length) * 4);
      const angle = rank * goldenAngle;
      initial.x[index] = Math.cos(angle) * radius;
      initial.y[index] = Math.sin(angle) * radius;
    }
  }
  for (let nodeIndex = 0; nodeIndex < model.specificationNodes.length; nodeIndex += 1) {
    const node = model.specificationNodes[nodeIndex];
    graph.addNode(node.id, {
      x: initial.x[nodeIndex],
      y: initial.y[nodeIndex],
      size: node.radius,
    });
  }
  if (options.includeFactualHyperedges !== false) {
    model.factualHyperedges.forEach((hyperedge, hyperedgeIndex) => {
    const id = `__factual-hyperedge-${hyperedgeIndex}`;
    let x = 0;
    let y = 0;
    for (const member of hyperedge.members) {
      const attributes = graph.getNodeAttributes(
        model.specificationNodes[member].id,
      );
      x += attributes.x;
      y += attributes.y;
    }
    graph.addNode(id, {
      x: x / hyperedge.members.length,
      y: y / hyperedge.members.length,
      size: 0,
    });
    for (const member of hyperedge.members) {
      graph.addUndirectedEdgeWithKey(
        `factual-hyperedge-${hyperedgeIndex}-${member}`,
        id,
        model.specificationNodes[member].id,
        {weight: Math.max(10, hyperedge.weight * 1_000)},
      );
    }
    });
  }
  if (scaffoldOrder && (options.scaffoldWeight ?? 0) > 0) {
    const rankByCell = scaffoldOrder;
    const offsets = [
      [1, 0],
      [0, 1],
      [1, 1],
      [-1, 1],
    ] as const;
    for (let rank = 0; rank < rankByCell.length; rank += 1) {
      const row = Math.floor(rank / scaffoldWidth);
      const column = rank % scaffoldWidth;
      for (const [dx, dy] of offsets) {
        const otherColumn = column + dx;
        const otherRow = row + dy;
        if (
          otherColumn < 0 ||
          otherColumn >= scaffoldWidth ||
          otherRow < 0
        ) {
          continue;
        }
        const otherRank = otherRow * scaffoldWidth + otherColumn;
        if (otherRank >= rankByCell.length) continue;
        graph.addUndirectedEdgeWithKey(
          `stable-scaffold-${rank}-${otherRank}`,
          model.specificationNodes[rankByCell[rank]].id,
          model.specificationNodes[rankByCell[otherRank]].id,
          {weight: options.scaffoldWeight},
        );
      }
    }
  }
  model.edges.forEach((edge, index) => {
    const source = model.specificationNodes[edge.source].id;
    const target = model.specificationNodes[edge.target].id;
    const weight =
      edge.rawWeight *
      (edge.broadFactual ? (options.broadFactualBoost ?? 1) : 1) *
      (edge.broadFactual
        ? Math.pow(
            edge.broadDegree,
            Math.min(0.5, Math.max(0, options.broadDegreeExponent ?? 0)),
          )
        : 1) *
      (!edge.broadFactual ? (options.localAffinityBoost ?? 1) : 1) *
      (edge.factual && !edge.broadFactual
        ? (options.exactFactualBoost ?? 1)
        : 1) *
      (edge.selection
        ? (options.selectionBoost ?? 16)
        : edge.semantic
          ? (options.semanticBoost ?? 12)
          : 1);
    const existing = graph.edge(source, target);
    if (existing !== undefined) {
      graph.setEdgeAttribute(
        existing,
        "weight",
        (graph.getEdgeAttribute(existing, "weight") as number) + weight,
      );
    } else {
      graph.addUndirectedEdgeWithKey(`affinity-${index}`, source, target, {
        weight,
      });
    }
  });
  const optimized = forceAtlas2(graph, {
    iterations: options.iterations ?? 1_000,
    getEdgeWeight: "weight",
    settings: {
      linLogMode: options.linLogMode ?? true,
      outboundAttractionDistribution: false,
      edgeWeightInfluence: options.edgeWeightInfluence ?? 1,
      scalingRatio: options.scalingRatio ?? 10,
      gravity: options.gravity ?? 0.05,
      strongGravityMode: options.strongGravityMode ?? true,
      slowDown: options.slowDown ?? 6,
      barnesHutOptimize: model.specificationNodes.length > 1_000,
      barnesHutTheta: 0.5,
      adjustSizes: false,
    },
  });
  const specificationCoordinates = new Map<string, {x: number; y: number}>();
  for (const node of model.specificationNodes) {
    specificationCoordinates.set(node.id, optimized[node.id] ?? {x: 0, y: 0});
  }
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
    iterations: options.iterations ?? 1_000,
  };
}

function stableNodeHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}
