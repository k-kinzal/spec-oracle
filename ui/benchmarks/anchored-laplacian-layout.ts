import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {buildSparseAffinity} from "./affinity";
import {layoutWithFeatureProjection} from "./feature-projection-layout";

export function layoutWithAnchoredLaplacian(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {
    anchorWeight?: number;
    iterations?: number;
    neighborBudget?: number;
    strongestReserve?: number;
    anchorMode?: "statement-grid" | "stable-hash" | "feature-projection";
    localBoost?: number;
    broadBoost?: number;
    semanticBoost?: number;
    selectionBoost?: number;
  } = {},
): SpecificationLayoutResult {
  const anchorWeight = options.anchorWeight ?? 1;
  const iterations = options.iterations ?? 180;
  const model = buildSparseAffinity(
    nodes,
    edges,
    options.neighborBudget ?? 32,
    "stable-multiscale",
    options.strongestReserve ?? 16,
  );
  const count = model.specificationNodes.length;
  const anchorX = new Float64Array(count);
  const anchorY = new Float64Array(count);
  const order = model.specificationNodes
    .map((_, index) => index)
    .sort((left, right) => {
      const statementOrder = model.specificationNodes[left].statement.localeCompare(
        model.specificationNodes[right].statement,
      );
      return (
        statementOrder ||
        model.specificationNodes[left].id.localeCompare(
          model.specificationNodes[right].id,
        )
      );
    });
  if ((options.anchorMode ?? "statement-grid") === "feature-projection") {
    const projection = layoutWithFeatureProjection(nodes, edges, {
      degreeExponent: 0.5,
      informationExponent: 0.5,
    });
    const projectionIndex = new Map(
      projection.ids.map((id, index) => [id, index]),
    );
    for (let index = 0; index < count; index += 1) {
      const projected = projectionIndex.get(model.specificationNodes[index].id);
      if (projected === undefined) continue;
      anchorX[index] = projection.positions[projected * 3];
      anchorY[index] = projection.positions[projected * 3 + 1];
    }
  } else if ((options.anchorMode ?? "statement-grid") === "stable-hash") {
    const hash = (value: string) => {
      let result = 2166136261;
      for (let index = 0; index < value.length; index += 1) {
        result ^= value.charCodeAt(index);
        result = Math.imul(result, 16777619);
      }
      return result >>> 0;
    };
    const stableOrder = Array.from({length: count}, (_, index) => index).sort(
      (left, right) =>
        hash(`anchor-rank\u0000${model.specificationNodes[left].id}`) -
          hash(`anchor-rank\u0000${model.specificationNodes[right].id}`) ||
        model.specificationNodes[left].id.localeCompare(
          model.specificationNodes[right].id,
        ),
    );
    const radius = Math.max(10, Math.sqrt(Math.max(1, count)) * 5);
    const goldenAngle = Math.PI * (3 - Math.sqrt(5));
    for (let rank = 0; rank < stableOrder.length; rank += 1) {
      const index = stableOrder[rank];
      const pointRadius =
        Math.sqrt((rank + 0.5) / Math.max(1, count)) * radius;
      const angle = rank * goldenAngle;
      anchorX[index] = Math.cos(angle) * pointRadius;
      anchorY[index] = Math.sin(angle) * pointRadius;
    }
  } else {
    const width = Math.max(1, Math.ceil(Math.sqrt(count)));
    for (let rank = 0; rank < order.length; rank += 1) {
      const row = Math.floor(rank / width);
      const columnInRow = rank % width;
      const column = row % 2 === 0 ? columnInRow : width - 1 - columnInRow;
      const index = order[rank];
      anchorX[index] = (column - (width - 1) / 2) * 10;
      anchorY[index] =
        (row - Math.floor((order.length - 1) / width) / 2) * 10;
    }
  }
  let x = anchorX.slice();
  let y = anchorY.slice();
  const incident = Array.from(
    {length: count},
    () => [] as Array<{target: number; weight: number}>,
  );
  for (const edge of model.edges) {
    const broad =
      edge.broadRawWeight *
      Math.sqrt(Math.max(1, edge.broadDegree)) *
      (options.broadBoost ?? 1);
    const local = edge.localWeight * (options.localBoost ?? 1);
    const direct = edge.selection
      ? (options.selectionBoost ?? 8)
      : edge.semantic
        ? (options.semanticBoost ?? 6)
        : 1;
    const weight = Math.max(1e-6, (local + broad) * direct);
    incident[edge.source].push({target: edge.target, weight});
    incident[edge.target].push({target: edge.source, weight});
  }
  for (let iteration = 0; iteration < iterations; iteration += 1) {
    const nextX = new Float64Array(count);
    const nextY = new Float64Array(count);
    for (let index = 0; index < count; index += 1) {
      let totalWeight = anchorWeight;
      let weightedX = anchorWeight * anchorX[index];
      let weightedY = anchorWeight * anchorY[index];
      for (const relation of incident[index]) {
        totalWeight += relation.weight;
        weightedX += relation.weight * x[relation.target];
        weightedY += relation.weight * y[relation.target];
      }
      nextX[index] = weightedX / totalWeight;
      nextY[index] = weightedY / totalWeight;
    }
    x = nextX;
    y = nextY;
  }

  const connectorMembers = new Map<string, number[]>();
  for (const edge of edges) {
    const source = model.specificationIndex.get(edge.source);
    const target = model.specificationIndex.get(edge.target);
    if (source !== undefined && target === undefined) {
      const values = connectorMembers.get(edge.target) ?? [];
      values.push(source);
      connectorMembers.set(edge.target, values);
    } else if (target !== undefined && source === undefined) {
      const values = connectorMembers.get(edge.source) ?? [];
      values.push(target);
      connectorMembers.set(edge.source, values);
    }
  }
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const specification = model.specificationIndex.get(nodes[index].id);
    const members = connectorMembers.get(nodes[index].id) ?? [];
    const point =
      specification !== undefined
        ? {x: x[specification], y: y[specification]}
        : members.length > 0
          ? {
              x: members.reduce((sum, member) => sum + x[member], 0) / members.length,
              y: members.reduce((sum, member) => sum + y[member], 0) / members.length,
            }
          : {x: 0, y: 0};
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
