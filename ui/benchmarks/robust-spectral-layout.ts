import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {
  buildSparseAffinity,
  type AffinityEdge,
  type SparseAffinityModel,
} from "./affinity";
import {
  initialAffinityCoordinates,
  type ObjectiveSettings,
} from "./objective-layout";

function pairKey(source: number, target: number, population: number) {
  return source < target
    ? source * population + target
    : target * population + source;
}

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function edgeStrength(edge: AffinityEdge) {
  const broad = edge.broadRawWeight * Math.sqrt(Math.max(1, edge.broadDegree));
  const direct = edge.selection ? 6 : edge.semantic ? 4 : 1;
  return Math.max(1e-9, (edge.localWeight + 1.25 * broad) * direct);
}

function diffuseAffinity(
  base: SparseAffinityModel,
  options: {neighborBudget: number; directWeight: number},
): SparseAffinityModel {
  const population = base.specificationNodes.length;
  const incident = Array.from(
    {length: population},
    () => [] as Array<{target: number; weight: number; edge: AffinityEdge}>,
  );
  const directByPair = new Map<number, AffinityEdge>();
  for (const edge of base.edges) {
    const weight = edgeStrength(edge);
    incident[edge.source].push({target: edge.target, weight, edge});
    incident[edge.target].push({target: edge.source, weight, edge});
    directByPair.set(pairKey(edge.source, edge.target, population), edge);
  }

  const nominated = new Map<number, number>();
  for (let source = 0; source < population; source += 1) {
    const scores = new Map<number, number>();
    for (const direct of incident[source]) {
      scores.set(
        direct.target,
        (scores.get(direct.target) ?? 0) + options.directWeight * direct.weight,
      );
      const normalization = Math.max(
        1,
        Math.log2(2 + incident[direct.target].length),
      );
      for (const second of incident[direct.target]) {
        if (second.target === source) continue;
        const contribution =
          Math.min(direct.weight, second.weight) / normalization;
        scores.set(
          second.target,
          (scores.get(second.target) ?? 0) + contribution,
        );
      }
    }
    const selected = [...scores]
      .sort(
        ([left, leftScore], [right, rightScore]) =>
          rightScore - leftScore ||
          stableHash(
            `${base.specificationNodes[source].id}\u0000${base.specificationNodes[left].id}`,
          ) -
            stableHash(
              `${base.specificationNodes[source].id}\u0000${base.specificationNodes[right].id}`,
            ),
      )
      .slice(0, options.neighborBudget);
    for (const [target, score] of selected) {
      const key = pairKey(source, target, population);
      nominated.set(key, Math.max(nominated.get(key) ?? 0, score));
    }
  }

  const maximum = new Float64Array(population);
  for (const [key, score] of nominated) {
    const source = Math.floor(key / population);
    const target = key - source * population;
    maximum[source] = Math.max(maximum[source], score);
    maximum[target] = Math.max(maximum[target], score);
  }
  const robustEdges: AffinityEdge[] = [...nominated]
    .sort(([left], [right]) => left - right)
    .map(([key, score]) => {
      const source = Math.floor(key / population);
      const target = key - source * population;
      const direct = directByPair.get(key);
      const normalized = Math.min(
        1,
        score /
          Math.max(1e-9, Math.sqrt(maximum[source] * maximum[target])),
      );
      return {
        source,
        target,
        weight: normalized,
        rawWeight: score,
        localRawWeight: score,
        broadRawWeight: 0,
        localWeight: normalized,
        independentSignals: direct?.independentSignals ?? 1,
        semantic: direct?.semantic ?? false,
        selection: direct?.selection ?? false,
        broadFactual: false,
        factual: direct?.factual ?? false,
        broadDegree: 1,
        featureDegree: direct?.featureDegree ?? 1,
      };
    });
  const adjacency = Array.from({length: population}, () => new Set<number>());
  for (const edge of robustEdges) {
    adjacency[edge.source].add(edge.target);
    adjacency[edge.target].add(edge.source);
  }
  return {
    ...base,
    edges: robustEdges,
    adjacency,
    factualHyperedges: [],
  };
}

const SPECTRAL_SETTINGS: ObjectiveSettings = {
  epochs: 0,
  learningRate: 0,
  negativeSamples: 0,
  negativeWeight: 0,
  distanceScale: 1,
  semanticBoost: 4,
  selectionBoost: 6,
  positiveTargetBase: 0,
  optimizer: "adam",
};

export function layoutWithRobustSpectral(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {neighborBudget?: number; directWeight?: number} = {},
): SpecificationLayoutResult {
  const base = buildSparseAffinity(nodes, edges, 32, "stable-multiscale", 16);
  const model = diffuseAffinity(base, {
    neighborBudget: options.neighborBudget ?? 48,
    directWeight: options.directWeight ?? 2,
  });
  const coordinates = initialAffinityCoordinates(model, SPECTRAL_SETTINGS, {
    edgeWeight: (edge) => edge.weight,
    includeFactualHyperedges: false,
  });
  const connectorMembers = new Map<string, number[]>();
  for (const edge of edges) {
    const source = model.specificationIndex.get(edge.source);
    const target = model.specificationIndex.get(edge.target);
    if (source !== undefined && target === undefined) {
      const members = connectorMembers.get(edge.target) ?? [];
      members.push(source);
      connectorMembers.set(edge.target, members);
    } else if (target !== undefined && source === undefined) {
      const members = connectorMembers.get(edge.source) ?? [];
      members.push(target);
      connectorMembers.set(edge.source, members);
    }
  }
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const specification = model.specificationIndex.get(nodes[index].id);
    const members = connectorMembers.get(nodes[index].id) ?? [];
    const x =
      specification !== undefined
        ? coordinates.x[specification]
        : members.length > 0
          ? members.reduce((sum, member) => sum + coordinates.x[member], 0) /
            members.length
          : 0;
    const y =
      specification !== undefined
        ? coordinates.y[specification]
        : members.length > 0
          ? members.reduce((sum, member) => sum + coordinates.y[member], 0) /
            members.length
          : 0;
    positions[index * 3] = x;
    positions[index * 3 + 1] = y;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: nodes.map((node) => node.id),
    positions,
    featureCount: model.featureCount,
    routeCount: model.routeCount,
    iterations: 96,
  };
}
