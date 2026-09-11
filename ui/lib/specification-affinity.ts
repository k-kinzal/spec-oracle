import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
} from "./specification-layout";
import {
  deriveSpecificationProximity,
  normalizedInverseDocumentFrequency,
  type ProximitySignal,
} from "./specification-proximity";

export type AffinityEdge = {
  source: number;
  target: number;
  weight: number;
  rawWeight: number;
  localRawWeight: number;
  broadRawWeight: number;
  localWeight: number;
  independentSignals: number;
  semantic: boolean;
  selection: boolean;
  broadFactual: boolean;
  factual: boolean;
  broadDegree: number;
  featureDegree: number;
};

export type SparseAffinityModel = {
  specificationNodes: SpecificationLayoutInputNode[];
  specificationIndex: ReadonlyMap<string, number>;
  edges: AffinityEdge[];
  adjacency: ReadonlyArray<ReadonlySet<number>>;
  factualHyperedges: ReadonlyArray<{
    members: readonly number[];
    weight: number;
  }>;
  featureCount: number;
  routeCount: number;
  candidatePairCount: number;
};

type AccumulatedPair = {
  source: number;
  target: number;
  rawWeight: number;
  localRawWeight: number;
  broadRawWeight: number;
  signals: Set<string>;
  semantic: boolean;
  selection: boolean;
  broadFactual: boolean;
  factual: boolean;
  broadDegree: number;
  featureDegree: number;
  stableOrder: number;
};

function pairKey(source: number, target: number, population: number) {
  return source < target
    ? source * population + target
    : target * population + source;
}

function pairEndpoints(key: number, population: number) {
  const source = Math.floor(key / population);
  return [source, key - source * population] as const;
}

function signalIdentity(signal: ProximitySignal, id: string) {
  return signal === "lexical_unigram" || signal === "lexical_bigram"
    ? signal
    : `${signal}\u0000${id}`;
}

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

/**
 * Convert factual and view-derived proximity routes into a sparse symmetric
 * affinity graph. Narrow features nominate candidate pairs. Broad features can
 * strengthen already nominated pairs but cannot manufacture an arbitrary
 * sampled topology of their own.
 */
export function buildSparseAffinity(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  neighborBudget = 32,
  retention: "strongest" | "multiscale" | "stable-multiscale" = "strongest",
  strongestReserve = 4,
): SparseAffinityModel {
  const specificationNodes = nodes.filter(
    (node) => node.nodeKind === "specification",
  );
  const specificationIndex = new Map(
    specificationNodes.map((node, index) => [node.id, index]),
  );
  const population = specificationNodes.length;
  const proximity = deriveSpecificationProximity(
    nodes.map((node) => ({
      id: node.id,
      nodeKind: node.nodeKind,
      statement: node.statement,
      excludedViewFeatureIds: node.excludedViewFeatureIds,
    })),
    edges,
  );
  const pairs = new Map<number, AccumulatedPair>();
  const factualHyperedges: Array<{
    members: number[];
    weight: number;
  }> = [];
  // Enumerating a complete feature clique is exact and inexpensive for narrow
  // evidence. The fixed ceiling is a complexity guard, not a corpus-specific
  // context threshold; broader evidence can only refine an already nominated
  // pair below.
  const exactFeatureDegree = 64;
  const add = (
    source: number,
    target: number,
    weight: number,
    identity: string,
    signal: ProximitySignal,
    broadFactual = false,
    broadDegree = 1,
    featureDegree = 1,
  ) => {
    if (source === target || weight <= 0) return;
    const key = pairKey(source, target, population);
    const [left, right] = pairEndpoints(key, population);
    const pair = pairs.get(key) ?? {
      source: left,
      target: right,
      rawWeight: 0,
      localRawWeight: 0,
      broadRawWeight: 0,
      signals: new Set<string>(),
      semantic: false,
      selection: false,
      broadFactual: false,
      factual: false,
      broadDegree: 1,
      featureDegree: 1,
      stableOrder: stableHash(
        `${specificationNodes[left].id}\u0000${specificationNodes[right].id}`,
      ),
    };
    pair.rawWeight += weight;
    if (broadFactual) pair.broadRawWeight += weight;
    else pair.localRawWeight += weight;
    pair.signals.add(identity);
    pair.semantic ||= signal === "semantic";
    pair.selection ||= signal === "selection";
    pair.broadFactual ||= broadFactual;
    pair.factual ||=
      signal === "shared_term" || signal === "shared_projection";
    if (broadFactual) pair.broadDegree = Math.max(pair.broadDegree, broadDegree);
    pair.featureDegree = Math.max(pair.featureDegree, featureDegree);
    pairs.set(key, pair);
  };

  for (const link of proximity.links) {
    if (link.signal !== "semantic" && link.signal !== "selection") continue;
    const source = specificationIndex.get(link.source);
    const target = specificationIndex.get(link.target);
    if (source === undefined || target === undefined) continue;
    add(source, target, link.weight, signalIdentity(link.signal, link.id), link.signal);
  }

  const broadMembership = Array.from(
    {length: population},
    () => new Map<string, number>(),
  );
  for (const hyperedge of proximity.hyperedges) {
    const information = normalizedInverseDocumentFrequency(
      population,
      hyperedge.degree,
    );
    const weight =
      (hyperedge.members.reduce((sum, member) => sum + member.weight, 0) /
        hyperedge.members.length) * information;
    if (weight <= 0) continue;
    const identity = signalIdentity(hyperedge.signal, hyperedge.id);
    if (hyperedge.degree <= exactFeatureDegree) {
      for (let left = 0; left < hyperedge.members.length; left += 1) {
        const leftIndex = specificationIndex.get(
          hyperedge.members[left].specificationId,
        );
        if (leftIndex === undefined) continue;
        for (let right = left + 1; right < hyperedge.members.length; right += 1) {
          const rightIndex = specificationIndex.get(
            hyperedge.members[right].specificationId,
          );
          if (rightIndex === undefined) continue;
          add(
            leftIndex,
            rightIndex,
            weight,
            identity,
            hyperedge.signal,
            false,
            1,
            hyperedge.degree,
          );
        }
      }
    } else {
      const memberIndices = hyperedge.members
        .flatMap((member) => {
          const index = specificationIndex.get(member.specificationId);
          return index === undefined
            ? []
            : [
                {
                  index,
                  order: stableHash(
                    `${hyperedge.id}\u0000${specificationNodes[index].id}`,
                  ),
                },
              ];
        })
        .sort((left, right) => left.order - right.order)
        .map((member) => member.index);
      // A broad hyperedge is a factual all-member relation. Approximate its
      // clique by a deterministic regular graph rather than dropping it or
      // choosing a context. Multiple long strides avoid turning ID order into
      // a chain; normalized information weight goes to zero for a universal
      // feature.
      if (
        hyperedge.signal === "shared_term" ||
        hyperedge.signal === "shared_projection"
      ) {
        const averageMemberWeight =
          hyperedge.members.reduce((sum, member) => sum + member.weight, 0) /
          hyperedge.members.length;
        const factualSparseWeight =
          averageMemberWeight * Math.sqrt(information);
        factualHyperedges.push({
          members: memberIndices,
          weight: factualSparseWeight,
        });
        const fanout = Math.min(
          8,
          Math.max(2, Math.ceil(Math.log2(memberIndices.length))),
        );
        for (let member = 0; member < memberIndices.length; member += 1) {
          for (let channel = 1; channel <= fanout; channel += 1) {
            const offset = Math.max(
              1,
              Math.floor((channel * memberIndices.length) / (fanout + 1)),
            );
            const other = (member + offset) % memberIndices.length;
            add(
              memberIndices[member],
              memberIndices[other],
              factualSparseWeight,
              identity,
              hyperedge.signal,
              true,
              hyperedge.degree,
              hyperedge.degree,
            );
          }
        }
      }
      if (
        hyperedge.signal === "shared_term" ||
        hyperedge.signal === "shared_projection"
      ) {
        for (const member of hyperedge.members) {
          const index = specificationIndex.get(member.specificationId);
          if (index !== undefined) broadMembership[index].set(identity, weight);
        }
      }
    }
  }

  // Broad evidence only refines pairs already justified by a narrow or direct
  // route. Universal evidence contributes equally and therefore no contrast.
  for (const pair of pairs.values()) {
    const left = broadMembership[pair.source];
    const right = broadMembership[pair.target];
    const smaller = left.size <= right.size ? left : right;
    const larger = smaller === left ? right : left;
    for (const [identity, weight] of smaller) {
      const otherWeight = larger.get(identity);
      if (otherWeight === undefined) continue;
      pair.rawWeight += Math.min(weight, otherWeight);
      pair.broadRawWeight += Math.min(weight, otherWeight);
      pair.signals.add(identity);
    }
  }

  const incident = Array.from({length: population}, () => [] as AccumulatedPair[]);
  for (const pair of pairs.values()) {
    incident[pair.source].push(pair);
    incident[pair.target].push(pair);
  }
  const retainedKeys = new Set<number>();
  // Persisted factual and direct relationships are never displaced by the
  // view-only sparsity budget. The budget exists only to bound lexical
  // candidate work; it must not make a recorded graph fact disappear.
  for (const pair of pairs.values()) {
    if (pair.factual || pair.semantic || pair.selection) {
      retainedKeys.add(pairKey(pair.source, pair.target, population));
    }
  }
  const pairOrder = (left: AccumulatedPair, right: AccumulatedPair) =>
    Number(right.selection) - Number(left.selection) ||
    Number(right.semantic) - Number(left.semantic) ||
    right.rawWeight - left.rawWeight ||
    left.stableOrder - right.stableOrder;
  const stableScaleOrder = (left: AccumulatedPair, right: AccumulatedPair) =>
    Number(right.selection) - Number(left.selection) ||
    Number(right.semantic) - Number(left.semantic) ||
    right.localRawWeight - left.localRawWeight ||
    right.rawWeight - left.rawWeight ||
    left.stableOrder - right.stableOrder;
  for (let index = 0; index < population; index += 1) {
    const ordered = incident[index].sort(
      retention === "stable-multiscale" ? stableScaleOrder : pairOrder,
    );
    if (retention === "strongest") {
      ordered
        .slice(0, neighborBudget)
        .forEach((pair) =>
          retainedKeys.add(pairKey(pair.source, pair.target, population)),
        );
      continue;
    }
    const selected = new Set<AccumulatedPair>();
    ordered
      .slice(0, Math.min(strongestReserve, neighborBudget))
      .forEach((pair) => selected.add(pair));
    const byScale = new Map<number, AccumulatedPair[]>();
    for (const pair of ordered) {
      if (selected.has(pair)) continue;
      const scale = Math.floor(Math.log2(Math.max(1, pair.featureDegree)));
      const values = byScale.get(scale) ?? [];
      values.push(pair);
      byScale.set(scale, values);
    }
    const scales = [...byScale.keys()].sort((left, right) => right - left);
    const cursor = new Map(scales.map((scale) => [scale, 0]));
    while (selected.size < neighborBudget) {
      let advanced = false;
      for (const scale of scales) {
        const values = byScale.get(scale) ?? [];
        const offset = cursor.get(scale) ?? 0;
        if (offset >= values.length) continue;
        selected.add(values[offset]);
        cursor.set(scale, offset + 1);
        advanced = true;
        if (selected.size >= neighborBudget) break;
      }
      if (!advanced) break;
    }
    for (const pair of selected) {
      retainedKeys.add(pairKey(pair.source, pair.target, population));
    }
  }
  const retained = [...retainedKeys]
    .sort((left, right) => left - right)
    .map((key) => pairs.get(key))
    .filter((pair): pair is AccumulatedPair => pair !== undefined);
  const maximumByNode = new Float64Array(population);
  const maximumLocalByNode = new Float64Array(population);
  for (const pair of retained) {
    maximumByNode[pair.source] = Math.max(
      maximumByNode[pair.source],
      pair.rawWeight,
    );
    maximumByNode[pair.target] = Math.max(
      maximumByNode[pair.target],
      pair.rawWeight,
    );
    maximumLocalByNode[pair.source] = Math.max(
      maximumLocalByNode[pair.source],
      pair.localRawWeight,
    );
    maximumLocalByNode[pair.target] = Math.max(
      maximumLocalByNode[pair.target],
      pair.localRawWeight,
    );
  }
  const affinityEdges = retained.map((pair) => ({
    source: pair.source,
    target: pair.target,
    rawWeight: pair.rawWeight,
    localRawWeight: pair.localRawWeight,
    broadRawWeight: pair.broadRawWeight,
    localWeight: Math.min(
      1,
      pair.localRawWeight /
        Math.max(
          1e-9,
          Math.sqrt(
            maximumLocalByNode[pair.source] * maximumLocalByNode[pair.target],
          ),
        ),
    ),
    weight: Math.min(
      1,
      pair.rawWeight /
        Math.max(
          1e-9,
          Math.sqrt(
            maximumByNode[pair.source] * maximumByNode[pair.target],
          ),
        ),
    ),
    independentSignals: pair.signals.size,
    semantic: pair.semantic,
    selection: pair.selection,
    broadFactual: pair.broadFactual,
    factual: pair.factual,
    broadDegree: pair.broadDegree,
    featureDegree: pair.featureDegree,
  }));
  const adjacency = Array.from({length: population}, () => new Set<number>());
  for (const edge of affinityEdges) {
    adjacency[edge.source].add(edge.target);
    adjacency[edge.target].add(edge.source);
  }
  return {
    specificationNodes,
    specificationIndex,
    edges: affinityEdges,
    adjacency,
    factualHyperedges,
    featureCount: proximity.featureCount,
    routeCount: proximity.routeCount,
    candidatePairCount: pairs.size,
  };
}
