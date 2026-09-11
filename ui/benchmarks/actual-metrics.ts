import type {AffinityEdge, SparseAffinityModel} from "./affinity";
import {densityBasinMemberships, nearestNeighbors} from "./metrics";
import {deterministicRandom} from "./random";
import type {LayoutCoordinates} from "./types";

function distance(
  coordinates: LayoutCoordinates,
  source: number,
  target: number,
  model: SparseAffinityModel,
) {
  const left = coordinates.get(model.specificationNodes[source].id);
  const right = coordinates.get(model.specificationNodes[target].id);
  return left && right
    ? Math.hypot(left.x - right.x, left.y - right.y)
    : Number.POSITIVE_INFINITY;
}

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function degreeBucket(degree: number) {
  return Math.floor(Math.log2(Math.max(1, degree)));
}

function degreeMatchedNegative(
  edge: AffinityEdge,
  model: SparseAffinityModel,
  buckets: ReadonlyMap<number, readonly number[]>,
) {
  const targetBucket = degreeBucket(model.adjacency[edge.target].size);
  const candidates = buckets.get(targetBucket) ?? [];
  if (candidates.length === 0) return undefined;
  const sourceId = model.specificationNodes[edge.source].id;
  const targetId = model.specificationNodes[edge.target].id;
  let index = stableHash(`${sourceId}\u0000${targetId}`) % candidates.length;
  for (let attempt = 0; attempt < candidates.length; attempt += 1) {
    const candidate = candidates[index];
    if (
      candidate !== edge.source &&
      candidate !== edge.target &&
      !model.adjacency[edge.source].has(candidate)
    ) {
      return candidate;
    }
    index = (index + 1) % candidates.length;
  }
  return undefined;
}

export function relationDistanceAuc(
  edges: readonly AffinityEdge[],
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
) {
  const buckets = new Map<number, number[]>();
  for (let index = 0; index < model.specificationNodes.length; index += 1) {
    const bucket = degreeBucket(model.adjacency[index].size);
    const values = buckets.get(bucket) ?? [];
    values.push(index);
    buckets.set(bucket, values);
  }
  let wins = 0;
  let comparisons = 0;
  for (const edge of edges) {
    const negativeTarget = degreeMatchedNegative(edge, model, buckets);
    if (negativeTarget === undefined) continue;
    const positiveDistance = distance(
      coordinates,
      edge.source,
      edge.target,
      model,
    );
    const negativeDistance = distance(
      coordinates,
      edge.source,
      negativeTarget,
      model,
    );
    wins +=
      positiveDistance < negativeDistance
        ? 1
        : positiveDistance === negativeDistance
          ? 0.5
          : 0;
    comparisons += 1;
  }
  return {
    auc: comparisons > 0 ? wins / comparisons : Number.NaN,
    comparisons,
  };
}

export function actualRelationAucs(
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
) {
  const direct = model.edges.filter((edge) => edge.semantic || edge.selection);
  const weights = model.edges
    .map((edge) => edge.rawWeight)
    .sort((left, right) => left - right);
  const threshold = weights[Math.floor(weights.length * 0.75)] ?? Infinity;
  const strongest = model.edges.filter((edge) => edge.rawWeight >= threshold);
  return {
    direct: relationDistanceAuc(direct, model, coordinates),
    strongestQuartile: relationDistanceAuc(strongest, model, coordinates),
    strongestQuartileThreshold: threshold,
  };
}

export function weightedNeighborhoodRecall(
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
  counts: readonly number[] = [10, 20, 50],
  sampleLimit = 1_000,
  geometricCache?: {
    sampled: readonly number[];
    neighbors: ReadonlyMap<number, readonly number[]>;
    maximum: number;
  },
) {
  const ids = model.specificationNodes.map((node) => node.id);
  const maximum = Math.max(...counts);
  const incident = Array.from(
    {length: model.specificationNodes.length},
    () => [] as AffinityEdge[],
  );
  for (const edge of model.edges) {
    incident[edge.source].push(edge);
    incident[edge.target].push(edge);
  }
  const sampled =
    geometricCache?.sampled ??
    Array.from(
      {length: Math.min(sampleLimit, ids.length)},
      (_, sample) =>
        Math.floor(
          (sample * ids.length) / Math.min(sampleLimit, ids.length),
        ),
    );
  const geometricNeighbors =
    geometricCache?.neighbors ??
    new Map(
      sampled.map((source) => [
        source,
        nearestNeighbors(ids[source], ids, coordinates, maximum).flatMap(
          (neighbor) => {
            const index = model.specificationIndex.get(neighbor.id);
            return index === undefined ? [] : [index];
          },
        ),
      ]),
    );
  const totals = new Map(counts.map((count) => [count, {recalled: 0, possible: 0}]));
  for (const source of sampled) {
    const rankedAffinity = [...incident[source]].sort(
      (left, right) =>
        right.rawWeight - left.rawWeight ||
        (left.source === source ? left.target : left.source) -
          (right.source === source ? right.target : right.source),
    );
    const geometric = geometricNeighbors.get(source) ?? [];
    for (const count of counts) {
      const topAffinity = rankedAffinity.slice(0, count);
      const geometricSet = new Set(geometric.slice(0, count));
      const totalsForCount = totals.get(count);
      if (!totalsForCount) continue;
      for (const edge of topAffinity) {
        const target = edge.source === source ? edge.target : edge.source;
        totalsForCount.possible += edge.rawWeight;
        if (geometricSet.has(target)) totalsForCount.recalled += edge.rawWeight;
      }
    }
  }
  return Object.fromEntries(
    [...totals].map(([count, value]) => [
      count,
      value.possible > 0 ? value.recalled / value.possible : Number.NaN,
    ]),
  );
}

function median(values: number[]) {
  values.sort((left, right) => left - right);
  return values[Math.floor(values.length / 2)] ?? Number.NaN;
}

function quantile(values: readonly number[], fraction: number) {
  if (values.length === 0) return Number.NaN;
  const sorted = [...values].sort((left, right) => left - right);
  const index = Math.max(
    0,
    Math.min(sorted.length - 1, Math.floor(fraction * sorted.length)),
  );
  return sorted[index];
}

function sampleValues(values: readonly number[], limit: number, seed: number) {
  if (values.length <= limit) return [...values];
  return deterministicRandom(seed).shuffle(values).slice(0, limit);
}

function bootstrapMedianDifference(
  left: readonly number[],
  right: readonly number[],
  seed: number,
  resamples = 400,
) {
  if (left.length === 0 || right.length === 0) {
    return {lower: Number.NaN, upper: Number.NaN};
  }
  const random = deterministicRandom(seed);
  const differences: number[] = [];
  for (let sample = 0; sample < resamples; sample += 1) {
    const leftSample = Array.from(
      {length: left.length},
      () => left[random.integer(left.length)],
    );
    const rightSample = Array.from(
      {length: right.length},
      () => right[random.integer(right.length)],
    );
    differences.push(median(leftSample) - median(rightSample));
  }
  return {
    lower: quantile(differences, 0.025),
    upper: quantile(differences, 0.975),
  };
}

export function independentSignalDistanceOrder(
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
  options: {bootstrap?: boolean; seed?: number; sampleLimit?: number} = {},
) {
  const one: number[] = [];
  const two: number[] = [];
  const threeOrMore: number[] = [];
  for (const edge of model.edges) {
    const value = distance(coordinates, edge.source, edge.target, model);
    if (edge.independentSignals >= 3) threeOrMore.push(value);
    else if (edge.independentSignals === 2) two.push(value);
    else one.push(value);
  }
  const medians = {
    one: median([...one]),
    two: median([...two]),
    threeOrMore: median([...threeOrMore]),
  };
  const sampleLimit = options.sampleLimit ?? 5_000;
  const seed = options.seed ?? 0x51a6a1;
  const sampledOne = sampleValues(one, sampleLimit, seed ^ 0x101);
  const sampledTwo = sampleValues(two, sampleLimit, seed ^ 0x202);
  const sampledThree = sampleValues(threeOrMore, sampleLimit, seed ^ 0x303);
  const confidenceIntervals = options.bootstrap
    ? {
        oneMinusTwo: bootstrapMedianDifference(
          sampledOne,
          sampledTwo,
          seed ^ 0xa12,
        ),
        twoMinusThreeOrMore: bootstrapMedianDifference(
          sampledTwo,
          sampledThree,
          seed ^ 0xb23,
        ),
      }
    : undefined;
  return {
    ...medians,
    counts: {one: one.length, two: two.length, threeOrMore: threeOrMore.length},
    ordered:
      medians.threeOrMore < medians.two && medians.two < medians.one,
    confidenceIntervals,
    confidencePass:
      confidenceIntervals === undefined
        ? undefined
        : confidenceIntervals.oneMinusTwo.lower > 0 &&
          confidenceIntervals.twoMinusThreeOrMore.lower > 0,
  };
}

function pairKey(source: number, target: number) {
  return source < target ? `${source}:${target}` : `${target}:${source}`;
}

/** Degree-preserving double-edge swaps used only to form an evaluation null. */
export function degreePreservingShuffle(
  model: SparseAffinityModel,
  seed: number,
  swapsPerEdge = 5,
): SparseAffinityModel {
  const random = deterministicRandom(seed);
  const edges = model.edges.map((edge) => ({...edge}));
  const pairs = new Set(edges.map((edge) => pairKey(edge.source, edge.target)));
  const attempts = Math.max(1, edges.length * swapsPerEdge);
  for (let attempt = 0; attempt < attempts && edges.length > 1; attempt += 1) {
    const leftIndex = random.integer(edges.length);
    let rightIndex = random.integer(edges.length - 1);
    if (rightIndex >= leftIndex) rightIndex += 1;
    const left = edges[leftIndex];
    const right = edges[rightIndex];
    const [a, b] = [left.source, left.target];
    const [c, d] = [right.source, right.target];
    const proposed =
      random.next() < 0.5
        ? ([
            [a, d],
            [c, b],
          ] as const)
        : ([
            [a, c],
            [b, d],
          ] as const);
    const [nextLeft, nextRight] = proposed;
    if (
      nextLeft[0] === nextLeft[1] ||
      nextRight[0] === nextRight[1] ||
      pairKey(nextLeft[0], nextLeft[1]) === pairKey(nextRight[0], nextRight[1])
    ) {
      continue;
    }
    const oldLeftKey = pairKey(a, b);
    const oldRightKey = pairKey(c, d);
    pairs.delete(oldLeftKey);
    pairs.delete(oldRightKey);
    const nextLeftKey = pairKey(nextLeft[0], nextLeft[1]);
    const nextRightKey = pairKey(nextRight[0], nextRight[1]);
    if (pairs.has(nextLeftKey) || pairs.has(nextRightKey)) {
      pairs.add(oldLeftKey);
      pairs.add(oldRightKey);
      continue;
    }
    left.source = Math.min(nextLeft[0], nextLeft[1]);
    left.target = Math.max(nextLeft[0], nextLeft[1]);
    right.source = Math.min(nextRight[0], nextRight[1]);
    right.target = Math.max(nextRight[0], nextRight[1]);
    pairs.add(nextLeftKey);
    pairs.add(nextRightKey);
  }
  const adjacency = Array.from(
    {length: model.specificationNodes.length},
    () => new Set<number>(),
  );
  for (const edge of edges) {
    adjacency[edge.source].add(edge.target);
    adjacency[edge.target].add(edge.source);
  }
  return {...model, edges, adjacency};
}

function meanAndPopulationDeviation(values: readonly number[]) {
  const mean =
    values.reduce((sum, value) => sum + value, 0) / Math.max(1, values.length);
  const deviation = Math.sqrt(
    values.reduce((sum, value) => sum + (value - mean) ** 2, 0) /
      Math.max(1, values.length),
  );
  return {mean, deviation};
}

export function shuffledRecallNull(
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
  baseline: Readonly<Record<number, number>>,
  counts: readonly number[] = [10, 20, 50],
  trials = 5,
) {
  const ids = model.specificationNodes.map((node) => node.id);
  const maximum = Math.max(...counts);
  const sampleLimit = 1_000;
  const sampled = Array.from(
    {length: Math.min(sampleLimit, ids.length)},
    (_, sample) =>
      Math.floor((sample * ids.length) / Math.min(sampleLimit, ids.length)),
  );
  const neighbors = new Map(
    sampled.map((source) => [
      source,
      nearestNeighbors(ids[source], ids, coordinates, maximum).flatMap(
        (neighbor) => {
          const index = model.specificationIndex.get(neighbor.id);
          return index === undefined ? [] : [index];
        },
      ),
    ]),
  );
  const geometricCache = {sampled, neighbors, maximum};
  const actual = weightedNeighborhoodRecall(
    model,
    coordinates,
    counts,
    sampleLimit,
    geometricCache,
  );
  const shuffled = Array.from({length: trials}, (_, trial) =>
    weightedNeighborhoodRecall(
      degreePreservingShuffle(model, 0x5a17 + trial * 104729),
      coordinates,
      counts,
      sampleLimit,
      geometricCache,
    ),
  );
  const comparisons = Object.fromEntries(
    counts.map((count) => {
      const nullValues = shuffled.map((value) => value[count]);
      const {mean, deviation} = meanAndPopulationDeviation(nullValues);
      const value = actual[count];
      const z =
        deviation > 0
          ? (value - mean) / deviation
          : value > mean
            ? Number.POSITIVE_INFINITY
            : 0;
      return [
        count,
        {
          value,
          baseline: baseline[count],
          previousBaseline: baseline[count],
          relativeToPreviousBaseline:
            baseline[count] > 0 ? value / baseline[count] : null,
          nullMean: mean,
          nullDeviation: deviation,
          z,
        },
      ];
    }),
  );
  return {actual, shuffled, comparisons};
}

function internalAffinityFraction(
  edges: readonly AffinityEdge[],
  population: number,
  basins: readonly (readonly number[])[],
) {
  const membership = new Int32Array(population).fill(-1);
  basins.forEach((basin, basinIndex) => {
    for (const member of basin) membership[member] = basinIndex;
  });
  let internal = 0;
  let total = 0;
  for (const edge of edges) {
    total += edge.rawWeight;
    if (
      membership[edge.source] >= 0 &&
      membership[edge.source] === membership[edge.target]
    ) {
      internal += edge.rawWeight;
    }
  }
  return total > 0 ? internal / total : Number.NaN;
}

export function densityAffinityEnrichment(
  model: SparseAffinityModel,
  coordinates: LayoutCoordinates,
  scales: readonly number[] = [10, 20, 40],
  permutations = 20,
) {
  const ids = model.specificationNodes.map((node) => node.id);
  const memberships = densityBasinMemberships(ids, coordinates, scales);
  const results = memberships.map(({scale, basins, coveredFraction}) => {
    const observed = internalAffinityFraction(
      model.edges,
      model.specificationNodes.length,
      basins,
    );
    const sizes = basins.map((basin) => basin.length);
    const random = deterministicRandom(0xd31517 ^ scale);
    const nullValues: number[] = [];
    for (let permutation = 0; permutation < permutations; permutation += 1) {
      const shuffled = random.shuffle(
        Array.from(
          {length: model.specificationNodes.length},
          (_, index) => index,
        ),
      );
      let offset = 0;
      const permuted = sizes.map((size) => {
        const basin = shuffled.slice(offset, offset + size);
        offset += size;
        return basin;
      });
      nullValues.push(
        internalAffinityFraction(
          model.edges,
          model.specificationNodes.length,
          permuted,
        ),
      );
    }
    const {mean, deviation} = meanAndPopulationDeviation(nullValues);
    const z =
      deviation > 0
        ? (observed - mean) / deviation
        : observed > mean
          ? Number.POSITIVE_INFINITY
          : 0;
    return {
      scale,
      basinCount: basins.length,
      coveredFraction,
      observed,
      nullMean: mean,
      nullDeviation: deviation,
      z,
    };
  });
  return {results};
}
