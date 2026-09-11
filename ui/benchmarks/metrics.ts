import {deterministicRandom} from "./random";
import type {
  FixtureRole,
  LayoutCoordinates,
  LayoutFixture,
  Point2D,
} from "./types";

export type Neighbor = {id: string; distance: number};

function distance(left: Point2D, right: Point2D) {
  return Math.hypot(left.x - right.x, left.y - right.y);
}

function quantile(values: readonly number[], fraction: number) {
  if (values.length === 0) return Number.NaN;
  const sorted = [...values].sort((left, right) => left - right);
  const index = Math.min(
    sorted.length - 1,
    Math.max(0, Math.floor(fraction * sorted.length)),
  );
  return sorted[index];
}

function sampleIds(ids: readonly string[], limit: number, seed: number) {
  if (ids.length <= limit) return [...ids];
  return deterministicRandom(seed).shuffle(ids).slice(0, limit);
}

export function nearestNeighbors(
  originId: string,
  eligibleIds: readonly string[],
  coordinates: LayoutCoordinates,
  count: number,
): Neighbor[] {
  const origin = coordinates.get(originId);
  if (!origin) return [];
  const result: Neighbor[] = [];
  for (const candidateId of eligibleIds) {
    if (candidateId === originId) continue;
    const candidate = coordinates.get(candidateId);
    if (!candidate) continue;
    const entry = {id: candidateId, distance: distance(origin, candidate)};
    let low = 0;
    let high = result.length;
    while (low < high) {
      const middle = (low + high) >>> 1;
      if (result[middle].distance <= entry.distance) low = middle + 1;
      else high = middle;
    }
    if (low < count) result.splice(low, 0, entry);
    else if (result.length < count) result.push(entry);
    if (result.length > count) result.pop();
  }
  return result;
}

function contextMembers(fixture: LayoutFixture) {
  const result = new Map<string, string[]>();
  for (const id of fixture.specificationIds) {
    const role = fixture.roles.get(id);
    if (role?.kind !== "context") continue;
    const members = result.get(role.context) ?? [];
    members.push(id);
    result.set(role.context, members);
  }
  return result;
}

function randomDistinctPair(
  values: readonly string[],
  random: ReturnType<typeof deterministicRandom>,
) {
  const leftIndex = random.integer(values.length);
  let rightIndex = random.integer(values.length - 1);
  if (rightIndex >= leftIndex) rightIndex += 1;
  return [values[leftIndex], values[rightIndex]] as const;
}

export function contextSeparationAuc(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
  samples = 20_000,
) {
  const groups = [...contextMembers(fixture).values()].filter(
    (members) => members.length >= 2,
  );
  if (groups.length < 2) return Number.NaN;
  const random = deterministicRandom(fixture.seed ^ 0xa0c);
  let wins = 0;
  let comparisons = 0;
  for (let index = 0; index < samples; index += 1) {
    const sameGroup = random.pick(groups);
    const [sameLeft, sameRight] = randomDistinctPair(sameGroup, random);
    const leftGroupIndex = random.integer(groups.length);
    let rightGroupIndex = random.integer(groups.length - 1);
    if (rightGroupIndex >= leftGroupIndex) rightGroupIndex += 1;
    const crossLeft = random.pick(groups[leftGroupIndex]);
    const crossRight = random.pick(groups[rightGroupIndex]);
    const sameLeftPoint = coordinates.get(sameLeft);
    const sameRightPoint = coordinates.get(sameRight);
    const crossLeftPoint = coordinates.get(crossLeft);
    const crossRightPoint = coordinates.get(crossRight);
    if (!sameLeftPoint || !sameRightPoint || !crossLeftPoint || !crossRightPoint) {
      continue;
    }
    const sameDistance = distance(sameLeftPoint, sameRightPoint);
    const crossDistance = distance(crossLeftPoint, crossRightPoint);
    wins += sameDistance < crossDistance ? 1 : sameDistance === crossDistance ? 0.5 : 0;
    comparisons += 1;
  }
  return comparisons > 0 ? wins / comparisons : Number.NaN;
}

export function contextNeighborPurity(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
  count = 10,
  sampleLimit = 1_000,
) {
  const labeled = fixture.specificationIds.filter(
    (id) => fixture.roles.get(id)?.kind === "context",
  );
  const sampled = sampleIds(labeled, sampleLimit, fixture.seed ^ 0x51a);
  let matching = 0;
  let total = 0;
  for (const id of sampled) {
    const role = fixture.roles.get(id);
    if (role?.kind !== "context") continue;
    for (const neighbor of nearestNeighbors(id, labeled, coordinates, count)) {
      const neighborRole = fixture.roles.get(neighbor.id);
      if (neighborRole?.kind === "context" && neighborRole.context === role.context) {
        matching += 1;
      }
      total += 1;
    }
  }
  return total > 0 ? matching / total : Number.NaN;
}

export function meanNeighborhoodJaccard(
  specificationIds: readonly string[],
  left: LayoutCoordinates,
  right: LayoutCoordinates,
  count = 20,
  sampleLimit = 1_000,
  seed = 0,
) {
  const sampled = sampleIds(specificationIds, sampleLimit, seed ^ 0xacc);
  let total = 0;
  let measured = 0;
  for (const id of sampled) {
    const leftSet = new Set(
      nearestNeighbors(id, specificationIds, left, count).map((value) => value.id),
    );
    const rightSet = new Set(
      nearestNeighbors(id, specificationIds, right, count).map((value) => value.id),
    );
    if (leftSet.size === 0 || rightSet.size === 0) continue;
    let intersection = 0;
    for (const value of leftSet) if (rightSet.has(value)) intersection += 1;
    total += intersection / (leftSet.size + rightSet.size - intersection);
    measured += 1;
  }
  return measured > 0 ? total / measured : Number.NaN;
}

function sampledPairDistances(
  groups: readonly (readonly string[])[],
  coordinates: LayoutCoordinates,
  samples: number,
  random: ReturnType<typeof deterministicRandom>,
) {
  const values: number[] = [];
  for (let index = 0; index < samples; index += 1) {
    const group = random.pick(groups);
    if (group.length < 2) continue;
    const [left, right] = randomDistinctPair(group, random);
    const leftPoint = coordinates.get(left);
    const rightPoint = coordinates.get(right);
    if (leftPoint && rightPoint) values.push(distance(leftPoint, rightPoint));
  }
  return values;
}

export function hierarchyOrder(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
  samples = 10_000,
) {
  const byContext = contextMembers(fixture);
  const parentByContext = new Map<string, string>();
  for (const id of fixture.specificationIds) {
    const role = fixture.roles.get(id);
    if (role?.kind === "context" && role.parent) {
      parentByContext.set(role.context, role.parent);
    }
  }
  const random = deterministicRandom(fixture.seed ^ 0x41e);
  const within = sampledPairDistances(
    [...byContext.values()],
    coordinates,
    samples,
    random,
  );
  const sibling: number[] = [];
  const crossParent: number[] = [];
  const contexts = [...byContext.keys()];
  for (let index = 0; index < samples; index += 1) {
    const leftContext = random.pick(contexts);
    const sameParent = contexts.filter(
      (value) =>
        value !== leftContext &&
        parentByContext.get(value) === parentByContext.get(leftContext),
    );
    const otherParent = contexts.filter(
      (value) => parentByContext.get(value) !== parentByContext.get(leftContext),
    );
    if (sameParent.length > 0) {
      const leftPoint = coordinates.get(random.pick(byContext.get(leftContext) ?? []));
      const rightPoint = coordinates.get(
        random.pick(byContext.get(random.pick(sameParent)) ?? []),
      );
      if (leftPoint && rightPoint) sibling.push(distance(leftPoint, rightPoint));
    }
    if (otherParent.length > 0) {
      const leftPoint = coordinates.get(random.pick(byContext.get(leftContext) ?? []));
      const rightPoint = coordinates.get(
        random.pick(byContext.get(random.pick(otherParent)) ?? []),
      );
      if (leftPoint && rightPoint) crossParent.push(distance(leftPoint, rightPoint));
    }
  }
  const medians = {
    withinSubcontext: quantile(within, 0.5),
    acrossSiblings: quantile(sibling, 0.5),
    acrossParents: quantile(crossParent, 0.5),
  };
  return {
    ...medians,
    ordered:
      medians.withinSubcontext < medians.acrossSiblings &&
      medians.acrossSiblings < medians.acrossParents,
  };
}

export function overlapCoverage(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
  count = 20,
) {
  const overlap = fixture.specificationIds.filter(
    (id) => fixture.roles.get(id)?.kind === "overlap",
  );
  let passing = 0;
  for (const id of overlap) {
    const role = fixture.roles.get(id);
    if (role?.kind !== "overlap") continue;
    const represented = new Set<string>();
    for (const neighbor of nearestNeighbors(
      id,
      fixture.specificationIds,
      coordinates,
      count,
    )) {
      const neighborRole = fixture.roles.get(neighbor.id);
      if (neighborRole?.kind === "context") represented.add(neighborRole.context);
      if (neighborRole?.kind === "overlap") {
        for (const context of neighborRole.contexts) represented.add(context);
      }
    }
    if (role.contexts.every((context) => represented.has(context))) passing += 1;
  }
  return overlap.length > 0 ? passing / overlap.length : Number.NaN;
}

function medianDistanceToMembers(
  id: string,
  members: readonly string[],
  coordinates: LayoutCoordinates,
) {
  const origin = coordinates.get(id);
  if (!origin) return Number.POSITIVE_INFINITY;
  return quantile(
    members.flatMap((member) => {
      const point = coordinates.get(member);
      return point ? [distance(origin, point)] : [];
    }),
    0.5,
  );
}

export function bridgeCoverage(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
) {
  const groups = contextMembers(fixture);
  const bridges = fixture.specificationIds.filter(
    (id) => fixture.roles.get(id)?.kind === "bridge",
  );
  let passing = 0;
  for (const id of bridges) {
    const role = fixture.roles.get(id);
    if (role?.kind !== "bridge") continue;
    const linked = role.contexts.map((context) =>
      medianDistanceToMembers(id, groups.get(context) ?? [], coordinates),
    );
    const unrelated = fixture.contextIds
      .filter((context) => !role.contexts.includes(context))
      .map((context) =>
        medianDistanceToMembers(id, groups.get(context) ?? [], coordinates),
      );
    if (
      linked.every((value) =>
        unrelated.every((unrelatedValue) => value < unrelatedValue),
      )
    ) {
      passing += 1;
    }
  }
  return bridges.length > 0 ? passing / bridges.length : Number.NaN;
}

class DisjointSet {
  private readonly parent: Int32Array;
  private readonly size: Int32Array;

  constructor(count: number) {
    this.parent = Int32Array.from({length: count}, (_, index) => index);
    this.size = new Int32Array(count).fill(1);
  }

  find(value: number): number {
    let root = value;
    while (this.parent[root] !== root) root = this.parent[root];
    while (this.parent[value] !== value) {
      const next = this.parent[value];
      this.parent[value] = root;
      value = next;
    }
    return root;
  }

  union(left: number, right: number) {
    let leftRoot = this.find(left);
    let rightRoot = this.find(right);
    if (leftRoot === rightRoot) return;
    if (this.size[leftRoot] < this.size[rightRoot]) {
      [leftRoot, rightRoot] = [rightRoot, leftRoot];
    }
    this.parent[rightRoot] = leftRoot;
    this.size[leftRoot] += this.size[rightRoot];
  }
}

/**
 * Evaluation-only density basin count. Mutual k-nearest-neighbor connectivity
 * avoids assigning a production context and does not feed back into layout.
 */
export function densityBasinCounts(
  specificationIds: readonly string[],
  coordinates: LayoutCoordinates,
  scales: readonly number[] = [10, 20, 40],
) {
  return densityBasinMemberships(specificationIds, coordinates, scales).map(
    ({scale, basins, coveredFraction}) => ({
      scale,
      count: basins.length,
      coveredFraction,
    }),
  );
}

export type DensityBasinMembership = {
  scale: number;
  basins: number[][];
  coveredFraction: number;
};

/**
 * Evaluation-only memberships behind the basin count. Candidate algorithms
 * never receive these groups; they are derived exclusively from final XY
 * coordinates so their source-graph affinity can be tested independently.
 */
export function densityBasinMemberships(
  specificationIds: readonly string[],
  coordinates: LayoutCoordinates,
  scales: readonly number[] = [10, 20, 40],
): DensityBasinMembership[] {
  const maximum = Math.min(
    Math.max(...scales),
    Math.max(1, specificationIds.length - 1),
  );
  const neighbors = specificationIds.map((id) =>
    nearestNeighbors(id, specificationIds, coordinates, maximum),
  );
  const indexById = new Map(specificationIds.map((id, index) => [id, index]));
  const minimumBasinSize = Math.max(5, Math.ceil(specificationIds.length * 0.02));
  return scales.map((requestedScale) => {
    const scale = Math.min(requestedScale, maximum);
    const sets = neighbors.map(
      (values) => new Set(values.slice(0, scale).map((value) => value.id)),
    );
    const localRadius = neighbors.map(
      (values) => values[Math.min(scale, values.length) - 1]?.distance ?? 0,
    );
    // A basin is anchored by a connected component of the denser half of the
    // final XY population. Sparse bridge points are assigned only after these
    // cores are found, so a thin path cannot erase a genuine density valley.
    // On a uniform body the dense core remains connected and yields one basin.
    const coreThreshold = quantile(localRadius, 0.5);
    const core = localRadius.map((radius) => radius <= coreThreshold);
    const disjoint = new DisjointSet(specificationIds.length);
    for (let index = 0; index < specificationIds.length; index += 1) {
      if (!core[index]) continue;
      for (const neighbor of neighbors[index].slice(0, scale)) {
        const other = indexById.get(neighbor.id);
        if (
          other !== undefined &&
          core[other] &&
          sets[other].has(specificationIds[index]) &&
          neighbor.distance <= Math.min(localRadius[index], localRadius[other])
        ) {
          disjoint.union(index, other);
        }
      }
    }
    const coreMembers = new Map<number, number[]>();
    for (let index = 0; index < specificationIds.length; index += 1) {
      if (!core[index]) continue;
      const root = disjoint.find(index);
      const basin = coreMembers.get(root) ?? [];
      basin.push(index);
      coreMembers.set(root, basin);
    }
    const minimumCoreSize = Math.max(
      3,
      Math.ceil(specificationIds.length * 0.005),
    );
    const retainedRoots = new Set(
      [...coreMembers]
        .filter(([, members]) => members.length >= minimumCoreSize)
        .map(([root]) => root),
    );
    const members = new Map<number, number[]>(
      [...retainedRoots].map((root) => [root, []]),
    );
    const retainedCoreIndexes = [...coreMembers]
      .filter(([root]) => retainedRoots.has(root))
      .flatMap(([, values]) => values);
    if (retainedCoreIndexes.length === 0) {
      return {
        scale: requestedScale,
        basins: [Array.from({length: specificationIds.length}, (_, index) => index)],
        coveredFraction: 1,
      };
    }
    for (let index = 0; index < specificationIds.length; index += 1) {
      let nearestCore = core[index] ? index : undefined;
      if (
        nearestCore === undefined ||
        !retainedRoots.has(disjoint.find(nearestCore))
      ) {
        nearestCore = undefined;
        for (const neighbor of neighbors[index]) {
          const candidate = indexById.get(neighbor.id);
          if (
            candidate !== undefined &&
            core[candidate] &&
            retainedRoots.has(disjoint.find(candidate))
          ) {
            nearestCore = candidate;
            break;
          }
        }
      }
      if (nearestCore === undefined) {
        const point = coordinates.get(specificationIds[index]);
        let nearestDistance = Number.POSITIVE_INFINITY;
        for (const candidate of retainedCoreIndexes) {
          const candidatePoint = coordinates.get(specificationIds[candidate]);
          if (!point || !candidatePoint) continue;
          const candidateDistance = distance(point, candidatePoint);
          if (candidateDistance < nearestDistance) {
            nearestDistance = candidateDistance;
            nearestCore = candidate;
          }
        }
      }
      if (nearestCore !== undefined) {
        members.get(disjoint.find(nearestCore))?.push(index);
      }
    }
    const basins = [...members.values()]
      .filter((basin) => basin.length >= minimumBasinSize)
      .sort(
        (left, right) =>
          right.length - left.length || (left[0] ?? 0) - (right[0] ?? 0),
      );
    return {
      scale: requestedScale,
      basins,
      coveredFraction:
        basins.reduce((sum, basin) => sum + basin.length, 0) /
        specificationIds.length,
    };
  });
}

export function disconnectedGapRatio(
  fixture: LayoutFixture,
  coordinates: LayoutCoordinates,
  localNeighborCount = 10,
) {
  const groups = [...contextMembers(fixture).entries()];
  let minimumCross = Number.POSITIVE_INFINITY;
  for (let left = 0; left < groups.length; left += 1) {
    for (let right = left + 1; right < groups.length; right += 1) {
      for (const leftId of groups[left][1]) {
        const leftPoint = coordinates.get(leftId);
        if (!leftPoint) continue;
        for (const rightId of groups[right][1]) {
          const rightPoint = coordinates.get(rightId);
          if (rightPoint) minimumCross = Math.min(minimumCross, distance(leftPoint, rightPoint));
        }
      }
    }
  }
  const localRadii = fixture.specificationIds.flatMap((id) => {
    const role = fixture.roles.get(id);
    if (role?.kind !== "context") return [];
    const members = groups.find(([context]) => context === role.context)?.[1] ?? [];
    const neighbors = nearestNeighbors(
      id,
      members,
      coordinates,
      localNeighborCount,
    );
    return neighbors.length > 0 ? [neighbors[neighbors.length - 1].distance] : [];
  });
  const localMedian = quantile(localRadii, 0.5);
  return minimumCross / localMedian;
}

export function coordinateIntegrity(
  fixture: LayoutFixture,
  result: {ids: string[]; positions: Float32Array},
) {
  const resultIds = new Set(result.ids);
  const missing = fixture.specificationIds.filter((id) => !resultIds.has(id));
  let nonFinite = 0;
  let nonzeroZ = 0;
  for (let index = 0; index < result.ids.length; index += 1) {
    const x = result.positions[index * 3];
    const y = result.positions[index * 3 + 1];
    const z = result.positions[index * 3 + 2];
    if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) {
      nonFinite += 1;
    }
    if (z !== 0) nonzeroZ += 1;
  }
  return {missing, nonFinite, nonzeroZ};
}
