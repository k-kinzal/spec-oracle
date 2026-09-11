import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {buildSparseAffinity, type SparseAffinityModel} from "./affinity";

export type ObjectiveFamily =
  | "weighted-linlog"
  | "neighborhood-cross-entropy"
  | "contrastive-stress";

export type ObjectiveSettings = {
  epochs: number;
  learningRate: number;
  negativeSamples: number;
  negativeWeight: number;
  distanceScale: number;
  semanticBoost: number;
  selectionBoost: number;
  positiveTargetBase: number;
  optimizer: "adam" | "sgd" | "cross-entropy-sgd";
  directStress?: boolean;
  neighborBudget?: number;
  multiscaleRetention?: boolean;
  strongestReserve?: number;
  broadFactualBoost?: number;
  broadDegreeExponent?: number;
  stableScaleRetention?: boolean;
  separateScaleWeights?: boolean;
  stableOptimizationOrder?: boolean;
  stableInitialization?: boolean;
  anchorWeight?: number;
};

const SETTINGS: Record<ObjectiveFamily, ObjectiveSettings> = {
  "weighted-linlog": {
    epochs: 260,
    learningRate: 1.4,
    negativeSamples: 14,
    negativeWeight: 0.85,
    distanceScale: 10,
    semanticBoost: 12,
    selectionBoost: 16,
    positiveTargetBase: 8,
    optimizer: "adam",
  },
  "neighborhood-cross-entropy": {
    epochs: 280,
    learningRate: 1.1,
    negativeSamples: 14,
    negativeWeight: 1.1,
    distanceScale: 12,
    semanticBoost: 12,
    selectionBoost: 16,
    positiveTargetBase: 8,
    optimizer: "adam",
  },
  "contrastive-stress": {
    epochs: 600,
    learningRate: 0.85,
    negativeSamples: 16,
    negativeWeight: 0.35,
    distanceScale: 24,
    semanticBoost: 32,
    selectionBoost: 48,
    positiveTargetBase: 8,
    optimizer: "adam",
  },
};

function affinityWeight(
  edge: SparseAffinityModel["edges"][number],
  settings: ObjectiveSettings,
) {
  if (settings.separateScaleWeights) {
    const broad =
      edge.broadRawWeight *
      (settings.broadFactualBoost ?? 1) *
      Math.pow(
        edge.broadDegree,
        Math.min(0.5, Math.max(0, settings.broadDegreeExponent ?? 0)),
      );
    return edge.localWeight + broad;
  }
  return edge.broadFactual && settings.broadDegreeExponent !== undefined
    ? edge.rawWeight *
        (settings.broadFactualBoost ?? 1) *
        Math.pow(
          edge.broadDegree,
          Math.min(0.5, Math.max(0, settings.broadDegreeExponent)),
        )
    : edge.weight;
}

function positiveAffinityWeight(
  edge: SparseAffinityModel["edges"][number],
  settings: ObjectiveSettings,
) {
  return (
    affinityWeight(edge, settings) *
    (edge.selection
      ? settings.selectionBoost
      : edge.semantic
        ? settings.semanticBoost
        : 1)
  );
}

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function pairKey(source: number, target: number, population: number) {
  return source < target
    ? source * population + target
    : target * population + source;
}

export function initialAffinityCoordinates(
  model: SparseAffinityModel,
  settings: ObjectiveSettings,
  options: {
    edgeWeight?: (edge: SparseAffinityModel["edges"][number]) => number;
    includeFactualHyperedges?: boolean;
  } = {},
) {
  const population = model.specificationNodes.length;
  const x = new Float64Array(population);
  const y = new Float64Array(population);
  const spread = Math.max(30, Math.sqrt(Math.max(1, population)) * 4);
  const degree = new Float64Array(population);
  for (const edge of model.edges) {
    const weight =
      options.edgeWeight?.(edge) ??
      edge.weight *
        (edge.selection
          ? settings.selectionBoost
          : edge.semantic
            ? settings.semanticBoost
            : 1);
    degree[edge.source] += weight;
    degree[edge.target] += weight;
  }
  if (options.includeFactualHyperedges !== false) {
    for (const hyperedge of model.factualHyperedges) {
      for (const member of hyperedge.members) degree[member] += hyperedge.weight;
    }
  }
  const active = Array.from({length: population}, (_, index) => index).filter(
    (index) => degree[index] > 1e-12,
  );
  if (active.length >= 3) {
    const inverseSqrtDegree = new Float64Array(population);
    const constant = new Float64Array(population);
    const totalDegree = active.reduce((sum, index) => sum + degree[index], 0);
    for (const index of active) {
      inverseSqrtDegree[index] = 1 / Math.sqrt(degree[index]);
      constant[index] = Math.sqrt(degree[index] / totalDegree);
    }
    const normalize = (vector: Float64Array) => {
      let norm = 0;
      for (const index of active) norm += vector[index] * vector[index];
      norm = Math.sqrt(norm);
      if (norm <= 1e-12) return false;
      for (const index of active) vector[index] /= norm;
      return true;
    };
    const removeBasis = (vector: Float64Array, basis: Float64Array[]) => {
      for (const direction of basis) {
        let projection = 0;
        for (const index of active) projection += vector[index] * direction[index];
        for (const index of active) vector[index] -= projection * direction[index];
      }
    };
    const multiply = (vector: Float64Array) => {
      const output = new Float64Array(population);
      for (const edge of model.edges) {
        const weight =
          options.edgeWeight?.(edge) ??
          edge.weight *
            (edge.selection
              ? settings.selectionBoost
              : edge.semantic
                ? settings.semanticBoost
                : 1);
        output[edge.source] +=
          weight *
          vector[edge.target] *
          inverseSqrtDegree[edge.source] *
          inverseSqrtDegree[edge.target];
        output[edge.target] +=
          weight *
          vector[edge.source] *
          inverseSqrtDegree[edge.target] *
          inverseSqrtDegree[edge.source];
      }
      if (options.includeFactualHyperedges !== false) {
        for (const hyperedge of model.factualHyperedges) {
          let mean = 0;
          for (const member of hyperedge.members) {
            mean += vector[member] * inverseSqrtDegree[member];
          }
          mean = (mean / hyperedge.members.length) * hyperedge.weight;
          for (const member of hyperedge.members) {
            output[member] += mean * inverseSqrtDegree[member];
          }
        }
      }
      return output;
    };
    const solve = (channel: string, previous: Float64Array[]) => {
      let vector = new Float64Array(population);
      for (const index of active) {
        vector[index] =
          (stableHash(`${channel}\u0000${model.specificationNodes[index].id}`) /
            2147483648) -
          1;
      }
      const basis = [constant, ...previous];
      removeBasis(vector, basis);
      normalize(vector);
      for (let iteration = 0; iteration < 96; iteration += 1) {
        const next = multiply(vector);
        removeBasis(next, basis);
        if (!normalize(next)) break;
        vector = next;
      }
      return vector;
    };
    const xAxis = solve("spectral-x", []);
    const yAxis = solve("spectral-y", [xAxis]);
    const activeScale = Math.sqrt(active.length);
    for (const index of active) {
      x[index] = xAxis[index] * activeScale * spread;
      y[index] = yAxis[index] * activeScale * spread;
    }
  }
  const inactive = Array.from({length: population}, (_, index) => index)
    .filter((index) => degree[index] <= 1e-12)
    .sort(
      (left, right) =>
        stableHash(`inactive\u0000${model.specificationNodes[left].id}`) -
        stableHash(`inactive\u0000${model.specificationNodes[right].id}`),
    );
  const goldenAngle = Math.PI * (3 - Math.sqrt(5));
  for (let rank = 0; rank < inactive.length; rank += 1) {
    const index = inactive[rank];
    const angle = rank * goldenAngle;
    const radius =
      Math.sqrt((rank + 0.5) / Math.max(1, inactive.length)) * spread;
    x[index] = Math.cos(angle) * radius;
    y[index] = Math.sin(angle) * radius;
  }
  return {x, y};
}

function negativePairs(
  model: SparseAffinityModel,
  samplesPerNode: number,
) {
  const population = model.specificationNodes.length;
  const pairs = new Set<number>();
  if (population <= 1) return [] as Array<readonly [number, number, number]>;
  const component = new Int32Array(population).fill(-1);
  let componentCount = 0;
  for (let start = 0; start < population; start += 1) {
    if (component[start] !== -1) continue;
    const stack = [start];
    component[start] = componentCount;
    while (stack.length > 0) {
      const current = stack.pop();
      if (current === undefined) break;
      for (const neighbor of model.adjacency[current]) {
        if (component[neighbor] !== -1) continue;
        component[neighbor] = componentCount;
        stack.push(neighbor);
      }
    }
    componentCount += 1;
  }
  const nearInAffinity = (source: number, target: number) => {
    if (model.adjacency[source].has(target)) return true;
    const sourceNeighbors = model.adjacency[source];
    const targetNeighbors = model.adjacency[target];
    const smaller =
      sourceNeighbors.size <= targetNeighbors.size
        ? sourceNeighbors
        : targetNeighbors;
    const larger = smaller === sourceNeighbors ? targetNeighbors : sourceNeighbors;
    for (const neighbor of smaller) if (larger.has(neighbor)) return true;
    return false;
  };
  for (let source = 0; source < population; source += 1) {
    const sourceId = model.specificationNodes[source].id;
    for (let sample = 0; sample < samplesPerNode; sample += 1) {
      let target = stableHash(`negative\u0000${sample}\u0000${sourceId}`) % population;
      for (let attempt = 0; attempt < population; attempt += 1) {
        if (target !== source && !nearInAffinity(source, target)) break;
        target = (target + 1) % population;
      }
      if (target === source || nearInAffinity(source, target)) continue;
      pairs.add(pairKey(source, target, population));
    }
  }
  return [...pairs]
    .sort((left, right) => left - right)
    .map((key) => {
      const source = Math.floor(key / population);
      const target = key - source * population;
      return [
        source,
        target,
        component[source] === component[target] ? 1 : 2,
      ] as const;
    });
}

function addPairGradient(
  gradientX: Float64Array,
  gradientY: Float64Array,
  source: number,
  target: number,
  coefficient: number,
  dx: number,
  dy: number,
) {
  const gx = coefficient * dx;
  const gy = coefficient * dy;
  gradientX[source] += gx;
  gradientY[source] += gy;
  gradientX[target] -= gx;
  gradientY[target] -= gy;
}

function optimizeContrastiveSgd(
  model: SparseAffinityModel,
  settings: ObjectiveSettings,
) {
  const {x, y} = initialAffinityCoordinates(model, settings);
  const negatives = negativePairs(model, settings.negativeSamples);
  const population = model.specificationNodes.length;
  const movePair = (
    source: number,
    target: number,
    coefficient: number,
    rate: number,
    maximumStep: number,
  ) => {
    let dx = x[source] - x[target];
    let dy = y[source] - y[target];
    let squared = dx * dx + dy * dy;
    if (squared < 1e-8) {
      const angle =
        (stableHash(
          `sgd-coincident\u0000${model.specificationNodes[source].id}\u0000${model.specificationNodes[target].id}`,
        ) /
          4294967296) *
        Math.PI *
        2;
      dx = Math.cos(angle) * 1e-4;
      dy = Math.sin(angle) * 1e-4;
      squared = 1e-8;
    }
    let moveX = rate * coefficient * dx;
    let moveY = rate * coefficient * dy;
    const magnitude = Math.hypot(moveX, moveY);
    if (magnitude > maximumStep) {
      moveX *= maximumStep / magnitude;
      moveY *= maximumStep / magnitude;
    }
    x[source] -= moveX;
    y[source] -= moveY;
    x[target] += moveX;
    y[target] += moveY;
  };

  for (let epoch = 0; epoch < settings.epochs; epoch += 1) {
    const cooling = 0.1 + 0.9 * (1 - epoch / settings.epochs);
    const rate = settings.learningRate * cooling;
    const positiveStart =
      model.edges.length > 0 ? (epoch * 104729) % model.edges.length : 0;
    for (let step = 0; step < model.edges.length; step += 1) {
      const edge = model.edges[(positiveStart + step) % model.edges.length];
      const dx = x[edge.source] - x[edge.target];
      const dy = y[edge.source] - y[edge.target];
      const currentDistance = Math.max(1e-4, Math.hypot(dx, dy));
      const positiveWeight = positiveAffinityWeight(edge, settings);
      const targetDistance =
        (settings.positiveTargetBase +
          settings.distanceScale * (1 - Math.min(1, edge.weight))) *
        (edge.selection ? 0.25 : edge.semantic ? 0.35 : 1);
      const coefficient =
        (2 * Math.max(0.08, positiveWeight) *
          (currentDistance - targetDistance)) /
        currentDistance;
      movePair(edge.source, edge.target, coefficient, rate, 1.5);
    }
    const negativeScale =
      settings.negativeWeight *
      Math.max(0.25, model.edges.length / Math.max(1, negatives.length));
    const negativeStart =
      negatives.length > 0 ? (epoch * 130363) % negatives.length : 0;
    for (let step = 0; step < negatives.length; step += 1) {
      const [source, target, componentSeparation] =
        negatives[(negativeStart + step) % negatives.length];
      const currentDistance = Math.max(
        1e-4,
        Math.hypot(x[source] - x[target], y[source] - y[target]),
      );
      if (currentDistance >= settings.distanceScale) continue;
      const coefficient =
        (-2 *
          negativeScale *
          componentSeparation *
          (settings.distanceScale - currentDistance)) /
        currentDistance;
      movePair(source, target, coefficient, rate, 0.75);
    }
    for (const hyperedge of model.factualHyperedges) {
      let centroidX = 0;
      let centroidY = 0;
      for (const member of hyperedge.members) {
        centroidX += x[member];
        centroidY += y[member];
      }
      centroidX /= hyperedge.members.length;
      centroidY /= hyperedge.members.length;
      const factor = Math.min(0.08, rate * hyperedge.weight);
      for (const member of hyperedge.members) {
        x[member] += (centroidX - x[member]) * factor;
        y[member] += (centroidY - y[member]) * factor;
      }
    }
    let meanX = 0;
    let meanY = 0;
    for (let index = 0; index < population; index += 1) {
      meanX += x[index];
      meanY += y[index];
    }
    meanX /= Math.max(1, population);
    meanY /= Math.max(1, population);
    for (let index = 0; index < population; index += 1) {
      x[index] -= meanX;
      y[index] -= meanY;
    }
  }
  return {x, y};
}

function stableInitialCoordinates(model: SparseAffinityModel) {
  const x = new Float64Array(model.specificationNodes.length);
  const y = new Float64Array(model.specificationNodes.length);
    const order = Array.from(
      {length: model.specificationNodes.length},
      (_, index) => index,
    ).sort(
      (left, right) =>
        stableHash(`stable-rank\u0000${model.specificationNodes[left].id}`) -
        stableHash(`stable-rank\u0000${model.specificationNodes[right].id}`),
    );
    const goldenAngle = Math.PI * (3 - Math.sqrt(5));
    for (let rank = 0; rank < order.length; rank += 1) {
      const index = order[rank];
      const radius =
        Math.sqrt((rank + 0.5) / Math.max(1, order.length)) * 10;
      const angle = rank * goldenAngle;
      x[index] = Math.cos(angle) * radius;
      y[index] = Math.sin(angle) * radius;
    }
  return {x, y};
}

function optimizeCrossEntropySgd(
  model: SparseAffinityModel,
  settings: ObjectiveSettings,
) {
  const initial = settings.stableInitialization
    ? stableInitialCoordinates(model)
    : initialAffinityCoordinates(model, settings, {
        edgeWeight: (edge) => positiveAffinityWeight(edge, settings),
      });
  const {x, y} = initial;
  const population = model.specificationNodes.length;
  let meanSquaredRadius = 0;
  for (let index = 0; index < population; index += 1) {
    meanSquaredRadius += x[index] * x[index] + y[index] * y[index];
  }
  const initialScale =
    Math.sqrt(meanSquaredRadius / Math.max(1, population)) / 10;
  if (initialScale > 1e-9) {
    for (let index = 0; index < population; index += 1) {
      x[index] /= initialScale;
      y[index] /= initialScale;
    }
  }
  const anchorX =
    (settings.anchorWeight ?? 0) > 0 ? x.slice() : undefined;
  const anchorY =
    (settings.anchorWeight ?? 0) > 0 ? y.slice() : undefined;
  const movePair = (
    source: number,
    target: number,
    coefficient: number,
    rate: number,
    maximumStep: number,
  ) => {
    let dx = x[source] - x[target];
    let dy = y[source] - y[target];
    let squared = dx * dx + dy * dy;
    if (squared < 1e-8) {
      const angle =
        (stableHash(
          `ce-coincident\u0000${model.specificationNodes[source].id}\u0000${model.specificationNodes[target].id}`,
        ) /
          4294967296) *
        Math.PI *
        2;
      dx = Math.cos(angle) * 1e-4;
      dy = Math.sin(angle) * 1e-4;
      squared = 1e-8;
    }
    let moveX = rate * coefficient * dx;
    let moveY = rate * coefficient * dy;
    const magnitude = Math.hypot(moveX, moveY);
    if (magnitude > maximumStep) {
      moveX *= maximumStep / magnitude;
      moveY *= maximumStep / magnitude;
    }
    x[source] -= moveX;
    y[source] -= moveY;
    x[target] += moveX;
    y[target] += moveY;
  };

  const scaleSquared = settings.distanceScale * settings.distanceScale;
  const optimizationEdges = settings.stableOptimizationOrder
    ? [...model.edges].sort((left, right) => {
        const leftIdentity =
          `${model.specificationNodes[left.source].id}\u0000` +
          model.specificationNodes[left.target].id;
        const rightIdentity =
          `${model.specificationNodes[right.source].id}\u0000` +
          model.specificationNodes[right.target].id;
        return stableHash(leftIdentity) - stableHash(rightIdentity);
      })
    : model.edges;
  for (let epoch = 0; epoch < settings.epochs; epoch += 1) {
    const cooling = 0.05 + 0.95 * (1 - epoch / settings.epochs);
    const rate = settings.learningRate * cooling;
    const start =
      !settings.stableOptimizationOrder && optimizationEdges.length > 0
        ? (epoch * 104729) % optimizationEdges.length
        : 0;
    for (let step = 0; step < optimizationEdges.length; step += 1) {
      const orderedStep =
        settings.stableOptimizationOrder && epoch % 2 === 1
          ? optimizationEdges.length - 1 - step
          : step;
      const edge =
        optimizationEdges[(start + orderedStep) % optimizationEdges.length];
      const dx = x[edge.source] - x[edge.target];
      const dy = y[edge.source] - y[edge.target];
      const squared = Math.max(1e-8, dx * dx + dy * dy);
      const positiveWeight = positiveAffinityWeight(edge, settings);
      // Persisted semantic and selection Edges are direct evidence. When the
      // composite objective is enabled, give them a quadratic distance term
      // whose gradient remains informative at long range; inferred factual
      // neighborhoods retain fuzzy cross-entropy. Both terms are optimized in
      // this same pass and produce one set of Node coordinates.
      const attraction =
        settings.directStress && (edge.semantic || edge.selection)
          ? (2 * positiveWeight) / scaleSquared
          : (2 * positiveWeight) / (scaleSquared + squared);
      movePair(edge.source, edge.target, attraction, rate, 2);

      for (let sample = 0; sample < settings.negativeSamples; sample += 1) {
        let negativeTarget =
          stableHash(
            `ce-negative\u0000${epoch}\u0000${sample}\u0000${model.specificationNodes[edge.source].id}\u0000${model.specificationNodes[edge.target].id}`,
          ) % population;
        for (let attempt = 0; attempt < population; attempt += 1) {
          if (
            negativeTarget !== edge.source &&
            !model.adjacency[edge.source].has(negativeTarget)
          ) {
            break;
          }
          negativeTarget = (negativeTarget + 1) % population;
        }
        if (
          negativeTarget === edge.source ||
          model.adjacency[edge.source].has(negativeTarget)
        ) {
          continue;
        }
        const negativeDx = x[edge.source] - x[negativeTarget];
        const negativeDy = y[edge.source] - y[negativeTarget];
        const negativeSquared = Math.max(
          1e-4,
          negativeDx * negativeDx + negativeDy * negativeDy,
        );
        const repulsion =
          (-2 * settings.negativeWeight * scaleSquared) /
          (negativeSquared * (scaleSquared + negativeSquared));
        movePair(edge.source, negativeTarget, repulsion, rate, 2);
      }
    }
    let meanX = 0;
    let meanY = 0;
    for (let index = 0; index < population; index += 1) {
      if (anchorX && anchorY) {
        const anchorStep = Math.min(
          1,
          rate * 2 * (settings.anchorWeight ?? 0),
        );
        x[index] += (anchorX[index] - x[index]) * anchorStep;
        y[index] += (anchorY[index] - y[index]) * anchorStep;
      }
      meanX += x[index];
      meanY += y[index];
    }
    meanX /= Math.max(1, population);
    meanY /= Math.max(1, population);
    for (let index = 0; index < population; index += 1) {
      x[index] -= meanX;
      y[index] -= meanY;
    }
  }
  return {x, y};
}

function optimize(
  family: ObjectiveFamily,
  model: SparseAffinityModel,
  settings: ObjectiveSettings,
) {
  if (settings.optimizer === "sgd" && family === "contrastive-stress") {
    return optimizeContrastiveSgd(model, settings);
  }
  if (
    settings.optimizer === "cross-entropy-sgd" &&
    family === "neighborhood-cross-entropy"
  ) {
    return optimizeCrossEntropySgd(model, settings);
  }
  const population = model.specificationNodes.length;
  const anchors =
    (settings.anchorWeight ?? 0) > 0
      ? stableInitialCoordinates(model)
      : undefined;
  const {x, y} =
    anchors ??
    initialAffinityCoordinates(model, settings, {
      edgeWeight: (edge) => positiveAffinityWeight(edge, settings),
    });
  const negatives = negativePairs(model, settings.negativeSamples);
  const firstMomentX = new Float64Array(population);
  const firstMomentY = new Float64Array(population);
  const secondMomentX = new Float64Array(population);
  const secondMomentY = new Float64Array(population);
  const beta1 = 0.9;
  const beta2 = 0.999;
  const epsilon = 1e-7;

  for (let epoch = 1; epoch <= settings.epochs; epoch += 1) {
    const gradientX = new Float64Array(population);
    const gradientY = new Float64Array(population);
    for (const edge of model.edges) {
      const positiveWeight = positiveAffinityWeight(edge, settings);
      let dx = x[edge.source] - x[edge.target];
      let dy = y[edge.source] - y[edge.target];
      let squared = dx * dx + dy * dy;
      if (squared < 1e-8) {
        const angle =
          (stableHash(
            `coincident\u0000${model.specificationNodes[edge.source].id}\u0000${model.specificationNodes[edge.target].id}`,
          ) /
            4294967296) *
          Math.PI *
          2;
        dx = Math.cos(angle) * 1e-4;
        dy = Math.sin(angle) * 1e-4;
        squared = 1e-8;
      }
      const currentDistance = Math.sqrt(squared);
      let coefficient = 0;
      if (family === "weighted-linlog") {
        // d/dx [w * ||x_i-x_j||]
        coefficient = positiveWeight / currentDistance;
      } else if (family === "neighborhood-cross-entropy") {
        if (settings.directStress && (edge.semantic || edge.selection)) {
          // Exact direct-relation distance term in the same composite energy.
          coefficient =
            (2 * positiveWeight) /
            (settings.distanceScale * settings.distanceScale);
        } else {
          // Attractive half of fuzzy-set cross entropy with
          // q(d)=1/(1+d²/s²).
          coefficient =
            (2 * positiveWeight) /
            (settings.distanceScale * settings.distanceScale + squared);
        }
      } else {
        const targetDistance =
          (settings.positiveTargetBase +
            settings.distanceScale * (1 - Math.min(1, edge.weight))) *
          (edge.selection ? 0.25 : edge.semantic ? 0.35 : 1);
        coefficient =
          (2 * Math.max(0.08, positiveWeight) *
            (currentDistance - targetDistance)) /
          currentDistance;
      }
      addPairGradient(
        gradientX,
        gradientY,
        edge.source,
        edge.target,
        coefficient,
        dx,
        dy,
      );
    }

    // Exact variance term for broad persisted hyperedges. This preserves a
    // factual parent-scale relation without constructing or arranging a
    // community. A universal feature has zero information weight upstream.
    for (const hyperedge of model.factualHyperedges) {
      let centroidX = 0;
      let centroidY = 0;
      for (const member of hyperedge.members) {
        centroidX += x[member];
        centroidY += y[member];
      }
      centroidX /= hyperedge.members.length;
      centroidY /= hyperedge.members.length;
      const coefficient = 2 * hyperedge.weight;
      for (const member of hyperedge.members) {
        gradientX[member] += coefficient * (x[member] - centroidX);
        gradientY[member] += coefficient * (y[member] - centroidY);
      }
    }

    const negativeScale =
      settings.negativeWeight *
      Math.max(0.25, model.edges.length / Math.max(1, negatives.length));
    for (const [source, target, componentSeparation] of negatives) {
      if (
        anchors &&
        model.adjacency[source].size === 0 &&
        model.adjacency[target].size === 0
      ) {
        continue;
      }
      let dx = x[source] - x[target];
      let dy = y[source] - y[target];
      let squared = dx * dx + dy * dy;
      if (squared < 1e-8) {
        const angle =
          (stableHash(
            `negative-coincident\u0000${model.specificationNodes[source].id}\u0000${model.specificationNodes[target].id}`,
          ) /
            4294967296) *
          Math.PI *
          2;
        dx = Math.cos(angle) * 1e-4;
        dy = Math.sin(angle) * 1e-4;
        squared = 1e-8;
      }
      const currentDistance = Math.sqrt(squared);
      let coefficient = 0;
      if (family === "weighted-linlog") {
        // d/dx [-lambda * log(||x_i-x_j||)]
        coefficient = (-negativeScale * componentSeparation) / squared;
      } else if (family === "neighborhood-cross-entropy") {
        const scaleSquared = settings.distanceScale * settings.distanceScale;
        // Repulsive half of the same cross entropy.
        coefficient =
          2 *
          negativeScale *
          componentSeparation *
          (1 / (scaleSquared + squared) - 1 / squared);
      } else if (currentDistance < settings.distanceScale) {
        coefficient =
          (-2 *
            negativeScale *
            componentSeparation *
            (settings.distanceScale - currentDistance)) /
          currentDistance;
      }
      addPairGradient(
        gradientX,
        gradientY,
        source,
        target,
        coefficient,
        dx,
        dy,
      );
    }

    // A very weak radial term fixes translation and prevents unconstrained
    // components from diverging. It is part of every declared objective.
    const gravity = 1e-4;
    for (let index = 0; index < population; index += 1) {
      gradientX[index] += gravity * x[index];
      gradientY[index] += gravity * y[index];
      if (anchors) {
        gradientX[index] +=
          2 * (settings.anchorWeight ?? 0) * (x[index] - anchors.x[index]);
        gradientY[index] +=
          2 * (settings.anchorWeight ?? 0) * (y[index] - anchors.y[index]);
      }
    }

    const biasCorrection1 = 1 - Math.pow(beta1, epoch);
    const biasCorrection2 = 1 - Math.pow(beta2, epoch);
    const cooling = 0.15 + 0.85 * (1 - (epoch - 1) / settings.epochs);
    for (let index = 0; index < population; index += 1) {
      const gx = Math.max(-50, Math.min(50, gradientX[index]));
      const gy = Math.max(-50, Math.min(50, gradientY[index]));
      firstMomentX[index] = beta1 * firstMomentX[index] + (1 - beta1) * gx;
      firstMomentY[index] = beta1 * firstMomentY[index] + (1 - beta1) * gy;
      secondMomentX[index] =
        beta2 * secondMomentX[index] + (1 - beta2) * gx * gx;
      secondMomentY[index] =
        beta2 * secondMomentY[index] + (1 - beta2) * gy * gy;
      x[index] -=
        settings.learningRate *
        cooling *
        (firstMomentX[index] / biasCorrection1) /
        (Math.sqrt(secondMomentX[index] / biasCorrection2) + epsilon);
      y[index] -=
        settings.learningRate *
        cooling *
        (firstMomentY[index] / biasCorrection1) /
        (Math.sqrt(secondMomentY[index] / biasCorrection2) + epsilon);
    }
  }
  return {x, y};
}

function normalizePresentationScale(x: Float64Array, y: Float64Array) {
  const population = x.length;
  if (population === 0) return;
  let meanX = 0;
  let meanY = 0;
  for (let index = 0; index < population; index += 1) {
    meanX += x[index];
    meanY += y[index];
  }
  meanX /= population;
  meanY /= population;
  for (let index = 0; index < population; index += 1) {
    x[index] -= meanX;
    y[index] -= meanY;
  }
  const sampled = Array.from(
    {length: Math.min(512, population)},
    (_, sample) => Math.floor((sample * population) / Math.min(512, population)),
  );
  const nearest: number[] = [];
  for (const index of sampled) {
    let best = Number.POSITIVE_INFINITY;
    for (let other = 0; other < population; other += 1) {
      if (other === index) continue;
      best = Math.min(best, Math.hypot(x[index] - x[other], y[index] - y[other]));
    }
    if (Number.isFinite(best) && best > 1e-9) nearest.push(best);
  }
  nearest.sort((left, right) => left - right);
  const median = nearest[Math.floor(nearest.length / 2)] ?? 1;
  const scale = 9 / Math.max(1e-6, median);
  for (let index = 0; index < population; index += 1) {
    x[index] *= scale;
    y[index] *= scale;
  }
}

function connectorCoordinates(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  model: SparseAffinityModel,
  x: Float64Array,
  y: Float64Array,
) {
  const incident = new Map<string, number[]>();
  for (const edge of edges) {
    const source = model.specificationIndex.get(edge.source);
    const target = model.specificationIndex.get(edge.target);
    if (source !== undefined && target === undefined) {
      const values = incident.get(edge.target) ?? [];
      values.push(source);
      incident.set(edge.target, values);
    } else if (target !== undefined && source === undefined) {
      const values = incident.get(edge.source) ?? [];
      values.push(target);
      incident.set(edge.source, values);
    }
  }
  const result = new Map<string, {x: number; y: number}>();
  for (const node of nodes) {
    const index = model.specificationIndex.get(node.id);
    if (index !== undefined) {
      result.set(node.id, {x: x[index], y: y[index]});
      continue;
    }
    const values = incident.get(node.id) ?? [];
    result.set(node.id, {
      x:
        values.length > 0
          ? values.reduce((sum, value) => sum + x[value], 0) / values.length
          : 0,
      y:
        values.length > 0
          ? values.reduce((sum, value) => sum + y[value], 0) / values.length
          : 0,
    });
  }
  return result;
}

export function layoutWithObjective(
  family: ObjectiveFamily,
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  overrides: Partial<ObjectiveSettings> = {},
): SpecificationLayoutResult {
  const settings = {...SETTINGS[family], ...overrides};
  const model = buildSparseAffinity(
    nodes,
    edges,
    settings.neighborBudget ?? 32,
    settings.stableScaleRetention
      ? "stable-multiscale"
      : settings.multiscaleRetention
        ? "multiscale"
        : "strongest",
    settings.strongestReserve ?? 4,
  );
  const {x, y} = optimize(family, model, settings);
  normalizePresentationScale(x, y);
  const coordinates = connectorCoordinates(nodes, edges, model, x, y);
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const point = coordinates.get(nodes[index].id) ?? {x: 0, y: 0};
    positions[index * 3] = point.x;
    positions[index * 3 + 1] = point.y;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: nodes.map((node) => node.id),
    positions,
    featureCount: model.featureCount,
    routeCount: model.routeCount,
    iterations: settings.epochs,
  };
}
