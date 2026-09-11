import {layoutSpecificationGraph as layoutFailedBaseline} from "./failed-layout";
import {layoutSpecificationGraph as layoutProductionSpecificationGraph} from "../lib/specification-layout";
import {layoutWithObjective} from "./objective-layout";
import {layoutWithForceAtlas2} from "./forceatlas-layout";
import {layoutWithMultiscaleStress} from "./multiscale-stress-layout";
import {layoutWithFeatureProjection} from "./feature-projection-layout";
import {layoutWithAnchoredLaplacian} from "./anchored-laplacian-layout";
import {layoutWithRobustSpectral} from "./robust-spectral-layout";
import type {LayoutCandidate} from "./types";

export const failedBaselineCandidate: LayoutCandidate = {
  id: "failed-baseline",
  description:
    "Spectral initialization followed by centroid attraction and uniform local packing; frozen as the rejected oval baseline.",
  layout: (nodes, edges) => layoutFailedBaseline(nodes, edges),
};

export const productionEvidenceCandidate: LayoutCandidate = {
  id: "production-evidence",
  description:
    "The production single-objective evidence-concentration XY layout.",
  layout: (nodes, edges) => layoutProductionSpecificationGraph(nodes, edges),
};

export const weightedLinLogCandidate: LayoutCandidate = {
  id: "weighted-linlog",
  description:
    "One weighted LinLog energy: factual attraction and fixed deterministic non-edge logarithmic repulsion.",
  layout: (nodes, edges) => layoutWithObjective("weighted-linlog", nodes, edges),
};

export const neighborhoodCrossEntropyCandidate: LayoutCandidate = {
  id: "neighborhood-cross-entropy",
  description:
    "One fuzzy-neighborhood cross-entropy objective over factual affinities and deterministic non-edges.",
  layout: (nodes, edges) =>
    layoutWithObjective("neighborhood-cross-entropy", nodes, edges),
};

export const contrastiveStressCandidate: LayoutCandidate = {
  id: "contrastive-stress",
  description:
    "One weighted target-distance stress objective with a non-edge margin term.",
  layout: (nodes, edges) =>
    layoutWithObjective("contrastive-stress", nodes, edges),
};

export const contrastiveSgdCandidate: LayoutCandidate = {
  id: "contrastive-stress-sgd",
  description:
    "The same single contrastive-stress objective optimized by deterministic per-constraint SGD.",
  layout: (nodes, edges) =>
    layoutWithObjective("contrastive-stress", nodes, edges, {
      optimizer: "sgd",
      epochs: 420,
      learningRate: 0.012,
      semanticBoost: 16,
      selectionBoost: 24,
      positiveTargetBase: 6,
    }),
};

export const normalizedSpectralCandidate: LayoutCandidate = {
  id: "normalized-spectral",
  description:
    "One normalized affinity spectral objective with no force or post-layout correction.",
  layout: (nodes, edges) =>
    layoutWithObjective("contrastive-stress", nodes, edges, {
      epochs: 0,
      semanticBoost: 16,
      selectionBoost: 24,
    }),
};

export const neighborhoodCrossEntropySgdCandidate: LayoutCandidate = {
  id: "neighborhood-cross-entropy-sgd",
  description:
    "One fuzzy-neighborhood cross-entropy objective optimized by deterministic positive-edge SGD and negative sampling.",
  layout: (nodes, edges) =>
    layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
      optimizer: "cross-entropy-sgd",
      epochs: 240,
      learningRate: 0.7,
      negativeSamples: 2,
      negativeWeight: 1,
      distanceScale: 1,
      semanticBoost: 12,
      selectionBoost: 18,
    }),
};

const featureProjectionCandidates: LayoutCandidate[] = [0.5, 1, 1.5].map(
  (informationExponent) => ({
    id: `feature-projection-i${informationExponent}`,
    description:
      `One closed-form deterministic weighted-feature projection ` +
      `(information exponent=${informationExponent}).`,
    layout: (nodes, edges) =>
      layoutWithFeatureProjection(nodes, edges, {
        degreeExponent: 0.5,
        informationExponent,
      }),
  }),
);

const anchoredLaplacianCandidates: LayoutCandidate[] = [0.05, 0.1, 0.2, 0.5, 2, 8].map(
  (anchorWeight) => ({
    id: `anchored-laplacian-a${anchorWeight}`,
    description:
      `One strictly convex affinity-plus-statement-grid quadratic energy ` +
      `(anchor=${anchorWeight}).`,
    layout: (nodes, edges) =>
      layoutWithAnchoredLaplacian(nodes, edges, {anchorWeight}),
  }),
);

const anchoredLaplacianSparseCandidates: LayoutCandidate[] = [0.2, 0.5, 1].map(
  (anchorWeight) => ({
    id: `anchored-laplacian-sparse-a${anchorWeight}`,
    description:
      `One strictly convex sparse affinity-plus-statement-grid energy ` +
      `(anchor=${anchorWeight}, strongest=2, multiscale=2).`,
    layout: (nodes, edges) =>
      layoutWithAnchoredLaplacian(nodes, edges, {
        anchorWeight,
        neighborBudget: 4,
        strongestReserve: 2,
      }),
  }),
);

const anchoredLaplacianHashCandidates: LayoutCandidate[] = [
  {anchorWeight: 0.01, localBoost: 1},
  {anchorWeight: 0.03, localBoost: 1},
  {anchorWeight: 0.1, localBoost: 1},
  {anchorWeight: 0.03, localBoost: 4},
  {anchorWeight: 0.1, localBoost: 4},
].map(({anchorWeight, localBoost}) => ({
  id: `anchored-laplacian-hash-a${anchorWeight}-l${localBoost}`,
  description:
    `One strictly convex affinity-plus-stable-hash quadratic energy ` +
    `(anchor=${anchorWeight}, local=${localBoost}).`,
  layout: (nodes, edges) =>
    layoutWithAnchoredLaplacian(nodes, edges, {
      anchorWeight,
      anchorMode: "stable-hash",
      localBoost,
    }),
}));

const anchoredLaplacianFeatureCandidates: LayoutCandidate[] = [
  {anchorWeight: 0.01, localBoost: 1},
  {anchorWeight: 0.03, localBoost: 1},
  {anchorWeight: 0.1, localBoost: 1},
  {anchorWeight: 0.3, localBoost: 1},
  {anchorWeight: 0.1, localBoost: 4},
].map(({anchorWeight, localBoost}) => ({
  id: `anchored-laplacian-feature-a${anchorWeight}-l${localBoost}`,
  description:
    `One strictly convex affinity-plus-feature-projection quadratic energy ` +
    `(anchor=${anchorWeight}, local=${localBoost}).`,
  layout: (nodes, edges) =>
    layoutWithAnchoredLaplacian(nodes, edges, {
      anchorWeight,
      anchorMode: "feature-projection",
      localBoost,
    }),
}));

const finiteDiffusionCandidates: LayoutCandidate[] = [
  1,
  2,
  4,
  8,
  12,
  16,
  20,
  24,
  32,
  48,
  64,
  96,
  128,
].flatMap(
  (iterations) =>
    [0.01, 0.02, 0.03, 0.05, 0.1, 0.2, 0.5, 1].map((anchorWeight) => ({
      id: `finite-diffusion-i${iterations}-a${anchorWeight}`,
      description:
        `One finite deterministic affinity diffusion from a stable uniform ` +
        `disk (iterations=${iterations}, restart=${anchorWeight}).`,
      layout: (nodes, edges) =>
        layoutWithAnchoredLaplacian(nodes, edges, {
          iterations,
          anchorWeight,
          anchorMode: "stable-hash",
          localBoost: 1,
        }),
    })),
);

const robustSpectralCandidates: LayoutCandidate[] = [32, 48, 64].flatMap(
  (neighborBudget) =>
    [1, 2, 4].map((directWeight) => ({
      id: `robust-spectral-k${neighborBudget}-d${directWeight}`,
      description:
        `One normalized spectral objective over direct plus shared-neighbor ` +
        `diffusion affinity (k=${neighborBudget}, direct=${directWeight}).`,
      layout: (nodes, edges) =>
        layoutWithRobustSpectral(nodes, edges, {neighborBudget, directWeight}),
    })),
);

const neighborhoodCrossEntropyFastCandidates: LayoutCandidate[] = [40, 80].flatMap(
  (epochs) =>
    [24, 48, 96].map((semanticBoost) => ({
      id: `neighborhood-ce-fast-e${epochs}-s${semanticBoost}`,
      description:
        `Tuning-only fuzzy-neighborhood cross-entropy variant ` +
        `(epochs=${epochs}, semantic=${semanticBoost}).`,
      layout: (nodes, edges) =>
        layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
          optimizer: "cross-entropy-sgd",
          epochs,
          learningRate: 0.7,
          negativeSamples: 1,
          negativeWeight: 1,
          distanceScale: 1,
          semanticBoost,
          selectionBoost: semanticBoost * 1.5,
        }),
    })),
);

const contrastiveTuningSettings = [
  {id: "contrastive-s8-t4", semanticBoost: 8, positiveTargetBase: 4},
  {id: "contrastive-s12-t4", semanticBoost: 12, positiveTargetBase: 4},
  {id: "contrastive-s12-t6", semanticBoost: 12, positiveTargetBase: 6},
  {id: "contrastive-s16-t4", semanticBoost: 16, positiveTargetBase: 4},
  {id: "contrastive-s16-t6", semanticBoost: 16, positiveTargetBase: 6},
  {id: "contrastive-s16-t8", semanticBoost: 16, positiveTargetBase: 8},
  {id: "contrastive-s20-t6", semanticBoost: 20, positiveTargetBase: 6},
  {id: "contrastive-s24-t8", semanticBoost: 24, positiveTargetBase: 8},
  {id: "contrastive-s32-t6", semanticBoost: 32, positiveTargetBase: 6},
  {id: "contrastive-s32-t10", semanticBoost: 32, positiveTargetBase: 10},
  {id: "contrastive-s48-t8", semanticBoost: 48, positiveTargetBase: 8},
  {id: "contrastive-s64-t6", semanticBoost: 64, positiveTargetBase: 6},
  {id: "contrastive-s128-t6", semanticBoost: 128, positiveTargetBase: 6},
] as const;
const contrastiveTuningCandidates: LayoutCandidate[] = contrastiveTuningSettings.map(
  ({id, semanticBoost, positiveTargetBase}) => ({
  id,
  description: `Tuning-only contrastive stress variant (semantic=${semanticBoost}, targetBase=${positiveTargetBase}).`,
  layout: (nodes, edges) =>
    layoutWithObjective("contrastive-stress", nodes, edges, {
      semanticBoost,
      selectionBoost: semanticBoost * 1.5,
      positiveTargetBase,
    }),
  }),
);

export const forceAtlasLinLogCandidate: LayoutCandidate = {
  id: "forceatlas2-linlog",
  description:
    "Graphology ForceAtlas2 with Barnes-Hut repulsion, hub-dissuasion, weighted edges, and one LinLog energy.",
  layout: layoutWithForceAtlas2,
};

export const forceAtlasLinearCandidate: LayoutCandidate = {
  id: "forceatlas2-linear",
  description:
    "Graphology ForceAtlas2 linear attraction with Barnes-Hut repulsion and factual edge weights.",
  layout: (nodes, edges) =>
    layoutWithForceAtlas2(nodes, edges, {
      linLogMode: false,
      iterations: 1_000,
      scalingRatio: 4,
    }),
};

export const forceAtlasStableCandidate: LayoutCandidate = {
  id: "forceatlas2-stable-budget16",
  description:
    "One sparse ForceAtlas2 energy from a graph-independent deterministic initialization.",
  layout: (nodes, edges) =>
    layoutWithForceAtlas2(nodes, edges, {
      linLogMode: false,
      iterations: 125,
      scalingRatio: 4,
      semanticBoost: 24,
      selectionBoost: 36,
      slowDown: 1.5,
      gravity: 0,
      strongGravityMode: false,
      includeFactualHyperedges: false,
      broadFactualBoost: 32,
      edgeWeightInfluence: 1.1,
      neighborBudget: 16,
      stableInitialization: true,
    }),
};

const forceAtlasStatementGridCandidates: LayoutCandidate[] = [40, 80, 125].map(
  (iterations) => ({
    id: `forceatlas2-statement-grid-i${iterations}`,
    description:
      `One sparse ForceAtlas2 energy from a deterministic statement-ordered ` +
      `grid (${iterations} iterations).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
        stableInitialization: "statement-grid",
      }),
  }),
);

const forceAtlasScaffoldCandidates: LayoutCandidate[] = [80, 125].flatMap(
  (iterations) =>
    [0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10].map((scaffoldWeight) => ({
      id: `forceatlas2-scaffold-i${iterations}-w${scaffoldWeight}`,
      description:
        `One ForceAtlas2 energy with a uniform context-free lattice ` +
        `regularizer (iterations=${iterations}, scaffold=${scaffoldWeight}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio: 4,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost: 32,
          edgeWeightInfluence: 1.1,
          neighborBudget: 16,
          stableInitialization: "uniform-grid",
          scaffoldWeight,
        }),
    })),
);

const forceAtlasStatementScaffoldCandidates: LayoutCandidate[] = [80, 125].flatMap(
  (iterations) =>
    [0.003, 0.01, 0.03, 0.1, 0.3, 1].map((scaffoldWeight) => ({
      id: `forceatlas2-statement-scaffold-i${iterations}-w${scaffoldWeight}`,
      description:
        `One ForceAtlas2 energy with a statement-ordered uniform lattice ` +
        `regularizer (iterations=${iterations}, scaffold=${scaffoldWeight}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio: 4,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost: 32,
          edgeWeightInfluence: 1.1,
          neighborBudget: 16,
          stableInitialization: "statement-grid",
          scaffoldWeight,
        }),
    })),
);

export const multiscaleStressCandidate: LayoutCandidate = {
  id: "multiscale-rest-stress",
  description:
    "One weighted stress-force objective with feature-degree rest distances and non-edge repulsion.",
  layout: layoutWithMultiscaleStress,
};

const multiscaleStressTuningCandidates: LayoutCandidate[] = [
  {broadStrength: 0.015, localStrength: 0.18},
  {broadStrength: 0.02, localStrength: 0.22},
  {broadStrength: 0.025, localStrength: 0.22},
  {broadStrength: 0.03, localStrength: 0.22},
  {broadStrength: 0.02, localStrength: 0.3},
].map(({broadStrength, localStrength}) => ({
  id: `multiscale-stress-b${broadStrength}-l${localStrength}`,
  description:
    `Tuning-only finite-rest stress strength variant ` +
    `(broad=${broadStrength}, local=${localStrength}).`,
  layout: (nodes, edges) =>
    layoutWithMultiscaleStress(nodes, edges, {
      broadStrength,
      localStrength,
    }),
}));

const multiscaleStressIterationCandidates: LayoutCandidate[] = [0, 30, 60, 90, 120].map(
  (iterations) => ({
    id: `multiscale-stress-i${iterations}`,
    description:
      `Diagnostic finite-rest stress convergence variant ` +
      `(iterations=${iterations}).`,
    layout: (nodes, edges) =>
      layoutWithMultiscaleStress(nodes, edges, {
        iterations,
        broadStrength: 0.015,
        localStrength: 0.18,
      }),
  }),
);

const evidenceLandscapeCandidates: LayoutCandidate[] = [
  {viewEvidenceScale: 0.12},
  {viewEvidenceScale: 0.18},
  {viewEvidenceScale: 0.25},
].map(({viewEvidenceScale}) => ({
  id: `evidence-landscape-contrast-v${viewEvidenceScale}`,
  description:
    `One multiscale evidence stress energy with exact broad factual ` +
    `hyperedges and nonlinear view evidence (view scale=${viewEvidenceScale}).`,
  layout: (nodes, edges) =>
    layoutWithMultiscaleStress(nodes, edges, {
      iterations: 120,
      localStrength: 0.35,
      radialStrength: 0.003,
      broadHyperedgeStrength: 0.75,
      removeSyntheticBroadPairs: true,
      stableInitialization: true,
      localStrengthCeiling: 0.6,
      velocityDecay: 0.6,
      repulsionStrength: -14,
      affinityExponent: 1.8,
      viewEvidenceScale,
      viewEvidenceExponent: 3,
    }),
}));

const statementGridStressCandidates: LayoutCandidate[] = [0.01, 0.03, 0.08].map(
  (statementGridAnchorStrength) => ({
    id: `statement-grid-stress-a${statementGridAnchorStrength}`,
    description:
      `One finite-rest affinity energy with weak statement-grid ` +
      `regularization (anchor=${statementGridAnchorStrength}).`,
    layout: (nodes, edges) =>
      layoutWithMultiscaleStress(nodes, edges, {
        iterations: 120,
        broadStrength: 0.015,
        localStrength: 0.18,
        statementGridAnchorStrength,
      }),
  }),
);

const forceAtlasLinearFastCandidates: LayoutCandidate[] = [100, 200, 300, 500].map(
  (iterations) => ({
    id: `forceatlas2-linear-${iterations}`,
    description: `Tuning-only ForceAtlas2 linear variant (${iterations} iterations).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations,
        scalingRatio: 4,
      }),
  }),
);

const forceAtlasLinearTuningCandidates: LayoutCandidate[] = [100, 200].flatMap(
  (iterations) =>
    [24, 48, 96].flatMap((semanticBoost) =>
      [1.5, 3, 6].map((slowDown) => ({
        id: `forceatlas2-linear-i${iterations}-s${semanticBoost}-d${slowDown}`,
        description:
          `Tuning-only ForceAtlas2 linear variant ` +
          `(iterations=${iterations}, semantic=${semanticBoost}, slowDown=${slowDown}).`,
        layout: (nodes, edges) =>
          layoutWithForceAtlas2(nodes, edges, {
            linLogMode: false,
            iterations,
            scalingRatio: 4,
            semanticBoost,
            selectionBoost: semanticBoost * 1.5,
            slowDown,
          }),
      })),
  ),
);

const neighborhoodCompositeCandidates: LayoutCandidate[] = [6, 12, 24].map(
  (semanticBoost) => ({
    id: `neighborhood-composite-s${semanticBoost}`,
    description:
      `One composite neighborhood energy: fuzzy inferred affinity plus ` +
      `quadratic direct-relation stress (semantic=${semanticBoost}).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        optimizer: "cross-entropy-sgd",
        epochs: 40,
        learningRate: 0.7,
        negativeSamples: 1,
        negativeWeight: 1,
        distanceScale: 1,
        semanticBoost,
        selectionBoost: semanticBoost * 1.5,
        directStress: true,
      }),
  }),
);

const neighborhoodCompositeMultiscaleCandidates: LayoutCandidate[] = [4, 6, 8].map(
  (semanticBoost) => ({
    id: `neighborhood-composite-multiscale-s${semanticBoost}`,
    description:
      `One multiscale composite neighborhood energy ` +
      `(semantic=${semanticBoost}, strongest reserve=16).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        optimizer: "cross-entropy-sgd",
        epochs: 40,
        learningRate: 0.7,
        negativeSamples: 1,
        negativeWeight: 1,
        distanceScale: 1,
        semanticBoost,
        selectionBoost: semanticBoost * 1.5,
        directStress: true,
        neighborBudget: 32,
        multiscaleRetention: true,
        strongestReserve: 16,
      }),
  }),
);

const neighborhoodCompositeScaleCandidates: LayoutCandidate[] = [
  0.5,
  1,
  1.25,
  1.5,
  2,
  4,
].map(
  (broadFactualBoost) => ({
    id: `neighborhood-composite-scale-b${broadFactualBoost}`,
    description:
      `One scale-normalized multiscale composite neighborhood energy ` +
      `(broad=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        optimizer: "cross-entropy-sgd",
        epochs: 40,
        learningRate: 0.7,
        negativeSamples: 1,
        negativeWeight: 1,
        distanceScale: 1,
        semanticBoost: 4,
        selectionBoost: 6,
        directStress: true,
        neighborBudget: 32,
        multiscaleRetention: true,
        strongestReserve: 16,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
      }),
  }),
);

export const neighborhoodCompositeStableCandidate: LayoutCandidate = {
  id: "neighborhood-composite-stable",
  description:
    "One scale-normalized composite neighborhood energy with perturbation-stable SGD ordering.",
  layout: (nodes, edges) =>
    layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
      optimizer: "cross-entropy-sgd",
      epochs: 40,
      learningRate: 0.7,
      negativeSamples: 1,
      negativeWeight: 1,
      distanceScale: 1,
      semanticBoost: 4,
      selectionBoost: 6,
      directStress: true,
      neighborBudget: 32,
      multiscaleRetention: true,
      strongestReserve: 16,
      broadFactualBoost: 1.25,
      broadDegreeExponent: 0.5,
      stableOptimizationOrder: true,
    }),
};

const neighborhoodSeparatedScaleCandidates: LayoutCandidate[] = [1, 1.25, 1.5].map(
  (broadFactualBoost) => ({
    id: `neighborhood-separated-b${broadFactualBoost}`,
    description:
      `One composite neighborhood energy with separately normalized local ` +
      `and broad factual evidence (broad=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        optimizer: "cross-entropy-sgd",
        epochs: 40,
        learningRate: 0.7,
        negativeSamples: 1,
        negativeWeight: 1,
        distanceScale: 1,
        semanticBoost: 4,
        selectionBoost: 6,
        directStress: true,
        neighborBudget: 32,
        stableScaleRetention: true,
        strongestReserve: 16,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        separateScaleWeights: true,
        stableOptimizationOrder: true,
      }),
  }),
);

export const neighborhoodCompositeBatchCandidate: LayoutCandidate = {
  id: "neighborhood-composite-batch",
  description:
    "One scale-normalized composite neighborhood energy optimized by deterministic full-batch gradients.",
  layout: (nodes, edges) =>
    layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
      directStress: true,
      neighborBudget: 32,
      multiscaleRetention: true,
      strongestReserve: 16,
      broadFactualBoost: 1.25,
      broadDegreeExponent: 0.5,
    }),
};

const neighborhoodAnchoredBatchCandidates: LayoutCandidate[] = [0.1, 1, 10].map(
  (anchorWeight) => ({
    id: `neighborhood-anchored-a${anchorWeight}`,
    description:
      `One full-batch composite neighborhood energy with stable isotropic ` +
      `tie-breaking regularization (anchor=${anchorWeight}).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        directStress: true,
        neighborBudget: 32,
        multiscaleRetention: true,
        strongestReserve: 16,
        broadFactualBoost: 1.25,
        broadDegreeExponent: 0.5,
        anchorWeight,
      }),
  }),
);

const neighborhoodCompositeFixedInitCandidates: LayoutCandidate[] = [40, 80].map(
  (epochs) => ({
    id: `neighborhood-composite-fixed-e${epochs}`,
    description:
      `One scale-normalized composite neighborhood energy with ` +
      `graph-independent initialization (${epochs} epochs).`,
    layout: (nodes, edges) =>
      layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
        optimizer: "cross-entropy-sgd",
        epochs,
        learningRate: 0.7,
        negativeSamples: 1,
        negativeWeight: 1,
        distanceScale: 1,
        semanticBoost: 4,
        selectionBoost: 6,
        directStress: true,
        neighborBudget: 32,
        multiscaleRetention: true,
        strongestReserve: 16,
        broadFactualBoost: 1.25,
        broadDegreeExponent: 0.5,
        stableOptimizationOrder: true,
        stableInitialization: true,
      }),
  }),
);

const neighborhoodCompositeRegularizedCandidates: LayoutCandidate[] = [
  0.002,
  0.005,
  0.01,
  0.02,
  0.05,
  0.1,
].map((anchorWeight) => ({
  id: `neighborhood-composite-regularized-a${anchorWeight}`,
  description:
    `One scale-normalized neighborhood cross-entropy energy with stable ` +
    `isotropic quadratic regularization (anchor=${anchorWeight}).`,
  layout: (nodes, edges) =>
    layoutWithObjective("neighborhood-cross-entropy", nodes, edges, {
      optimizer: "cross-entropy-sgd",
      epochs: 40,
      learningRate: 0.7,
      negativeSamples: 1,
      negativeWeight: 1,
      distanceScale: 1,
      semanticBoost: 4,
      selectionBoost: 6,
      directStress: true,
      neighborBudget: 32,
      multiscaleRetention: true,
      strongestReserve: 16,
      broadFactualBoost: 1.25,
      broadDegreeExponent: 0.5,
      stableOptimizationOrder: true,
      stableInitialization: true,
      anchorWeight,
    }),
}));

const forceAtlasSparseTuningCandidates: LayoutCandidate[] = [30, 50, 75, 100, 150].map(
  (iterations) => ({
    id: `forceatlas2-sparse-${iterations}`,
    description:
      `Tuning-only ForceAtlas2 over the one sparse degree-normalized ` +
      `affinity graph (${iterations} iterations, no duplicate hub Nodes).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
      }),
  }),
);

const forceAtlasSparseGridCandidates: LayoutCandidate[] = [75, 100, 125].flatMap(
  (iterations) =>
    [32, 64, 128].map((broadFactualBoost) => ({
      id: `forceatlas2-sparse-i${iterations}-b${broadFactualBoost}`,
      description:
        `Tuning-only sparse ForceAtlas2 variant ` +
        `(iterations=${iterations}, broad=${broadFactualBoost}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio: 4,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost,
        }),
    })),
);

const forceAtlasSparseWeightCandidates: LayoutCandidate[] = [100, 125].flatMap(
  (iterations) =>
    [0.5, 1].flatMap((slowDown) =>
      [1.5, 2].map((edgeWeightInfluence) => ({
        id:
          `forceatlas2-sparse-i${iterations}-d${slowDown}` +
          `-e${edgeWeightInfluence}`,
        description:
          `Tuning-only sparse ForceAtlas2 weight variant ` +
          `(iterations=${iterations}, slowDown=${slowDown}, ` +
          `edgeWeightInfluence=${edgeWeightInfluence}).`,
        layout: (nodes, edges) =>
          layoutWithForceAtlas2(nodes, edges, {
            linLogMode: false,
            iterations,
            scalingRatio: 4,
            semanticBoost: 24,
            selectionBoost: 36,
            slowDown,
            gravity: 0,
            strongGravityMode: false,
            includeFactualHyperedges: false,
            broadFactualBoost: 32,
            edgeWeightInfluence,
          }),
      })),
    ),
);

const forceAtlasSparseFineWeightCandidates: LayoutCandidate[] = [1.1, 1.2, 1.3].flatMap(
  (edgeWeightInfluence) =>
    [1.2, 1.5].map((slowDown) => ({
      id: `forceatlas2-sparse-fine-e${edgeWeightInfluence}-d${slowDown}`,
      description:
        `Tuning-only sparse ForceAtlas2 fine weight variant ` +
        `(edgeWeightInfluence=${edgeWeightInfluence}, slowDown=${slowDown}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations: 125,
          scalingRatio: 4,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost: 32,
          edgeWeightInfluence,
        }),
    })),
);

const forceAtlasSparseScalingCandidates: LayoutCandidate[] = [1.5, 2, 3, 5, 6].map(
  (scalingRatio) => ({
    id: `forceatlas2-sparse-scale-${scalingRatio}`,
    description:
      `Tuning-only sparse ForceAtlas2 repulsion-scale variant ` +
      `(scalingRatio=${scalingRatio}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
      }),
  }),
);

const forceAtlasSparseIterationCandidates: LayoutCandidate[] = [75, 90, 100, 110, 115, 120].map(
  (iterations) => ({
    id: `forceatlas2-sparse-local-${iterations}`,
    description:
      `Tuning-only sparse ForceAtlas2 local-fidelity iteration variant ` +
      `(${iterations} iterations).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
        edgeWeightInfluence: 1.1,
      }),
  }),
);

const forceAtlasSparseFastScaleCandidates: LayoutCandidate[] = [100, 110].flatMap(
  (iterations) =>
    [6, 8, 10, 12].map((scalingRatio) => ({
      id: `forceatlas2-sparse-fast-i${iterations}-r${scalingRatio}`,
      description:
        `Tuning-only sparse ForceAtlas2 fast-repulsion variant ` +
        `(iterations=${iterations}, scalingRatio=${scalingRatio}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost: 32,
          edgeWeightInfluence: 1.1,
        }),
    })),
);

const forceAtlasSparseFastBroadCandidates: LayoutCandidate[] = [100, 110].flatMap(
  (iterations) =>
    [40, 48, 56, 64].map((broadFactualBoost) => ({
      id: `forceatlas2-sparse-fast-i${iterations}-b${broadFactualBoost}`,
      description:
        `Tuning-only sparse ForceAtlas2 fast broad-evidence variant ` +
        `(iterations=${iterations}, broad=${broadFactualBoost}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio: 8,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost,
          edgeWeightInfluence: 1.1,
        }),
    })),
);

const forceAtlasSparseLocalScaleCandidates: LayoutCandidate[] = [100, 110, 115].flatMap(
  (iterations) =>
    [1.5, 2, 3].map((scalingRatio) => ({
      id: `forceatlas2-sparse-local-i${iterations}-r${scalingRatio}`,
      description:
        `Tuning-only sparse ForceAtlas2 local-fidelity scale variant ` +
        `(iterations=${iterations}, scalingRatio=${scalingRatio}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations,
          scalingRatio,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost: 32,
          edgeWeightInfluence: 1.1,
        }),
    })),
);

const forceAtlasSparseBudgetCandidates: LayoutCandidate[] = [16, 20, 24, 28].map(
  (neighborBudget) => ({
    id: `forceatlas2-sparse-budget-${neighborBudget}`,
    description:
      `Tuning-only sparse ForceAtlas2 affinity-budget variant ` +
      `(neighborBudget=${neighborBudget}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
        edgeWeightInfluence: 1.1,
        neighborBudget,
      }),
  }),
);

const forceAtlasBudgetWeightCandidates: LayoutCandidate[] = [1.1, 1.15, 1.2, 1.25, 1.3].map(
  (edgeWeightInfluence) => ({
    id: `forceatlas2-budget16-weight-${edgeWeightInfluence}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 weight variant ` +
      `(edgeWeightInfluence=${edgeWeightInfluence}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
        edgeWeightInfluence,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasBudgetSemanticCandidates: LayoutCandidate[] = [36, 48, 72, 96, 144].map(
  (semanticBoost) => ({
    id: `forceatlas2-budget16-semantic-${semanticBoost}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 semantic variant ` +
      `(semanticBoost=${semanticBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost,
        selectionBoost: semanticBoost * 1.5,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 32,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasBudgetBroadCandidates: LayoutCandidate[] = [36, 40, 48, 64].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-budget16-broad-${broadFactualBoost}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 broad-evidence variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasBudgetIterationCandidates: LayoutCandidate[] = [150, 175, 200, 250].map(
  (iterations) => ({
    id: `forceatlas2-budget16-iterations-${iterations}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 convergence variant ` +
      `(${iterations} iterations).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 40,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasBudgetLowSemanticCandidates: LayoutCandidate[] = [2, 4, 8, 12, 16].map(
  (semanticBoost) => ({
    id: `forceatlas2-budget16-low-semantic-${semanticBoost}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 low-semantic variant ` +
      `(semanticBoost=${semanticBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost,
        selectionBoost: Math.max(semanticBoost * 1.5, 8),
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 40,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasBudgetFactualCandidates: LayoutCandidate[] = [1.5, 2, 3, 4, 6, 8].map(
  (exactFactualBoost) => ({
    id: `forceatlas2-budget16-factual-${exactFactualBoost}`,
    description:
      `Tuning-only budget-16 ForceAtlas2 exact factual variant ` +
      `(exactFactualBoost=${exactFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 40,
        exactFactualBoost,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasScaleInvariantCandidates: LayoutCandidate[] = [0.25, 0.5].map(
  (broadDegreeExponent) => ({
    id: `forceatlas2-scale-invariant-${broadDegreeExponent}`,
    description:
      `Tuning-only scale-invariant broad-evidence variant ` +
      `(broadDegreeExponent=${broadDegreeExponent}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 40,
        broadDegreeExponent,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
      }),
  }),
);

const forceAtlasScaleInvariantGridCandidates: LayoutCandidate[] = [
  ...[10, 12, 14, 16, 20].map((broadFactualBoost) => ({
    exponent: 0.25,
    broadFactualBoost,
  })),
  ...[2, 4, 6, 8].map((broadFactualBoost) => ({
    exponent: 0.5,
    broadFactualBoost,
  })),
].map(({exponent, broadFactualBoost}) => ({
  id: `forceatlas2-scale-e${exponent}-b${broadFactualBoost}`,
  description:
    `Tuning-only scale-invariant broad grid ` +
    `(exponent=${exponent}, boost=${broadFactualBoost}).`,
  layout: (nodes, edges) =>
    layoutWithForceAtlas2(nodes, edges, {
      linLogMode: false,
      iterations: 125,
      scalingRatio: 4,
      semanticBoost: 24,
      selectionBoost: 36,
      slowDown: 1.5,
      gravity: 0,
      strongGravityMode: false,
      includeFactualHyperedges: false,
      broadFactualBoost,
      broadDegreeExponent: exponent,
      edgeWeightInfluence: 1.1,
      neighborBudget: 16,
    }),
}));

const forceAtlasMultiscaleCandidates: LayoutCandidate[] = [0, 0.25, 0.5].map(
  (broadDegreeExponent) => ({
    id: `forceatlas2-multiscale-${broadDegreeExponent}`,
    description:
      `Tuning-only ForceAtlas2 with degree-scale-stratified sparse affinity ` +
      `(broadDegreeExponent=${broadDegreeExponent}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: broadDegreeExponent === 0 ? 40 : 14,
        broadDegreeExponent,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
        multiscaleRetention: true,
      }),
  }),
);

const forceAtlasMultiscaleBoostCandidates: LayoutCandidate[] = [10, 12, 16, 18, 20, 24].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-multiscale-b${broadFactualBoost}`,
    description:
      `Tuning-only scale-invariant multiscale boost variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
        multiscaleRetention: true,
      }),
  }),
);

const forceAtlasHybridCandidates: LayoutCandidate[] = [6, 8, 10, 12].map(
  (strongestReserve) => ({
    id: `forceatlas2-hybrid-${strongestReserve}`,
    description:
      `Tuning-only hybrid strongest/multiscale sparse affinity ` +
      `(strongestReserve=${strongestReserve}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 20,
        broadDegreeExponent: 0.5,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
        multiscaleRetention: true,
        strongestReserve,
      }),
  }),
);

const forceAtlasHybridBoostCandidates: LayoutCandidate[] = [24, 28, 32, 40].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-hybrid6-b${broadFactualBoost}`,
    description:
      `Tuning-only hybrid-6 broad boost variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        edgeWeightInfluence: 1.1,
        neighborBudget: 16,
        multiscaleRetention: true,
        strongestReserve: 6,
      }),
  }),
);

const forceAtlasWiderMultiscaleCandidates: LayoutCandidate[] = [20, 24].flatMap(
  (neighborBudget) =>
    [8, 10].flatMap((strongestReserve) =>
      [20, 24].map((broadFactualBoost) => ({
        id:
          `forceatlas2-wide-n${neighborBudget}-r${strongestReserve}` +
          `-b${broadFactualBoost}`,
        description:
          `Tuning-only wider multiscale sparse affinity ` +
          `(budget=${neighborBudget}, reserve=${strongestReserve}, ` +
          `broad=${broadFactualBoost}).`,
        layout: (nodes, edges) =>
          layoutWithForceAtlas2(nodes, edges, {
            linLogMode: false,
            iterations: 125,
            scalingRatio: 4,
            semanticBoost: 24,
            selectionBoost: 36,
            slowDown: 1.5,
            gravity: 0,
            strongGravityMode: false,
            includeFactualHyperedges: false,
            broadFactualBoost,
            broadDegreeExponent: 0.5,
            edgeWeightInfluence: 1.1,
            neighborBudget,
            multiscaleRetention: true,
            strongestReserve,
          }),
      })),
    ),
);

const forceAtlasLocalBalanceCandidates: LayoutCandidate[] = [1.25, 1.5, 2, 3].map(
  (localAffinityBoost) => ({
    id: `forceatlas2-balanced-local-${localAffinityBoost}`,
    description:
      `Tuning-only wide multiscale local-balance variant ` +
      `(localAffinityBoost=${localAffinityBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 20,
        broadDegreeExponent: 0.5,
        localAffinityBoost,
        edgeWeightInfluence: 1.1,
        neighborBudget: 24,
        multiscaleRetention: true,
        strongestReserve: 10,
      }),
  }),
);

const forceAtlasBalancedBroadCandidates: LayoutCandidate[] = [22, 24, 26, 28].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-balanced-broad-${broadFactualBoost}`,
    description:
      `Tuning-only local/broad balanced multiscale variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        localAffinityBoost: 1.5,
        edgeWeightInfluence: 1.1,
        neighborBudget: 24,
        multiscaleRetention: true,
        strongestReserve: 10,
      }),
  }),
);

const forceAtlasFineBalanceCandidates: LayoutCandidate[] = [1.6, 1.7, 1.8].map(
  (localAffinityBoost) => ({
    id: `forceatlas2-balanced-local-fine-${localAffinityBoost}`,
    description:
      `Tuning-only fine local/broad balance variant ` +
      `(localAffinityBoost=${localAffinityBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 24,
        broadDegreeExponent: 0.5,
        localAffinityBoost,
        edgeWeightInfluence: 1.1,
        neighborBudget: 24,
        multiscaleRetention: true,
        strongestReserve: 10,
      }),
  }),
);

const forceAtlasStrong16PlusScaleCandidates: LayoutCandidate[] = [12, 16, 20, 24, 32].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-strong16-scale-b${broadFactualBoost}`,
    description:
      `Tuning-only strongest-16 plus eight multiscale Edge variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        localAffinityBoost: 1,
        edgeWeightInfluence: 1.1,
        neighborBudget: 24,
        multiscaleRetention: true,
        strongestReserve: 16,
      }),
  }),
);

const forceAtlasStrong16WideScaleCandidates: LayoutCandidate[] = [16, 20, 24, 32].map(
  (broadFactualBoost) => ({
    id: `forceatlas2-strong16-wide-b${broadFactualBoost}`,
    description:
      `Tuning-only strongest-16 plus sixteen multiscale Edge variant ` +
      `(broadFactualBoost=${broadFactualBoost}).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost,
        broadDegreeExponent: 0.5,
        localAffinityBoost: 1,
        edgeWeightInfluence: 1.1,
        neighborBudget: 32,
        multiscaleRetention: true,
        strongestReserve: 16,
      }),
  }),
);

const forceAtlasLocalReserveCandidates: LayoutCandidate[] = [20, 24, 28].flatMap(
  (strongestReserve) =>
    [12, 16].map((broadFactualBoost) => ({
      id: `forceatlas2-local-r${strongestReserve}-b${broadFactualBoost}`,
      description:
        `Tuning-only strongest-local reserve plus multiscale evidence ` +
        `(reserve=${strongestReserve}, broad=${broadFactualBoost}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations: 125,
          scalingRatio: 4,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost,
          broadDegreeExponent: 0.5,
          localAffinityBoost: 1,
          edgeWeightInfluence: 1.1,
          neighborBudget: 32,
          multiscaleRetention: true,
          strongestReserve,
        }),
    })),
);

const forceAtlasLocalFineCandidates: LayoutCandidate[] = [1.1, 1.2, 1.3, 1.5].map(
  (localAffinityBoost) => ({
    id: `forceatlas2-local-fine-${localAffinityBoost}`,
    description:
      `Tuning-only strongest-16 plus eight multiscale Edge variant ` +
      `(local=${localAffinityBoost}, broad=16).`,
    layout: (nodes, edges) =>
      layoutWithForceAtlas2(nodes, edges, {
        linLogMode: false,
        iterations: 125,
        scalingRatio: 4,
        semanticBoost: 24,
        selectionBoost: 36,
        slowDown: 1.5,
        gravity: 0,
        strongGravityMode: false,
        includeFactualHyperedges: false,
        broadFactualBoost: 16,
        broadDegreeExponent: 0.5,
        localAffinityBoost,
        edgeWeightInfluence: 1.1,
        neighborBudget: 24,
        multiscaleRetention: true,
        strongestReserve: 16,
      }),
  }),
);

const forceAtlasRepulsionBalanceCandidates: LayoutCandidate[] = [12, 16].flatMap(
  (broadFactualBoost) =>
    [2, 3, 5].map((scalingRatio) => ({
      id: `forceatlas2-repulsion-s${scalingRatio}-b${broadFactualBoost}`,
      description:
        `Tuning-only strongest-16 plus eight multiscale Edge variant ` +
        `(repulsion=${scalingRatio}, broad=${broadFactualBoost}).`,
      layout: (nodes, edges) =>
        layoutWithForceAtlas2(nodes, edges, {
          linLogMode: false,
          iterations: 125,
          scalingRatio,
          semanticBoost: 24,
          selectionBoost: 36,
          slowDown: 1.5,
          gravity: 0,
          strongGravityMode: false,
          includeFactualHyperedges: false,
          broadFactualBoost,
          broadDegreeExponent: 0.5,
          localAffinityBoost: 1,
          edgeWeightInfluence: 1.1,
          neighborBudget: 24,
          multiscaleRetention: true,
          strongestReserve: 16,
        }),
    })),
);

export const layoutCandidates: ReadonlyMap<string, LayoutCandidate> = new Map([
  [productionEvidenceCandidate.id, productionEvidenceCandidate],
  [failedBaselineCandidate.id, failedBaselineCandidate],
  [weightedLinLogCandidate.id, weightedLinLogCandidate],
  [neighborhoodCrossEntropyCandidate.id, neighborhoodCrossEntropyCandidate],
  [contrastiveStressCandidate.id, contrastiveStressCandidate],
  [contrastiveSgdCandidate.id, contrastiveSgdCandidate],
  [normalizedSpectralCandidate.id, normalizedSpectralCandidate],
  [
    neighborhoodCrossEntropySgdCandidate.id,
    neighborhoodCrossEntropySgdCandidate,
  ],
  ...featureProjectionCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...anchoredLaplacianCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...anchoredLaplacianSparseCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...anchoredLaplacianHashCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...anchoredLaplacianFeatureCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...finiteDiffusionCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...robustSpectralCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCrossEntropyFastCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCompositeCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCompositeMultiscaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCompositeScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  [neighborhoodCompositeStableCandidate.id, neighborhoodCompositeStableCandidate],
  ...neighborhoodSeparatedScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  [neighborhoodCompositeBatchCandidate.id, neighborhoodCompositeBatchCandidate],
  ...neighborhoodAnchoredBatchCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCompositeFixedInitCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...neighborhoodCompositeRegularizedCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  [forceAtlasLinLogCandidate.id, forceAtlasLinLogCandidate],
  [forceAtlasLinearCandidate.id, forceAtlasLinearCandidate],
  [forceAtlasStableCandidate.id, forceAtlasStableCandidate],
  ...forceAtlasStatementGridCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasScaffoldCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasStatementScaffoldCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  [multiscaleStressCandidate.id, multiscaleStressCandidate],
  ...multiscaleStressTuningCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...multiscaleStressIterationCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...evidenceLandscapeCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...statementGridStressCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasLinearFastCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasLinearTuningCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseTuningCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseGridCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseWeightCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseFineWeightCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseScalingCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseIterationCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseFastScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseFastBroadCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseLocalScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasSparseBudgetCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetWeightCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetSemanticCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetBroadCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetIterationCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetLowSemanticCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBudgetFactualCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasScaleInvariantCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasScaleInvariantGridCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasMultiscaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasMultiscaleBoostCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasHybridCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasHybridBoostCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasWiderMultiscaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasLocalBalanceCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasBalancedBroadCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasFineBalanceCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasStrong16PlusScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasStrong16WideScaleCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasLocalReserveCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasLocalFineCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...forceAtlasRepulsionBalanceCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
  ...contrastiveTuningCandidates.map(
    (candidate) => [candidate.id, candidate] as const,
  ),
]);
