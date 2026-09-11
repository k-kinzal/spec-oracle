import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
} from "../lib/specification-layout";
import {
  deriveSpecificationProximity,
  statementLexicalFeatures,
} from "../lib/specification-proximity";

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

export type PerturbedLayoutInput = {
  nodes: SpecificationLayoutInputNode[];
  edges: SpecificationLayoutInputEdge[];
};

/**
 * Remove the highest-degree one percent of view features without assigning a
 * context. Each selected view feature is masked directly so adjacent lexical
 * routes that were not selected remain intact.
 */
export function omitHighestDegreeFeatures(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  fraction = 0.01,
): PerturbedLayoutInput & {omittedFeatureIds: string[]} {
  const proximity = deriveSpecificationProximity(nodes, edges);
  const ranked = [...proximity.hyperedges].sort(
    (left, right) => right.degree - left.degree || left.id.localeCompare(right.id),
  );
  const omitted = ranked.slice(0, Math.max(1, Math.ceil(ranked.length * fraction)));
  const omittedFeatureIds = omitted.map((feature) => feature.id);
  const connectorIds = new Set<string>();
  const lexicalFeatureIds = new Set<string>();
  for (const feature of omitted) {
    if (feature.signal === "shared_term") {
      connectorIds.add(feature.id.slice("shared_term:".length));
    } else if (feature.signal === "shared_projection") {
      connectorIds.add(feature.id.slice("shared_projection:".length));
    } else if (feature.signal === "lexical_unigram") {
      lexicalFeatureIds.add(feature.id);
    } else if (feature.signal === "lexical_bigram") {
      lexicalFeatureIds.add(feature.id);
    }
  }
  const perturbedNodes = nodes
    .filter((node) => !connectorIds.has(node.id))
    .map((node) => {
      if (node.nodeKind !== "specification") return node;
      return {
        ...node,
        excludedViewFeatureIds: [
          ...(node.excludedViewFeatureIds ?? []),
          ...lexicalFeatureIds,
        ],
      };
    });
  return {
    nodes: perturbedNodes,
    edges: edges.filter(
      (edge) =>
        !connectorIds.has(edge.source) && !connectorIds.has(edge.target),
    ),
    omittedFeatureIds,
  };
}

/** Deterministic ten-percent observation loss for incomplete-data trials. */
export function omitNonSemanticRoutes(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  trial: number,
  fraction = 0.1,
): PerturbedLayoutInput {
  const salt = `dropout-${trial}`;
  return {
    nodes: nodes.map((node) => {
      if (node.nodeKind !== "specification") return node;
      const features = statementLexicalFeatures(node.statement);
      const featureIds = [
        ...[...features.unigrams].map((token) => `lexical_unigram:${token}`),
        ...[...features.bigrams].map((token) => `lexical_bigram:${token}`),
      ];
      return {
        ...node,
        excludedViewFeatureIds: [
          ...(node.excludedViewFeatureIds ?? []),
          ...featureIds.filter(
            (featureId) =>
              stableHash(`${salt}\u0000${node.id}\u0000${featureId}`) /
                4294967296 <
              fraction,
          ),
        ],
      };
    }),
    edges: edges.filter(
      (edge) =>
        edge.family === "semantic" ||
        edge.family === "selection" ||
        stableHash(`${salt}\u0000${edge.id}`) / 4294967296 >= fraction,
    ),
  };
}
