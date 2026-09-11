import type {GraphEdge, GraphNode} from "@/lib/types";

export type ProximitySignal =
  | "semantic"
  | "selection"
  | "shared_term"
  | "shared_projection"
  | "lexical_unigram"
  | "lexical_bigram"
  | "other";

export type ProximityLink = {
  id: string;
  source: string;
  target: string;
  signal: ProximitySignal;
  weight: number;
  distance: number;
};

export type ProximityHyperedge = {
  id: string;
  signal:
    | "shared_term"
    | "shared_projection"
    | "lexical_unigram"
    | "lexical_bigram";
  degree: number;
  members: Array<{specificationId: string; weight: number}>;
};

export type SpecificationProximityModel = {
  links: ProximityLink[];
  hyperedges: ProximityHyperedge[];
  featureCount: number;
  routeCount: number;
};

export type SpecificationLayoutGraph = {
  nodes: GraphNode[];
  edges: GraphEdge[];
};

type ProximityNodeInput = Pick<GraphNode, "id" | "nodeKind" | "statement"> & {
  excludedViewFeatureIds?: readonly string[];
};
type ProximityEdgeInput = Pick<
  GraphEdge,
  "id" | "source" | "target" | "current" | "family"
>;

const SIGNAL_WEIGHT = {
  semantic: 6,
  selection: 8,
  shared_term: 1.35,
  shared_projection: 2.25,
  lexical_unigram: 0.9,
  lexical_bigram: 2.8,
  other: 0.4,
} as const satisfies Record<ProximitySignal, number>;

function isTopAssumption(node: GraphNode | undefined): boolean {
  return node?.nodeKind === "assumption" && node.statement.trim() === "⊤";
}

export function isCompleteDefaultTopology(
  populationComplete: boolean,
  presentedSpecifications: number,
  totalSpecifications: number,
) {
  return (
    populationComplete &&
    totalSpecifications > 0 &&
    presentedSpecifications === totalSpecifications
  );
}

/**
 * Select the complete input of the default view without assigning a context.
 * Every Specification remains. A non-Specification connector remains only when
 * it supplies an actual route between at least two current Specifications.
 */
export function selectDefaultSpecificationGraph(
  pool: GraphNode[],
  candidateEdges: GraphEdge[],
): SpecificationLayoutGraph {
  const byId = new Map(pool.map((node) => [node.id, node]));
  const specifications = pool.filter(
    (node) => node.nodeKind === "specification",
  );
  const specificationIds = new Set(specifications.map((node) => node.id));
  const specificationsByConnector = new Map<string, Set<string>>();

  for (const edge of candidateEdges) {
    if (!edge.current) continue;
    const sourceSpecification = specificationIds.has(edge.source);
    const targetSpecification = specificationIds.has(edge.target);
    if (sourceSpecification === targetSpecification) continue;
    const connectorId = sourceSpecification ? edge.target : edge.source;
    const specificationId = sourceSpecification ? edge.source : edge.target;
    const connector = byId.get(connectorId);
    if (
      !connector ||
      connector.nodeKind === "specification" ||
      isTopAssumption(connector)
    ) {
      continue;
    }
    const incident =
      specificationsByConnector.get(connectorId) ?? new Set<string>();
    incident.add(specificationId);
    specificationsByConnector.set(connectorId, incident);
  }

  const sharedConnectorIds = new Set(
    [...specificationsByConnector]
      .filter(([, incident]) => incident.size > 1)
      .map(([connectorId]) => connectorId),
  );
  const edges = candidateEdges.filter((edge) => {
    if (!edge.current) return false;
    if (specificationIds.has(edge.source) && specificationIds.has(edge.target)) {
      return edge.family === "semantic" || edge.family === "selection";
    }
    return (
      (specificationIds.has(edge.source) && sharedConnectorIds.has(edge.target)) ||
      (sharedConnectorIds.has(edge.source) && specificationIds.has(edge.target))
    );
  });

  return {
    nodes: [
      ...specifications,
      ...pool.filter(
        (node) =>
          node.nodeKind !== "specification" &&
          sharedConnectorIds.has(node.id),
      ),
    ],
    edges,
  };
}

/**
 * One incidence of a global connector must not be as strong as one incidence
 * of a narrow connector. The connector remains factual; only its per-Node pull
 * is reduced.
 */
export function normalizedIncidenceWeight(distinctSpecificationDegree: number) {
  return 1 / Math.sqrt(Math.max(1, distinctSpecificationDegree - 1));
}

/** Corpus-relative information content normalized to [0, 1]. */
export function normalizedInverseDocumentFrequency(
  population: number,
  documentFrequency: number,
) {
  if (population <= 1 || documentFrequency <= 0) return 0;
  return Math.max(
    0,
    Math.log((population + 1) / (documentFrequency + 1)) /
      Math.log(population + 1),
  );
}

/**
 * Unicode lexical features derived only for this view. No authored context,
 * crate, command, or project name is embedded in the tokenizer.
 */
export function statementLexicalFeatures(statement: string) {
  const normalized = statement
    .normalize("NFKC")
    .replace(/([\p{Ll}\p{N}])([\p{Lu}])/gu, "$1 $2")
    .toLowerCase();
  const tokens = normalized.match(/[\p{L}\p{N}]+/gu) ?? [];
  const unigrams = new Set(tokens.filter((token) => token.length > 1));
  const bigrams = new Set<string>();
  for (let index = 0; index + 1 < tokens.length; index += 1) {
    if (tokens[index].length <= 1 || tokens[index + 1].length <= 1) continue;
    bigrams.add(`${tokens[index]}\u0001${tokens[index + 1]}`);
  }
  return {unigrams, bigrams};
}

function connectorSignal(
  node: ProximityNodeInput,
): "shared_term" | "shared_projection" {
  return node.nodeKind === "term" ? "shared_term" : "shared_projection";
}

function featureIncidenceWeight(
  signal: "lexical_unigram" | "lexical_bigram",
  population: number,
  degree: number,
) {
  const specificity = Math.pow(
    normalizedInverseDocumentFrequency(population, degree),
    1.35,
  );
  return (
    SIGNAL_WEIGHT[signal] *
    specificity *
    normalizedIncidenceWeight(degree)
  );
}

/**
 * Produce every distance input consumed by the one Node-level layout.
 * Lexical hyperedges affect coordinates only; they are never returned as
 * GraphEdge values and are never drawn as persisted relationships.
 */
export function deriveSpecificationProximity(
  nodes: ProximityNodeInput[],
  edges: ProximityEdgeInput[],
): SpecificationProximityModel {
  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const specifications = nodes.filter((node) => node.nodeKind === "specification");
  const specificationIds = new Set(specifications.map((node) => node.id));
  const population = specifications.length;
  const incidentSpecifications = new Map<string, Set<string>>();

  for (const edge of edges) {
    if (!edge.current) continue;
    const sourceSpecification = specificationIds.has(edge.source);
    const targetSpecification = specificationIds.has(edge.target);
    if (sourceSpecification === targetSpecification) continue;
    const connectorId = sourceSpecification ? edge.target : edge.source;
    const specificationId = sourceSpecification ? edge.source : edge.target;
    const connector = nodeById.get(connectorId);
    if (!connector || connector.nodeKind === "specification") continue;
    if (connector.nodeKind === "assumption" && connector.statement.trim() === "⊤") {
      continue;
    }
    const incident = incidentSpecifications.get(connectorId) ?? new Set<string>();
    incident.add(specificationId);
    incidentSpecifications.set(connectorId, incident);
  }

  const links: ProximityLink[] = [];
  for (const edge of edges) {
    const source = nodeById.get(edge.source);
    const target = nodeById.get(edge.target);
    if (!source || !target) continue;
    if (
      (source.nodeKind === "assumption" && source.statement.trim() === "⊤") ||
      (target.nodeKind === "assumption" && target.statement.trim() === "⊤")
    ) {
      continue;
    }
    const sourceSpecification = specificationIds.has(edge.source);
    const targetSpecification = specificationIds.has(edge.target);
    let signal: ProximitySignal = "other";
    let weight: number = SIGNAL_WEIGHT.other;
    let distance: number = 64;
    if (sourceSpecification && targetSpecification) {
      if (edge.family === "semantic") signal = "semantic";
      if (edge.family === "selection") signal = "selection";
      weight = SIGNAL_WEIGHT[signal];
      distance = signal === "selection" ? 8 : signal === "semantic" ? 10 : 58;
    } else if (sourceSpecification !== targetSpecification) {
      const connector = sourceSpecification ? target : source;
      signal = connectorSignal(connector);
      const degree = incidentSpecifications.get(connector.id)?.size ?? 1;
      const idf = normalizedInverseDocumentFrequency(population, degree);
      const specificity = 0.35 + 0.65 * idf;
      weight =
        SIGNAL_WEIGHT[signal] *
        specificity *
        normalizedIncidenceWeight(degree);
      distance = 34 + Math.min(82, Math.log2(Math.max(1, degree)) * 9);
    }
    if (!edge.current) weight *= 0.25;
    if (weight <= 0) continue;
    links.push({
      id: edge.id,
      source: edge.source,
      target: edge.target,
      signal,
      weight,
      distance,
    });
  }

  const hyperedges: ProximityHyperedge[] = [];
  for (const [connectorId, incident] of incidentSpecifications) {
    if (incident.size < 2) continue;
    const connector = nodeById.get(connectorId);
    if (!connector) continue;
    const signal = connectorSignal(connector);
    const idf = normalizedInverseDocumentFrequency(population, incident.size);
    const specificity = 0.35 + 0.65 * idf;
    const weight =
      SIGNAL_WEIGHT[signal] *
      specificity *
      normalizedIncidenceWeight(incident.size);
    hyperedges.push({
      id: `${signal}:${connectorId}`,
      signal,
      degree: incident.size,
      members: [...incident]
        .sort()
        .map((specificationId) => ({specificationId, weight})),
    });
  }

  const documents = specifications.map((specification) => {
    const features = statementLexicalFeatures(specification.statement);
    const excluded = new Set(specification.excludedViewFeatureIds ?? []);
    return {
      id: specification.id,
      unigrams: new Set(
        [...features.unigrams].filter(
          (token) => !excluded.has(`lexical_unigram:${token}`),
        ),
      ),
      bigrams: new Set(
        [...features.bigrams].filter(
          (token) => !excluded.has(`lexical_bigram:${token}`),
        ),
      ),
    };
  });
  const unigramMembers = new Map<string, string[]>();
  const bigramMembers = new Map<string, string[]>();
  for (const document of documents) {
    for (const token of document.unigrams) {
      const members = unigramMembers.get(token) ?? [];
      members.push(document.id);
      unigramMembers.set(token, members);
    }
    for (const token of document.bigrams) {
      const members = bigramMembers.get(token) ?? [];
      members.push(document.id);
      bigramMembers.set(token, members);
    }
  }

  const appendFeatures = (
    memberMap: Map<string, string[]>,
    signal: "lexical_unigram" | "lexical_bigram",
  ) => {
    for (const [token, memberIds] of memberMap) {
      if (memberIds.length < 2) continue;
      const weight = featureIncidenceWeight(signal, population, memberIds.length);
      if (weight <= 0) continue;
      hyperedges.push({
        id: `${signal}:${token}`,
        signal,
        degree: memberIds.length,
        members: memberIds
          .sort()
          .map((specificationId) => ({specificationId, weight})),
      });
    }
  };
  appendFeatures(unigramMembers, "lexical_unigram");
  appendFeatures(bigramMembers, "lexical_bigram");

  return {
    links,
    hyperedges,
    featureCount: hyperedges.length,
    routeCount:
      links.length +
      hyperedges.reduce((sum, hyperedge) => sum + hyperedge.members.length, 0),
  };
}
