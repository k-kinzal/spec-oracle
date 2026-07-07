// Shared graph types and the speech-act palette. No server-only imports here,
// so both the BFF route (mapping the wire response) and the client components
// (rendering) can use it.

export type SpeechAct =
  | "definition"
  | "description"
  | "obligation"
  | "prohibition"
  | "recommendation"
  | "permission"
  | "unknown";

export type EdgeKind = "refines" | "composes" | "contradicts" | "unspecified";

/** A node as the UI consumes it — the wire Node projected to what a graph view
 *  needs: identity, the sentence text (hover label), its speech act (color),
 *  and the evidence count (size). */
export type GraphNode = {
  id: string;
  statement: string;
  speechAct: SpeechAct;
  evidenceCount: number;
};

export type GraphEdge = {
  id: string;
  source: string;
  target: string;
  kind: EdgeKind;
};

/** One bounded page of the graph, as returned by the BFF (`/api/graph`). */
export type GraphPage = {
  nodes: GraphNode[];
  edges: GraphEdge[];
  nextPageToken: string;
  totalNodes: number;
};

/** Color by speech act — the dimension that gives the graph its clustered,
 *  legible look. Chosen for contrast on the dark canvas. */
export const SPEECH_ACT_COLORS: Record<SpeechAct, string> = {
  obligation: "#4a90d9", // blue — the binding "shall"
  prohibition: "#e0533d", // red — the forbidding "shall not"
  recommendation: "#e8b84b", // amber — the advisory "should"
  permission: "#7ed957", // green — the admitting "may"
  definition: "#b06fd8", // purple — vocabulary, not behavior
  description: "#9aa0a6", // grey — states of affairs
  unknown: "#5f6368", // dim — unparsed / pre-grammar rows
};

/** Human-readable labels for the legend. */
export const SPEECH_ACT_LABELS: Record<SpeechAct, string> = {
  obligation: "Obligation (shall)",
  prohibition: "Prohibition (shall not)",
  recommendation: "Recommendation (should)",
  permission: "Permission (may)",
  definition: "Definition (means)",
  description: "Description (is)",
  unknown: "Unknown",
};

export const SPEECH_ACT_ORDER: SpeechAct[] = [
  "obligation",
  "prohibition",
  "recommendation",
  "permission",
  "definition",
  "description",
  "unknown",
];
