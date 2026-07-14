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

export type EdgeKind =
  | "mentions_term"
  | "refines"
  | "equivalent"
  | "hard_contradiction"
  | "advisory_tension"
  | "descriptive_conflict"
  | "envelope_conflict"
  | "supports"
  | "defeats"
  | "supersedes"
  | "unspecified";

export type EdgeFamily =
  | "lexical"
  | "semantic"
  | "selection"
  | "unspecified";

export type EndpointRole =
  | "mentioner"
  | "mentioned_term"
  | "refiner"
  | "refined"
  | "equivalent_peer"
  | "conflict_peer"
  | "supporter"
  | "supported"
  | "defeater"
  | "defeated"
  | "superseder"
  | "superseded"
  | "unspecified";

export type GraphViewMode =
  | "all"
  | "semantic"
  | "vocabulary"
  | "refinement"
  | "conflicts"
  | "isolated"
  | "selection"
  | "current";

/** A node as the UI consumes it — the wire Node projected to what a graph view
 *  needs: identity, the sentence text (hover label), its speech act (color),
 *  and asynchronous Evidence request/capture counts. */
export type GraphNode = {
  id: string;
  nodeKind: "specification" | "term";
  statement: string;
  speechAct: SpeechAct;
  evidenceCount: number;
  evidenceRequestCount: number;
};

export type GraphEdge = {
  id: string;
  source: string;
  target: string;
  kind: EdgeKind;
  family: EdgeFamily;
  sourceRole: EndpointRole;
  targetRole: EndpointRole;
  derivationMethod: string;
  derivationVersion: string;
};

export const TERM_NODE_COLOR = "#35c7b4";

export const EDGE_KIND_COLORS: Record<EdgeKind, string> = {
  mentions_term: "rgba(150, 150, 160, 0.22)",
  refines: "rgba(74, 144, 217, 0.82)",
  equivalent: "rgba(53, 199, 180, 0.78)",
  hard_contradiction: "rgba(239, 76, 64, 0.92)",
  advisory_tension: "rgba(232, 184, 75, 0.86)",
  descriptive_conflict: "rgba(196, 124, 93, 0.84)",
  envelope_conflict: "rgba(176, 111, 216, 0.86)",
  supports: "rgba(126, 217, 87, 0.9)",
  defeats: "rgba(239, 76, 64, 0.92)",
  supersedes: "rgba(176, 111, 216, 0.92)",
  unspecified: "rgba(120, 120, 125, 0.3)",
};

export const EDGE_KIND_LABELS: Record<EdgeKind, string> = {
  mentions_term: "Mentions written term",
  refines: "Refines",
  equivalent: "Equivalent",
  hard_contradiction: "Hard contradiction",
  advisory_tension: "Advisory tension",
  descriptive_conflict: "Descriptive conflict",
  envelope_conflict: "Envelope conflict",
  supports: "Supports selection",
  defeats: "Defeats",
  supersedes: "Supersedes",
  unspecified: "Unspecified",
};

export const EDGE_KIND_DESCRIPTIONS: Record<EdgeKind, string> = {
  mentions_term:
    "The mentioner contains the mentioned written term form. This is lexical incidence, not support.",
  refines:
    "Every behavior admitted by the stronger refiner is admitted by the weaker refined specification.",
  equivalent:
    "The two specifications have the same force and mutually imply the same guarantee under current rules.",
  hard_contradiction:
    "Two binding guarantees are proved unable to hold together.",
  advisory_tension:
    "Following a recommendation is proved to violate the other specification.",
  descriptive_conflict:
    "A described state is proved to conflict with the other specification.",
  envelope_conflict:
    "A permission admits the same behavior that the other specification forbids.",
  supports:
    "A versioned selection derivation records the supporter as a positive reason for the supported specification.",
  defeats:
    "A versioned selection derivation records the defeater as winning an explicitly resolved competition with the defeated specification.",
  supersedes:
    "A versioned selection derivation records the superseder as the selected replacement for the superseded specification.",
  unspecified: "The relation kind is not recognized by this UI version.",
};

export const EDGE_FAMILY_LABELS: Record<EdgeFamily, string> = {
  lexical: "Lexical",
  semantic: "Semantic",
  selection: "Selection",
  unspecified: "Unspecified",
};

export const EDGE_KIND_FAMILIES: Record<EdgeKind, EdgeFamily> = {
  mentions_term: "lexical",
  refines: "semantic",
  equivalent: "semantic",
  hard_contradiction: "semantic",
  advisory_tension: "semantic",
  descriptive_conflict: "semantic",
  envelope_conflict: "semantic",
  supports: "selection",
  defeats: "selection",
  supersedes: "selection",
  unspecified: "unspecified",
};

export const ENDPOINT_ROLE_LABELS: Record<EndpointRole, string> = {
  mentioner: "Mentioner",
  mentioned_term: "Mentioned term",
  refiner: "Refiner / stronger",
  refined: "Refined / weaker",
  equivalent_peer: "Equivalent peer",
  conflict_peer: "Conflict peer",
  supporter: "Supporter",
  supported: "Supported",
  defeater: "Defeater",
  defeated: "Defeated",
  superseder: "Superseder",
  superseded: "Superseded",
  unspecified: "Unspecified role",
};

export const EDGE_KIND_ORDER: EdgeKind[] = [
  "refines",
  "equivalent",
  "hard_contradiction",
  "advisory_tension",
  "descriptive_conflict",
  "envelope_conflict",
  "supports",
  "defeats",
  "supersedes",
  "mentions_term",
  "unspecified",
];

export const DIRECTED_EDGE_KINDS = new Set<EdgeKind>([
  "mentions_term",
  "refines",
  "supports",
  "defeats",
  "supersedes",
]);

export const SEMANTIC_EDGE_KINDS = new Set<EdgeKind>([
  "refines",
  "equivalent",
  "hard_contradiction",
  "advisory_tension",
  "descriptive_conflict",
  "envelope_conflict",
]);

export const CONFLICT_EDGE_KINDS = new Set<EdgeKind>([
  "hard_contradiction",
  "advisory_tension",
  "descriptive_conflict",
  "envelope_conflict",
]);

export const SELECTION_EDGE_KINDS = new Set<EdgeKind>([
  "supports",
  "defeats",
  "supersedes",
]);

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
