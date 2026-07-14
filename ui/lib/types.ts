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
  | "occurrence_reliance"
  | "guarantee_discharge"
  | "admissibility_envelope"
  | "supports"
  | "defeats"
  | "supersedes"
  | "grounded_by"
  | "has_assumption"
  | "has_guarantee"
  | "unspecified";

export type EdgeFamily =
  | "lexical"
  | "semantic"
  | "selection"
  | "projection"
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
  | "grounded_specification"
  | "evidence"
  | "contract_specification"
  | "assumption"
  | "guarantee"
  | "reliance_evidence"
  | "reliant_contract"
  | "discharging_guarantee"
  | "discharged_contract"
  | "admissible_environment"
  | "bounded_contract"
  | "unspecified";

export type GraphViewMode =
  | "all"
  | "semantic"
  | "vocabulary"
  | "refinement"
  | "conflicts"
  | "isolated"
  | "selection"
  | "fitness"
  | "contracts"
  | "ledger"
  | "current";

export type ScoreContribution = {
  kind: string;
  points: number;
  edgeId: string;
  sourceNodeId: string | null;
  evidenceNodeId: string | null;
  detail: string;
};

export type SelectionExclusion = {
  kind: string;
  edgeId: string | null;
  competingNodeId: string | null;
  detail: string;
};

/** A node as the UI consumes it — the wire Node projected to what a graph view
 *  needs: identity, the sentence text (hover label), its speech act (color),
 *  and asynchronous Evidence request/capture counts. */
export type GraphNode = {
  id: string;
  nodeKind:
    | "specification"
    | "term"
    | "evidence"
    | "assumption"
    | "guarantee";
  statement: string;
  speechAct: SpeechAct;
  evidenceCount: number;
  evidenceRequestCount: number;
  current: boolean;
  policyVersion: string;
  supportScore: number;
  evidenceScore: number;
  relationScore: number;
  contributions: ScoreContribution[];
  exclusions: SelectionExclusion[];
};

export type GraphEdge = {
  id: string;
  source: string;
  target: string;
  kind: EdgeKind;
  family: EdgeFamily;
  sourceRole: EndpointRole;
  targetRole: EndpointRole;
  reliedSpecId: string | null;
  current: boolean;
  derivationMethod: string;
  derivationVersion: string;
};

export const TERM_NODE_COLOR = "#35c7b4";
export const DERIVED_NODE_COLORS = {
  evidence: "#f0a35e",
  assumption: "#58c4dd",
  guarantee: "#d783e8",
} as const;

export const EDGE_KIND_COLORS: Record<EdgeKind, string> = {
  mentions_term: "rgba(150, 150, 160, 0.22)",
  refines: "rgba(74, 144, 217, 0.82)",
  equivalent: "rgba(53, 199, 180, 0.78)",
  hard_contradiction: "rgba(239, 76, 64, 0.92)",
  advisory_tension: "rgba(232, 184, 75, 0.86)",
  descriptive_conflict: "rgba(196, 124, 93, 0.84)",
  envelope_conflict: "rgba(176, 111, 216, 0.86)",
  occurrence_reliance: "rgba(83, 176, 234, 0.92)",
  guarantee_discharge: "rgba(77, 214, 170, 0.94)",
  admissibility_envelope: "rgba(126, 217, 87, 0.9)",
  supports: "rgba(126, 217, 87, 0.9)",
  defeats: "rgba(239, 76, 64, 0.92)",
  supersedes: "rgba(176, 111, 216, 0.92)",
  grounded_by: "rgba(240, 163, 94, 0.78)",
  has_assumption: "rgba(88, 196, 221, 0.78)",
  has_guarantee: "rgba(215, 131, 232, 0.78)",
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
  occurrence_reliance: "Occurrence / state reliance",
  guarantee_discharge: "Guarantee discharge",
  admissibility_envelope: "Admissibility envelope",
  supports: "Supports selection",
  defeats: "Defeats",
  supersedes: "Supersedes",
  grounded_by: "Grounded by",
  has_assumption: "Has assumption",
  has_guarantee: "Has guarantee",
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
  occurrence_reliance:
    "The target contract relies on an explicitly named occurrence or state, proved by the source assertion.",
  guarantee_discharge:
    "The source guarantee proves and discharges an explicitly named assumption of the target contract.",
  admissibility_envelope:
    "The source permission explicitly bounds environment behavior the target contract must tolerate; it does not become an assumption conjunct.",
  supports:
    "A versioned selection derivation records the supporter as a positive reason for the supported specification.",
  defeats:
    "A versioned selection derivation records the defeater as winning an explicitly resolved competition with the defeated specification.",
  supersedes:
    "A versioned selection derivation records the superseder as the selected replacement for the superseded specification.",
  grounded_by:
    "The evidence vertex records captured grounding for the specification.",
  has_assumption:
    "The assumption vertex is the environment side of the specification's ingest contract.",
  has_guarantee:
    "The guarantee vertex is the behavior side of the specification's ingest contract.",
  unspecified: "The relation kind is not recognized by this UI version.",
};

export const EDGE_FAMILY_LABELS: Record<EdgeFamily, string> = {
  lexical: "Lexical",
  semantic: "Semantic",
  selection: "Selection",
  projection: "Projection",
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
  occurrence_reliance: "semantic",
  guarantee_discharge: "semantic",
  admissibility_envelope: "semantic",
  supports: "selection",
  defeats: "selection",
  supersedes: "selection",
  grounded_by: "projection",
  has_assumption: "projection",
  has_guarantee: "projection",
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
  grounded_specification: "Grounded specification",
  evidence: "Evidence",
  contract_specification: "Contract specification",
  assumption: "Assumption",
  guarantee: "Guarantee",
  reliance_evidence: "Reliance evidence",
  reliant_contract: "Reliant contract",
  discharging_guarantee: "Discharging guarantee",
  discharged_contract: "Discharged contract",
  admissible_environment: "Admissible environment",
  bounded_contract: "Bounded contract",
  unspecified: "Unspecified role",
};

export const EDGE_KIND_ORDER: EdgeKind[] = [
  "refines",
  "equivalent",
  "hard_contradiction",
  "advisory_tension",
  "descriptive_conflict",
  "envelope_conflict",
  "occurrence_reliance",
  "guarantee_discharge",
  "admissibility_envelope",
  "supports",
  "defeats",
  "supersedes",
  "grounded_by",
  "has_assumption",
  "has_guarantee",
  "mentions_term",
  "unspecified",
];

export const DIRECTED_EDGE_KINDS = new Set<EdgeKind>([
  "mentions_term",
  "refines",
  "occurrence_reliance",
  "guarantee_discharge",
  "admissibility_envelope",
  "supports",
  "defeats",
  "supersedes",
  "grounded_by",
  "has_assumption",
  "has_guarantee",
]);

export const SEMANTIC_EDGE_KINDS = new Set<EdgeKind>([
  "refines",
  "equivalent",
  "hard_contradiction",
  "advisory_tension",
  "descriptive_conflict",
  "envelope_conflict",
  "occurrence_reliance",
  "guarantee_discharge",
  "admissibility_envelope",
]);

export const PAIRING_EDGE_KINDS = new Set<EdgeKind>([
  "occurrence_reliance",
  "guarantee_discharge",
  "admissibility_envelope",
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

export type LedgerPage = {
  nodes: GraphNode[];
  edges: GraphEdge[];
  nextPageToken: string;
  totalEdges: number;
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
