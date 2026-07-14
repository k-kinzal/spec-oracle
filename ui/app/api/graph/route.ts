// BFF endpoint: GET /api/graph?pageSize=&pageToken= → one bounded page of the
// graph as JSON. The browser calls this; it calls specd over gRPC. The read is
// bounded on both sides: the daemon hard-caps the page, and this handler clamps
// the requested size before forwarding, so the client can never coerce an
// unbounded read.

import { NextRequest, NextResponse } from "next/server";
import { getGraph } from "@/lib/grpc";
import type {
  EdgeFamily,
  EdgeKind,
  EndpointRole,
  GraphEdge,
  GraphNode,
  SpeechAct,
} from "@/lib/types";

// This route talks gRPC over a raw socket, so it must run on the Node runtime,
// and its result changes with the store, so it is never statically cached.
export const runtime = "nodejs";
export const dynamic = "force-dynamic";

// Mirror the daemon's own ceiling so an over-large request is rejected here too,
// before a round trip.
const MAX_PAGE_SIZE = 1000;

export async function GET(req: NextRequest) {
  const params = req.nextUrl.searchParams;
  const rawSize = Number(params.get("pageSize"));
  const pageSize = Number.isFinite(rawSize)
    ? Math.min(Math.max(0, Math.trunc(rawSize)), MAX_PAGE_SIZE)
    : 0; // 0 → let the daemon apply its default
  const pageToken = params.get("pageToken") ?? "";

  try {
    const page = await getGraph(pageSize, pageToken);
    return NextResponse.json({
      nodes: [
        ...(page.nodes ?? []).map(toNode),
        ...(page.term_nodes ?? []).map(toTermNode),
        ...(page.derived_nodes ?? []).map(toDerivedNode),
      ],
      edges: (page.edges ?? []).map(toEdge),
      nextPageToken: page.next_page_token ?? "",
      totalNodes: Number(page.total_nodes ?? 0),
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "graph read failed";
    // A daemon that is down or erroring is an upstream failure from the UI's
    // point of view.
    return NextResponse.json({ error: message }, { status: 502 });
  }
}

// ---- wire → UI projection --------------------------------------------------

const SPEECH_ACTS: Record<string, SpeechAct> = {
  SPEECH_ACT_DEFINITION: "definition",
  SPEECH_ACT_DESCRIPTION: "description",
  SPEECH_ACT_OBLIGATION: "obligation",
  SPEECH_ACT_PROHIBITION: "prohibition",
  SPEECH_ACT_RECOMMENDATION: "recommendation",
  SPEECH_ACT_PERMISSION: "permission",
};

const EDGE_KINDS: Record<string, EdgeKind> = {
  EDGE_KIND_MENTIONS_TERM: "mentions_term",
  EDGE_KIND_REFINES: "refines",
  EDGE_KIND_EQUIVALENT: "equivalent",
  EDGE_KIND_HARD_CONTRADICTION: "hard_contradiction",
  EDGE_KIND_ADVISORY_TENSION: "advisory_tension",
  EDGE_KIND_DESCRIPTIVE_CONFLICT: "descriptive_conflict",
  EDGE_KIND_ENVELOPE_CONFLICT: "envelope_conflict",
  EDGE_KIND_OCCURRENCE_RELIANCE: "occurrence_reliance",
  EDGE_KIND_GUARANTEE_DISCHARGE: "guarantee_discharge",
  EDGE_KIND_ADMISSIBILITY_ENVELOPE: "admissibility_envelope",
  EDGE_KIND_SUPPORTS: "supports",
  EDGE_KIND_DEFEATS: "defeats",
  EDGE_KIND_SUPERSEDES: "supersedes",
  EDGE_KIND_GROUNDED_BY: "grounded_by",
  EDGE_KIND_HAS_ASSUMPTION: "has_assumption",
  EDGE_KIND_HAS_GUARANTEE: "has_guarantee",
};

const EDGE_FAMILIES: Record<string, EdgeFamily> = {
  EDGE_FAMILY_LEXICAL: "lexical",
  EDGE_FAMILY_SEMANTIC: "semantic",
  EDGE_FAMILY_SELECTION: "selection",
  EDGE_FAMILY_PROJECTION: "projection",
};

const ENDPOINT_ROLES: Record<string, EndpointRole> = {
  EDGE_ENDPOINT_ROLE_MENTIONER: "mentioner",
  EDGE_ENDPOINT_ROLE_MENTIONED_TERM: "mentioned_term",
  EDGE_ENDPOINT_ROLE_REFINER: "refiner",
  EDGE_ENDPOINT_ROLE_REFINED: "refined",
  EDGE_ENDPOINT_ROLE_EQUIVALENT_PEER: "equivalent_peer",
  EDGE_ENDPOINT_ROLE_CONFLICT_PEER: "conflict_peer",
  EDGE_ENDPOINT_ROLE_SUPPORTER: "supporter",
  EDGE_ENDPOINT_ROLE_SUPPORTED: "supported",
  EDGE_ENDPOINT_ROLE_DEFEATER: "defeater",
  EDGE_ENDPOINT_ROLE_DEFEATED: "defeated",
  EDGE_ENDPOINT_ROLE_SUPERSEDER: "superseder",
  EDGE_ENDPOINT_ROLE_SUPERSEDED: "superseded",
  EDGE_ENDPOINT_ROLE_GROUNDED_SPECIFICATION: "grounded_specification",
  EDGE_ENDPOINT_ROLE_EVIDENCE: "evidence",
  EDGE_ENDPOINT_ROLE_CONTRACT_SPECIFICATION: "contract_specification",
  EDGE_ENDPOINT_ROLE_ASSUMPTION: "assumption",
  EDGE_ENDPOINT_ROLE_GUARANTEE: "guarantee",
  EDGE_ENDPOINT_ROLE_RELIANCE_EVIDENCE: "reliance_evidence",
  EDGE_ENDPOINT_ROLE_RELIANT_CONTRACT: "reliant_contract",
  EDGE_ENDPOINT_ROLE_DISCHARGING_GUARANTEE: "discharging_guarantee",
  EDGE_ENDPOINT_ROLE_DISCHARGED_CONTRACT: "discharged_contract",
  EDGE_ENDPOINT_ROLE_ADMISSIBLE_ENVIRONMENT: "admissible_environment",
  EDGE_ENDPOINT_ROLE_BOUNDED_CONTRACT: "bounded_contract",
};

function toNode(raw: unknown): GraphNode {
  const n = raw as {
    id?: string;
    statement?: string;
    sentence?: { speech_act?: string } | null;
    meta?: { evidence?: unknown[]; evidence_requests?: unknown[] } | null;
    selection?: {
      current?: boolean;
      supporting_edge_ids?: unknown[];
      policy_version?: string;
      support_score?: number;
      evidence_score?: number;
      relation_score?: number;
      contributions?: Array<{
        kind?: string;
        points?: number;
        edge_id?: string;
        source_node_id?: string | null;
        evidence_node_id?: string | null;
        detail?: string;
      }>;
      exclusions?: Array<{
        kind?: string;
        edge_id?: string | null;
        competing_node_id?: string | null;
        detail?: string;
      }>;
    } | null;
  };
  return {
    id: n.id ?? "",
    nodeKind: "specification",
    statement: n.statement ?? "",
    // A node whose text no longer parses under the current grammar has no
    // derived sentence view; it degrades to "unknown" rather than vanishing.
    speechAct: SPEECH_ACTS[n.sentence?.speech_act ?? ""] ?? "unknown",
    evidenceCount: n.meta?.evidence?.length ?? 0,
    evidenceRequestCount: n.meta?.evidence_requests?.length ?? 0,
    current: n.selection?.current ?? true,
    policyVersion: n.selection?.policy_version ?? "",
    supportScore: n.selection?.support_score ?? 0,
    evidenceScore: n.selection?.evidence_score ?? 0,
    relationScore: n.selection?.relation_score ?? 0,
    contributions: (n.selection?.contributions ?? []).map((contribution) => ({
      kind: contribution.kind ?? "unknown",
      points: contribution.points ?? 0,
      edgeId: contribution.edge_id ?? "",
      sourceNodeId: contribution.source_node_id ?? null,
      evidenceNodeId: contribution.evidence_node_id ?? null,
      detail: contribution.detail ?? "",
    })),
    exclusions: (n.selection?.exclusions ?? []).map((exclusion) => ({
      kind: exclusion.kind ?? "unknown",
      edgeId: exclusion.edge_id ?? null,
      competingNodeId: exclusion.competing_node_id ?? null,
      detail: exclusion.detail ?? "",
    })),
  };
}

function toTermNode(raw: unknown): GraphNode {
  const term = raw as { id?: string; form?: string };
  return {
    id: term.id ?? "",
    nodeKind: "term",
    statement: term.form ?? "",
    speechAct: "unknown",
    evidenceCount: 0,
    evidenceRequestCount: 0,
    current: true,
    policyVersion: "",
    supportScore: 0,
    evidenceScore: 0,
    relationScore: 0,
    contributions: [],
    exclusions: [],
  };
}

function toDerivedNode(raw: unknown): GraphNode {
  const node = raw as {
    id?: string;
    value?: "evidence" | "assumption" | "guarantee";
    evidence?: { evidence?: { snapshot?: { content_hash?: string } | null } | null };
    assumption?: { expression?: string };
    guarantee?: { expression?: string };
  };
  const nodeKind = node.value ?? "evidence";
  const statement =
    nodeKind === "assumption"
      ? node.assumption?.expression ?? ""
      : nodeKind === "guarantee"
        ? node.guarantee?.expression ?? ""
        : `Evidence ${node.evidence?.evidence?.snapshot?.content_hash ?? ""}`.trim();
  return {
    id: node.id ?? "",
    nodeKind,
    statement,
    speechAct: "unknown",
    evidenceCount: 0,
    evidenceRequestCount: 0,
    current: true,
    policyVersion: "",
    supportScore: 0,
    evidenceScore: 0,
    relationScore: 0,
    contributions: [],
    exclusions: [],
  };
}

function toEdge(raw: unknown): GraphEdge {
  const e = raw as {
    id?: string;
    source?: string;
    target?: string;
    kind?: string;
    family?: string;
    source_role?: string;
    target_role?: string;
    relied_spec_id?: string | null;
    current?: boolean;
    derivation?: { method?: string; version?: string } | null;
  };
  return {
    id: e.id ?? "",
    source: e.source ?? "",
    target: e.target ?? "",
    kind: EDGE_KINDS[e.kind ?? ""] ?? "unspecified",
    family: EDGE_FAMILIES[e.family ?? ""] ?? "unspecified",
    sourceRole: ENDPOINT_ROLES[e.source_role ?? ""] ?? "unspecified",
    targetRole: ENDPOINT_ROLES[e.target_role ?? ""] ?? "unspecified",
    reliedSpecId: e.relied_spec_id ?? null,
    current: e.current ?? true,
    derivationMethod: e.derivation?.method ?? "",
    derivationVersion: e.derivation?.version ?? "",
  };
}
