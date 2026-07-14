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
};

function toNode(raw: unknown): GraphNode {
  const n = raw as {
    id?: string;
    statement?: string;
    sentence?: { speech_act?: string } | null;
    meta?: { evidence?: unknown[]; evidence_requests?: unknown[] } | null;
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
    derivationMethod: e.derivation?.method ?? "",
    derivationVersion: e.derivation?.version ?? "",
  };
}
