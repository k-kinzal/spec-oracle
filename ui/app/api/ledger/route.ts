// Bounded append-only Ledger Edge page. Authored Specification Nodes are
// already loaded through /api/graph; this route supplies historical topology
// plus any non-Specification endpoint values needed to render that page.

import { NextRequest, NextResponse } from "next/server";
import { getLedger } from "@/lib/grpc";
import type {
  EdgeFamily,
  EdgeKind,
  EndpointRole,
  GraphEdge,
  GraphNode,
} from "@/lib/types";

export const runtime = "nodejs";
export const dynamic = "force-dynamic";

const MAX_PAGE_SIZE = 1000;

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

export async function GET(req: NextRequest) {
  const params = req.nextUrl.searchParams;
  const rawSize = Number(params.get("pageSize"));
  const pageSize = Number.isFinite(rawSize)
    ? Math.min(Math.max(0, Math.trunc(rawSize)), MAX_PAGE_SIZE)
    : 0;
  const pageToken = params.get("pageToken") ?? "";
  try {
    const page = await getLedger(pageSize, pageToken);
    return NextResponse.json({
      nodes: [
        ...(page.term_nodes ?? []).map(toTermNode),
        ...(page.derived_nodes ?? []).map(toDerivedNode),
      ],
      edges: (page.edges ?? []).map(toEdge),
      nextPageToken: page.next_page_token ?? "",
      totalEdges: Number(page.total_edges ?? 0),
    });
  } catch (error) {
    const message = error instanceof Error ? error.message : "Ledger read failed";
    return NextResponse.json({ error: message }, { status: 502 });
  }
}

function baseNode(id: string, nodeKind: GraphNode["nodeKind"], statement: string): GraphNode {
  return {
    id,
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

function toTermNode(raw: unknown): GraphNode {
  const term = raw as { id?: string; form?: string };
  return baseNode(term.id ?? "", "term", term.form ?? "");
}

function toDerivedNode(raw: unknown): GraphNode {
  const node = raw as {
    id?: string;
    value?: "evidence" | "assumption" | "guarantee";
    evidence?: { evidence?: { snapshot?: { content_hash?: string } | null } | null };
    assumption?: { expression?: string };
    guarantee?: { expression?: string };
  };
  const kind = node.value ?? "evidence";
  const statement =
    kind === "assumption"
      ? node.assumption?.expression ?? ""
      : kind === "guarantee"
        ? node.guarantee?.expression ?? ""
        : `Evidence ${node.evidence?.evidence?.snapshot?.content_hash ?? ""}`.trim();
  return baseNode(node.id ?? "", kind, statement);
}

function toEdge(raw: unknown): GraphEdge {
  const edge = raw as {
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
    id: edge.id ?? "",
    source: edge.source ?? "",
    target: edge.target ?? "",
    kind: EDGE_KINDS[edge.kind ?? ""] ?? "unspecified",
    family: EDGE_FAMILIES[edge.family ?? ""] ?? "unspecified",
    sourceRole: ENDPOINT_ROLES[edge.source_role ?? ""] ?? "unspecified",
    targetRole: ENDPOINT_ROLES[edge.target_role ?? ""] ?? "unspecified",
    reliedSpecId: edge.relied_spec_id ?? null,
    current: edge.current ?? false,
    derivationMethod: edge.derivation?.method ?? "",
    derivationVersion: edge.derivation?.version ?? "",
  };
}
