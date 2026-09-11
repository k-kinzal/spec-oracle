"use client";

import {
  startTransition,
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";
import dynamic from "next/dynamic";
import Legend from "@/components/Legend";
import RelationPanel from "@/components/RelationPanel";
import StatusBar from "@/components/StatusBar";
import ViewSwitcher from "@/components/ViewSwitcher";
import {deriveSupportContexts} from "@/lib/specification-context";
import {isCompleteDefaultTopology} from "@/lib/specification-proximity";
import {
  CONFLICT_EDGE_KINDS,
  PAIRING_EDGE_KINDS,
  DERIVED_NODE_COLORS,
  SPEECH_ACT_COLORS,
  SPEECH_ACT_LABELS,
  TERM_NODE_COLOR,
  type GraphEdge,
  type EdgeKind,
  type GraphNode,
  type GraphPage,
  type LedgerPage,
  type GraphViewMode,
  type SpeechAct,
} from "@/lib/types";

// The Three.js/WebGL renderer and its planar layout Worker are browser-only.
const GraphView = dynamic(() => import("@/components/GraphView"), {
  ssr: false,
});

// --- Scale discipline -------------------------------------------------------
// Fetching and drawing are deliberately separate. The browser receives the
// candidate set in small pages, while the canvas grows on its own fixed
// rendering cadence. Diagnostic views stay bounded; the default proximity
// landscape retains every loaded specification.
const PAGE_SIZE = 100;
const LEDGER_BATCH_EDGES = 4000;
const RENDER_CAP = 50000;
const OVERVIEW_NODE_LIMIT = 1200;
const OVERVIEW_EDGE_LIMIT = 1800;
const TERM_NEIGHBORHOOD_LIMIT = 80;
const TERM_NEIGHBOR_LIMIT = 10;
const UNCONNECTED_SAMPLE_LIMIT = 320;

const VIEW_COPY: Record<GraphViewMode, { title: string; description: string }> = {
  all: {
    title: "Support-context landscape",
    description:
      "Current structural and realization support forms explicit, overlapping context boundaries; ungrounded proximity remains outside them.",
  },
  semantic: {
    title: "Meaning relations",
    description: "Specification-to-specification judgments only; lexical incidence is removed.",
  },
  vocabulary: {
    title: "Vocabulary incidence",
    description: "Exact written term occurrences used for discovery, never as semantic support.",
  },
  refinement: {
    title: "Refinement pairs",
    description: "Directed refiner-to-refined pairs, isolated from every other relation.",
  },
  conflicts: {
    title: "Conflict review",
    description: "Symmetric contradiction, tension, description, and envelope conflicts.",
  },
  isolated: {
    title: "Semantic isolation",
    description: "Specifications with no current proved semantic Edge in the loaded graph.",
  },
  selection: {
    title: "Selection relations",
    description:
      "Versioned Supports, Defeats, and Supersedes judgments; never inferred from semantic arrow direction.",
  },
  fitness: {
    title: "Fitness and exclusions",
    description:
      "Every candidate's versioned Evidence/support score, effective contributions, and exact reason for survival or exclusion.",
  },
  contracts: {
    title: "Assume–guarantee contracts",
    description:
      "Proved pairings show evidence source, explicitly relied assertion, target guarantee, and the materialized current Assumption.",
  },
  ledger: {
    title: "Append-only Ledger",
    description:
      "Every recorded Edge version, with current derivations bright and superseded or historical derivations dimmed for audit.",
  },
  current: {
    title: "Current specification graph",
    description:
      "Selected specifications together with their current Evidence, meaning projections, and relationships.",
  },
};

type LoadState = {
  nodes: Map<string, GraphNode>;
  edges: Map<string, GraphEdge>;
  specificationCount: number;
  nextToken: string;
  total: number;
  reachedEnd: boolean;
};

type VisibleGraph = { nodes: GraphNode[]; edges: GraphEdge[] };

function isTopAssumption(node: GraphNode | undefined): boolean {
  return node?.nodeKind === "assumption" && node.statement.trim() === "⊤";
}

function boundedTopology(
  pool: GraphNode[],
  candidateEdges: GraphEdge[],
  nodeLimit = OVERVIEW_NODE_LIMIT,
  edgeLimit = OVERVIEW_EDGE_LIMIT,
): VisibleGraph {
  const byId = new Map(pool.map((node) => [node.id, node]));
  const selectedIds = new Set<string>();
  const selectedEdgeIds = new Set<string>();
  const selectedEdges: GraphEdge[] = [];

  for (const edge of candidateEdges) {
    if (selectedEdges.length >= edgeLimit || selectedEdgeIds.has(edge.id)) continue;
    if (!byId.has(edge.source) || !byId.has(edge.target)) continue;
    const newIds = [edge.source, edge.target].filter((id) => !selectedIds.has(id));
    if (selectedIds.size + newIds.length > nodeLimit) continue;
    for (const id of newIds) selectedIds.add(id);
    selectedEdgeIds.add(edge.id);
    selectedEdges.push(edge);
  }

  return {
    nodes: pool.filter((node) => selectedIds.has(node.id)),
    edges: selectedEdges,
  };
}

function proximityTermNeighborhoods(
  pool: GraphNode[],
  lexicalEdges: GraphEdge[],
): GraphEdge[] {
  const byId = new Map(pool.map((node) => [node.id, node]));
  const byTerm = new Map<string, Map<string, GraphEdge>>();

  for (const edge of lexicalEdges) {
    const source = byId.get(edge.source);
    const target = byId.get(edge.target);
    const termId =
      source?.nodeKind === "term"
        ? source.id
        : target?.nodeKind === "term"
          ? target.id
          : null;
    if (!termId) continue;
    const specificationId =
      source?.nodeKind === "specification"
        ? source.id
        : target?.nodeKind === "specification"
          ? target.id
          : null;
    if (!specificationId) continue;
    const incident = byTerm.get(termId) ?? new Map<string, GraphEdge>();
    const previous = incident.get(specificationId);
    if (!previous || edge.id.localeCompare(previous.id) < 0) {
      incident.set(specificationId, edge);
    }
    byTerm.set(termId, incident);
  }

  const candidates = [...byTerm.entries()]
    .map(([termId, incident]) => ({
      termId,
      edges: [...incident.values()].sort((left, right) =>
        left.id.localeCompare(right.id),
      ),
    }))
    // A term occurring in only one specification is a useful visible satellite
    // but cannot express proximity between specifications.
    .filter((candidate) => candidate.edges.length > 1);
  const coveredSpecifications = new Set<string>();
  const selected: GraphEdge[] = [];

  for (
    let count = 0;
    count < TERM_NEIGHBORHOOD_LIMIT && candidates.length > 0;
    count += 1
  ) {
    let bestIndex = 0;
    let bestScore = Number.NEGATIVE_INFINITY;
    for (let index = 0; index < candidates.length; index += 1) {
      const candidate = candidates[index];
      const unseen = candidate.edges.filter((edge) => {
        const specificationId = byId.get(edge.source)?.nodeKind === "specification"
          ? edge.source
          : edge.target;
        return !coveredSpecifications.has(specificationId);
      }).length;
      // Marginal coverage keeps independent topology regions in the default
      // view. Total degree only breaks ties, so one huge vocabulary hub cannot
      // consume the complete bounded overview.
      const score =
        Math.min(unseen, TERM_NEIGHBOR_LIMIT) * 1000 +
        Math.min(candidate.edges.length, TERM_NEIGHBOR_LIMIT) * 10 +
        Math.log2(candidate.edges.length + 1);
      if (
        score > bestScore ||
        (score === bestScore &&
          candidate.termId.localeCompare(candidates[bestIndex].termId) < 0)
      ) {
        bestIndex = index;
        bestScore = score;
      }
    }

    const [candidate] = candidates.splice(bestIndex, 1);
    const sample = [...candidate.edges]
      .sort((left, right) => {
        const leftSpecification =
          byId.get(left.source)?.nodeKind === "specification"
            ? left.source
            : left.target;
        const rightSpecification =
          byId.get(right.source)?.nodeKind === "specification"
            ? right.source
            : right.target;
        return (
          Number(coveredSpecifications.has(leftSpecification)) -
            Number(coveredSpecifications.has(rightSpecification)) ||
          left.id.localeCompare(right.id)
        );
      })
      .slice(0, TERM_NEIGHBOR_LIMIT);
    selected.push(...sample);
    for (const edge of sample) {
      coveredSpecifications.add(
        byId.get(edge.source)?.nodeKind === "specification"
          ? edge.source
          : edge.target,
      );
    }
  }

  return selected;
}

function strongestTermNeighborhoods(
  pool: GraphNode[],
  lexicalEdges: GraphEdge[],
): GraphEdge[] {
  const byId = new Map(pool.map((node) => [node.id, node]));
  const byTerm = new Map<string, GraphEdge[]>();
  for (const edge of lexicalEdges) {
    const source = byId.get(edge.source);
    const target = byId.get(edge.target);
    const termId =
      source?.nodeKind === "term"
        ? source.id
        : target?.nodeKind === "term"
          ? target.id
          : null;
    if (!termId) continue;
    const incident = byTerm.get(termId) ?? [];
    incident.push(edge);
    byTerm.set(termId, incident);
  }
  return [...byTerm.entries()]
    .sort(
      ([leftId, left], [rightId, right]) =>
        right.length - left.length || leftId.localeCompare(rightId),
    )
    .slice(0, TERM_NEIGHBORHOOD_LIMIT)
    .flatMap(([, incident]) => incident.slice(0, TERM_NEIGHBOR_LIMIT));
}

function representativeSpecifications(
  specifications: GraphNode[],
  limit = UNCONNECTED_SAMPLE_LIMIT,
): GraphNode[] {
  const groups = new Map<SpeechAct, GraphNode[]>();
  for (const node of specifications) {
    const group = groups.get(node.speechAct) ?? [];
    group.push(node);
    groups.set(node.speechAct, group);
  }
  for (const group of groups.values()) {
    group.sort((left, right) => left.id.localeCompare(right.id));
  }

  const acts = [...groups.keys()].sort();
  const offsets = new Map(acts.map((act) => [act, 0]));
  const result: GraphNode[] = [];
  while (result.length < limit) {
    let added = false;
    for (const act of acts) {
      const group = groups.get(act) ?? [];
      const offset = offsets.get(act) ?? 0;
      if (offset >= group.length) continue;
      result.push(group[offset]);
      offsets.set(act, offset + 1);
      added = true;
      if (result.length >= limit) break;
    }
    if (!added) break;
  }
  return result;
}

function overviewCandidates(
  pool: GraphNode[],
  candidateEdges: GraphEdge[],
  includeTopAssumption = false,
): GraphEdge[] {
  const byId = new Map(pool.map((node) => [node.id, node]));
  // Top is a real, auditable contract assumption but the logical identity
  // carries no contextual information. Letting every unconditional
  // specification share it turns the proximity landscape into one artificial
  // hub. Contracts and Ledger views may opt back in for inspection.
  const proximityEdges = includeTopAssumption
    ? candidateEdges
    : candidateEdges.filter(
        (edge) =>
          !isTopAssumption(byId.get(edge.source)) &&
          !isTopAssumption(byId.get(edge.target)),
      );
  const backbone = proximityEdges.filter(
    (edge) => edge.family === "semantic" || edge.family === "selection",
  );
  const lexical = proximityTermNeighborhoods(
    pool,
    proximityEdges.filter((edge) => edge.family === "lexical"),
  );
  const connected = new Set<string>();
  for (const edge of [...backbone, ...lexical]) {
    connected.add(edge.source);
    connected.add(edge.target);
  }
  const projections = proximityEdges
    .filter(
      (edge) =>
        edge.family === "projection" &&
        (connected.has(edge.source) || connected.has(edge.target)),
    )
    .slice(0, 180);
  return [...backbone, ...lexical, ...projections];
}

function candidateOverview(
  pool: GraphNode[],
  candidateEdges: GraphEdge[],
  includeTopAssumption = false,
): VisibleGraph {
  return boundedTopology(
    pool,
    overviewCandidates(pool, candidateEdges, includeTopAssumption),
  );
}

export default function Page() {
  const [nodes, setNodes] = useState<GraphNode[]>([]);
  const [edges, setEdges] = useState<GraphEdge[]>([]);
  const [total, setTotal] = useState(0);
  const [reachedEnd, setReachedEnd] = useState(false);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selected, setSelected] = useState<GraphNode | null>(null);
  const [view, setView] = useState<GraphViewMode>("all");
  const viewRef = useRef<GraphViewMode>("all");
  const [ledgerNodes, setLedgerNodes] = useState<GraphNode[]>([]);
  const [ledgerEdges, setLedgerEdges] = useState<GraphEdge[]>([]);
  const [ledgerTotal, setLedgerTotal] = useState(0);
  const [ledgerReachedEnd, setLedgerReachedEnd] = useState(false);
  const [ledgerLoading, setLedgerLoading] = useState(false);
  const [overviewAppend, setOverviewAppend] = useState<VisibleGraph>({
    nodes: [],
    edges: [],
  });
  const [overviewSpecificationCount, setOverviewSpecificationCount] = useState(0);
  const [overviewEdgeCount, setOverviewEdgeCount] = useState(0);
  const [overviewSpeechActs, setOverviewSpeechActs] = useState<Set<SpeechAct>>(
    () => new Set(),
  );
  const [overviewEdgeKinds, setOverviewEdgeKinds] = useState<Set<EdgeKind>>(
    () => new Set(),
  );
  const [drawProgress, setDrawProgress] = useState({
    nodes: 0,
    edges: 0,
    actualFps: 0,
    renderMs: 0,
  });
  const [acquisitionPage, setAcquisitionPage] = useState(0);

  // Acquisition may advance as fast as the service responds; GraphView reveals
  // the resulting topology on its own 24 fps cadence.
  const acc = useRef<LoadState>({
    nodes: new Map(),
    edges: new Map(),
    specificationCount: 0,
    nextToken: "",
    total: 0,
    reachedEnd: false,
  });
  const inFlight = useRef(false);
  const overviewWaitingEdges = useRef(new Map<string, GraphEdge>());
  const overviewDrawableEdges = useRef(new Set<string>());
  const ledgerAcc = useRef({
    nodes: new Map<string, GraphNode>(),
    edges: new Map<string, GraphEdge>(),
    nextToken: "",
    total: 0,
    reachedEnd: false,
  });
  const ledgerInFlight = useRef(false);

  const publishGraph = useCallback((
    appendedNodes: GraphNode[],
    appendedEdges: GraphEdge[],
  ) => {
    const accumulated = acc.current;
    // This state is a durable acquisition buffer, not the presentation batch.
    // Functional append prevents React from coalescing two fast page responses
    // into one replacement and losing the earlier page. GraphView remembers
    // the IDs it has already sent to the Worker and consumes only new entries.
    setOverviewAppend((current) => ({
      nodes: [...current.nodes, ...appendedNodes],
      edges: [...current.edges, ...appendedEdges],
    }));
    setOverviewSpecificationCount(accumulated.specificationCount);
    if (appendedNodes.some((node) => node.nodeKind === "specification")) {
      setOverviewSpeechActs((current) => {
        const next = new Set(current);
        for (const node of appendedNodes) {
          if (node.nodeKind === "specification") next.add(node.speechAct);
        }
        return next.size === current.size ? current : next;
      });
    }
    for (const edge of appendedEdges) {
      overviewWaitingEdges.current.set(edge.id, edge);
    }
    const addedEdgeKinds: EdgeKind[] = [];
    for (const [edgeId, edge] of overviewWaitingEdges.current) {
      const source = accumulated.nodes.get(edge.source);
      const target = accumulated.nodes.get(edge.target);
      if (!source || !target) continue;
      overviewWaitingEdges.current.delete(edgeId);
      if (
        source.nodeKind !== "specification" ||
        target.nodeKind !== "specification"
      ) {
        continue;
      }
      overviewDrawableEdges.current.add(edgeId);
      addedEdgeKinds.push(edge.kind);
    }
    setOverviewEdgeCount(overviewDrawableEdges.current.size);
    if (addedEdgeKinds.length > 0) {
      setOverviewEdgeKinds((current) => {
        const next = new Set(current);
        for (const kind of addedEdgeKinds) next.add(kind);
        return next.size === current.size ? current : next;
      });
    }
    // Diagnostic projections are unrelated to the default presentation
    // clock. Keep them out of React entirely until the user opens one; while a
    // diagnostic is open, append only its page delta at transition priority.
    if (viewRef.current !== "all") {
      startTransition(() => {
        if (appendedNodes.length > 0) {
          setNodes((current) => [...current, ...appendedNodes]);
        }
        if (appendedEdges.length > 0) {
          setEdges((current) => [...current, ...appendedEdges]);
        }
      });
    }
    setTotal(accumulated.total);
    setReachedEnd(accumulated.reachedEnd);
  }, []);

  // Fetch exactly one page per request and publish it immediately. The explicit
  // page counter advances continuation even if a page only repeats connector
  // Nodes and therefore does not change the accumulated Node count.
  const loadBatch = useCallback(async () => {
    if (inFlight.current) return;
    if (acc.current.reachedEnd) return;
    const loadedSpecifications = () => acc.current.specificationCount;
    if (loadedSpecifications() >= RENDER_CAP) return;
    inFlight.current = true;
    setLoading(true);
    setError(null);

    try {
      const requestedToken = acc.current.nextToken;
      const params = new URLSearchParams({pageSize: String(PAGE_SIZE)});
      if (requestedToken) params.set("pageToken", requestedToken);
      const res = await fetch(`/api/graph?${params.toString()}`, {
        cache: "no-store",
      });
      if (!res.ok) {
        const body = (await res.json().catch(() => ({}))) as {
          error?: string;
        };
        throw new Error(body.error ?? `graph request failed (${res.status})`);
      }
      const page = (await res.json()) as GraphPage;
      const appendedNodes: GraphNode[] = [];
      const appendedEdges: GraphEdge[] = [];
      for (const node of page.nodes) {
        if (acc.current.nodes.has(node.id)) continue;
        if (
          node.nodeKind === "specification" &&
          acc.current.specificationCount >= RENDER_CAP
        ) {
          continue;
        }
        acc.current.nodes.set(node.id, node);
        appendedNodes.push(node);
        if (node.nodeKind === "specification") {
          acc.current.specificationCount += 1;
        }
      }
      for (const edge of page.edges) {
        if (acc.current.edges.has(edge.id)) continue;
        acc.current.edges.set(edge.id, edge);
        appendedEdges.push(edge);
      }
      acc.current.total = page.totalNodes;
      acc.current.nextToken = page.nextPageToken;
      if (page.nextPageToken === requestedToken && page.nextPageToken) {
        throw new Error("graph pagination returned the same continuation token");
      }
      if (!page.nextPageToken) {
        const specificationCount = loadedSpecifications();
        if (specificationCount < page.totalNodes) {
          throw new Error(
            `graph pagination ended at ${specificationCount} of ${page.totalNodes} Specifications`,
          );
        }
        acc.current.reachedEnd = true;
      }
      publishGraph(appendedNodes, appendedEdges);
      setAcquisitionPage((pageNumber) => pageNumber + 1);
    } catch (e) {
      setError(e instanceof Error ? e.message : "failed to load the graph");
    } finally {
      inFlight.current = false;
      setLoading(false);
    }
  }, [publishGraph]);

  const loadLedger = useCallback(async () => {
    if (ledgerInFlight.current || ledgerAcc.current.reachedEnd) return;
    ledgerInFlight.current = true;
    setLedgerLoading(true);
    setError(null);
    const start = ledgerAcc.current.edges.size;
    try {
      while (
        !ledgerAcc.current.reachedEnd &&
        ledgerAcc.current.edges.size - start < LEDGER_BATCH_EDGES &&
        ledgerAcc.current.edges.size < RENDER_CAP
      ) {
        const params = new URLSearchParams({ pageSize: String(PAGE_SIZE) });
        if (ledgerAcc.current.nextToken) {
          params.set("pageToken", ledgerAcc.current.nextToken);
        }
        const response = await fetch(`/api/ledger?${params.toString()}`, {
          cache: "no-store",
        });
        if (!response.ok) {
          const body = (await response.json().catch(() => ({}))) as { error?: string };
          throw new Error(body.error ?? `Ledger request failed (${response.status})`);
        }
        const page = (await response.json()) as LedgerPage;
        for (const node of page.nodes) ledgerAcc.current.nodes.set(node.id, node);
        for (const edge of page.edges) ledgerAcc.current.edges.set(edge.id, edge);
        ledgerAcc.current.total = page.totalEdges;
        ledgerAcc.current.nextToken = page.nextPageToken;
        if (!page.nextPageToken) ledgerAcc.current.reachedEnd = true;
      }
      const nextEdges = Array.from(ledgerAcc.current.edges.values()).slice(0, RENDER_CAP);
      const visible = new Set<string>();
      for (const edge of nextEdges) {
        visible.add(edge.source);
        visible.add(edge.target);
        if (edge.reliedSpecId) visible.add(edge.reliedSpecId);
      }
      setLedgerEdges(nextEdges);
      setLedgerNodes(
        Array.from(ledgerAcc.current.nodes.values()).filter((node) => visible.has(node.id)),
      );
      setLedgerTotal(ledgerAcc.current.total);
      setLedgerReachedEnd(ledgerAcc.current.reachedEnd);
    } catch (caught) {
      setError(caught instanceof Error ? caught.message : "failed to load the Ledger");
    } finally {
      ledgerInFlight.current = false;
      setLedgerLoading(false);
    }
  }, []);

  // Continue automatically without coupling acquisition to drawing progress.
  useEffect(() => {
    if (
      error ||
      reachedEnd ||
      acc.current.specificationCount >= RENDER_CAP ||
      inFlight.current
    ) {
      return;
    }
    const timer = window.setTimeout(() => void loadBatch(), 0);
    return () => window.clearTimeout(timer);
  }, [acquisitionPage, error, loadBatch, loading, reachedEnd]);

  useEffect(() => {
    if (
      view !== "ledger" ||
      error ||
      ledgerReachedEnd ||
      ledgerEdges.length >= RENDER_CAP ||
      ledgerInFlight.current
    ) {
      return;
    }
    const timer = window.setTimeout(() => void loadLedger(), 0);
    return () => window.clearTimeout(timer);
  }, [error, ledgerEdges.length, ledgerLoading, ledgerReachedEnd, loadLedger, view]);

  const diagnosticsActive = view !== "all";
  const specifications = useMemo(
    () =>
      diagnosticsActive
        ? nodes.filter((node) => node.nodeKind === "specification")
        : [],
    [diagnosticsActive, nodes],
  );
  const semanticEdges = useMemo(
    () =>
      diagnosticsActive
        ? edges.filter((edge) => edge.family === "semantic")
        : [],
    [diagnosticsActive, edges],
  );
  const vocabularyEdges = useMemo(
    () =>
      diagnosticsActive
        ? edges.filter((edge) => edge.family === "lexical")
        : [],
    [diagnosticsActive, edges],
  );
  const selectionEdges = useMemo(
    () =>
      diagnosticsActive
        ? edges.filter((edge) => edge.family === "selection")
        : [],
    [diagnosticsActive, edges],
  );
  const pairingEdges = useMemo(
    () => semanticEdges.filter((edge) => PAIRING_EDGE_KINDS.has(edge.kind)),
    [semanticEdges],
  );
  const contractEdges = useMemo(() => {
    if (!diagnosticsActive) return [];
    const targets = new Set(pairingEdges.map((edge) => edge.target));
    const projections = edges.filter(
      (edge) =>
        targets.has(edge.source) &&
        (edge.kind === "has_assumption" || edge.kind === "has_guarantee"),
    );
    return [...pairingEdges, ...projections];
  }, [diagnosticsActive, edges, pairingEdges]);
  const refinementEdges = useMemo(
    () => semanticEdges.filter((edge) => edge.kind === "refines"),
    [semanticEdges],
  );
  const conflictEdges = useMemo(
    () => semanticEdges.filter((edge) => CONFLICT_EDGE_KINDS.has(edge.kind)),
    [semanticEdges],
  );
  const isolatedNodes = useMemo(() => {
    const related = new Set<string>();
    for (const edge of semanticEdges) {
      related.add(edge.source);
      related.add(edge.target);
    }
    return specifications.filter((node) => !related.has(node.id));
  }, [semanticEdges, specifications]);
  const currentSpecifications = useMemo(
    () => specifications.filter((node) => node.current),
    [specifications],
  );

  const viewGraph = useMemo(() => {
    switch (view) {
      case "all":
        return {nodes: [] as GraphNode[], edges: [] as GraphEdge[]};
      case "semantic":
        return boundedTopology(nodes, semanticEdges);
      case "vocabulary":
        return boundedTopology(
          nodes,
          strongestTermNeighborhoods(nodes, vocabularyEdges),
        );
      case "refinement":
        return boundedTopology(nodes, refinementEdges);
      case "conflicts":
        return boundedTopology(nodes, conflictEdges);
      case "isolated":
        return {
          nodes: representativeSpecifications(isolatedNodes),
          edges: [] as GraphEdge[],
        };
      case "selection":
        return boundedTopology(nodes, selectionEdges);
      case "fitness":
        {
          const ranked = [...specifications].sort(
            (left, right) =>
              right.supportScore - left.supportScore || left.id.localeCompare(right.id),
          );
          const half = Math.floor(UNCONNECTED_SAMPLE_LIMIT / 2);
          const extremes = [...ranked.slice(0, half), ...ranked.slice(-half)];
          return {
            nodes: [...new Map(extremes.map((node) => [node.id, node])).values()],
            edges: [] as GraphEdge[],
          };
        }
      case "contracts":
        return boundedTopology(nodes, contractEdges);
      case "ledger":
        return candidateOverview(
          [...new Map([...nodes, ...ledgerNodes].map((node) => [node.id, node])).values()],
          ledgerEdges,
          true,
        );
      case "current":
        {
          const currentIds = new Set(currentSpecifications.map((node) => node.id));
          const byId = new Map(nodes.map((node) => [node.id, node]));
          const endpointRemains = (id: string) => {
            const node = byId.get(id);
            return Boolean(
              node && (node.nodeKind !== "specification" || currentIds.has(id)),
            );
          };
          const currentEdges = edges.filter(
            (edge) =>
              endpointRemains(edge.source) &&
              endpointRemains(edge.target) &&
              (!edge.reliedSpecId || currentIds.has(edge.reliedSpecId)),
          );
          const currentPool = nodes.filter(
            (node) => node.nodeKind !== "specification" || currentIds.has(node.id),
          );
          return candidateOverview(currentPool, currentEdges);
        }
    }
  }, [
    conflictEdges,
    currentSpecifications,
    edges,
    isolatedNodes,
    nodes,
    refinementEdges,
    semanticEdges,
    selectionEdges,
    contractEdges,
    ledgerEdges,
    ledgerNodes,
    specifications,
    view,
    vocabularyEdges,
  ]);

  const diagnosticPresent = useMemo(() => {
    const s = new Set<SpeechAct>();
    for (const n of viewGraph.nodes) {
      if (n.nodeKind === "specification") s.add(n.speechAct);
    }
    return s;
  }, [viewGraph.nodes]);
  const present = view === "all" ? overviewSpeechActs : diagnosticPresent;
  const loadedSpecifications =
    view === "all" ? overviewSpecificationCount : specifications.length;
  const connectorsAreLayoutOnly = view === "all";
  const viewNodeKinds = useMemo(
    () =>
      connectorsAreLayoutOnly
        ? new Map<string, GraphNode["nodeKind"]>()
        : new Map(viewGraph.nodes.map((node) => [node.id, node.nodeKind])),
    [connectorsAreLayoutOnly, viewGraph.nodes],
  );
  const isPresentedEdge = useCallback(
    (edge: GraphEdge) =>
      !connectorsAreLayoutOnly ||
      (viewNodeKinds.get(edge.source) === "specification" &&
        viewNodeKinds.get(edge.target) === "specification"),
    [connectorsAreLayoutOnly, viewNodeKinds],
  );
  const presentedNodeTotal = connectorsAreLayoutOnly
    ? overviewSpecificationCount
    : viewGraph.nodes.length;
  const presentedEdgeTotal = connectorsAreLayoutOnly
    ? overviewEdgeCount
    : viewGraph.edges.length;
  const diagnosticPresentEdges = useMemo(
    () =>
      new Set<EdgeKind>(
        viewGraph.edges
          .filter(isPresentedEdge)
          .map((edge) => edge.kind),
      ),
    [isPresentedEdge, viewGraph.edges],
  );
  const presentEdges = connectorsAreLayoutOnly
    ? overviewEdgeKinds
    : diagnosticPresentEdges;
  const viewCounts = useMemo<Record<GraphViewMode, number | null>>(
    () => ({
      all: overviewSpecificationCount,
      semantic: semanticEdges.length,
      vocabulary: vocabularyEdges.length,
      refinement: refinementEdges.length,
      conflicts: conflictEdges.length,
      isolated: isolatedNodes.length,
      selection: selectionEdges.length,
      fitness: specifications.length,
      contracts: pairingEdges.length,
      ledger: ledgerTotal || ledgerEdges.length,
      current: currentSpecifications.length,
    }),
    [
      conflictEdges.length,
      currentSpecifications.length,
      isolatedNodes.length,
      specifications.length,
      refinementEdges.length,
      semanticEdges.length,
      selectionEdges.length,
      pairingEdges.length,
      ledgerEdges.length,
      ledgerTotal,
      overviewSpecificationCount,
      vocabularyEdges.length,
    ],
  );

  const selectedSemanticRelations = useMemo(
    () =>
      selected
        ? semanticEdges.filter(
            (edge) =>
            edge.source === selected.id ||
            edge.target === selected.id ||
            edge.reliedSpecId === selected.id,
          ).length
        : 0,
    [selected, semanticEdges],
  );
  const selectedSelectionRelations = useMemo(
    () =>
      selected
        ? selectionEdges.filter(
            (edge) => edge.source === selected.id || edge.target === selected.id,
          ).length
        : 0,
    [selected, selectionEdges],
  );

  const showingLedger = view === "ledger";
  const complete = showingLedger ? ledgerReachedEnd : reachedEnd;
  const atHardCap = showingLedger
    ? ledgerEdges.length >= RENDER_CAP && !ledgerReachedEnd
    : overviewSpecificationCount >= RENDER_CAP && !reachedEnd;
  const copy = VIEW_COPY[view];
  const topologyReady =
    complete &&
    (!connectorsAreLayoutOnly ||
      isCompleteDefaultTopology(complete, presentedNodeTotal, total));

  const changeView = useCallback((next: GraphViewMode) => {
    setSelected(null);
    setDrawProgress({
      nodes: 0,
      edges: 0,
      actualFps: 0,
      renderMs: 0,
    });
    if (next === "all" && view !== "all") {
      setOverviewAppend({
        nodes: Array.from(acc.current.nodes.values()),
        edges: Array.from(acc.current.edges.values()),
      });
    } else if (next !== "all" && view === "all") {
      setNodes(Array.from(acc.current.nodes.values()));
      setEdges(Array.from(acc.current.edges.values()));
    }
    viewRef.current = next;
    setView(next);
  }, [view]);
  const updateDrawProgress = useCallback(
    (
      drawnNodes: number,
      drawnEdges: number,
      actualFps: number,
      renderMs: number,
    ) => {
      const roundedFps = Math.round(actualFps * 10) / 10;
      const roundedRenderMs = Math.round(renderMs * 10) / 10;
      setDrawProgress((previous) =>
        previous.nodes === drawnNodes &&
        previous.edges === drawnEdges &&
        previous.actualFps === roundedFps &&
        previous.renderMs === roundedRenderMs
          ? previous
          : {
              nodes: drawnNodes,
              edges: drawnEdges,
              actualFps: roundedFps,
              renderMs: roundedRenderMs,
            },
      );
    },
    [],
  );
  const drawing =
    drawProgress.nodes < presentedNodeTotal ||
    drawProgress.edges < presentedEdgeTotal;
  const graphViewNodes = view === "all" ? overviewAppend.nodes : viewGraph.nodes;
  const graphViewEdges = view === "all" ? overviewAppend.edges : viewGraph.edges;
  const supportContexts = useMemo(
    () => deriveSupportContexts(graphViewNodes),
    [graphViewNodes],
  );
  const selectedSupportContexts = useMemo(() => {
    if (!selected) return [];
    const contextIds = new Set(
      supportContexts.membership.get(selected.id) ?? [],
    );
    return supportContexts.contexts.filter((context) =>
      contextIds.has(context.id),
    );
  }, [selected, supportContexts]);

  return (
    <main className="stage">
      {graphViewNodes.length > 0 && (
        <GraphView
          key={view}
          nodes={graphViewNodes}
          links={graphViewEdges}
          supportContexts={supportContexts}
          onSelect={setSelected}
          onDrawProgress={updateDrawProgress}
          withInspector={view !== "all"}
          hideLayoutConnectors={connectorsAreLayoutOnly}
          topologyComplete={topologyReady}
        />
      )}

      <div className="topbar">
        <div className="title panel">
          <h1>spec-oracle · graph view</h1>
          <p>
            <strong>{copy.title}</strong> · {copy.description}
            <span className="scope">
              Drawing {drawProgress.nodes.toLocaleString()} of{" "}
              {presentedNodeTotal.toLocaleString()} visible nodes ·{" "}
              {drawProgress.edges.toLocaleString()} of{" "}
              {presentedEdgeTotal.toLocaleString()} visible edges · XY · target 24 fps
              {drawProgress.actualFps > 0
                ? ` · actual ${drawProgress.actualFps.toFixed(1)} fps · submit ${drawProgress.renderMs.toFixed(1)} ms`
                : ""}
              {supportContexts.contexts.length > 0
                ? ` · ${supportContexts.contexts.length.toLocaleString()} support contexts · ${supportContexts.contextualizedNodeCount.toLocaleString()} contextualized`
                : ""}
            </span>
          </p>
        </div>
        <StatusBar
          loaded={showingLedger ? ledgerEdges.length : loadedSpecifications}
          total={showingLedger ? ledgerTotal : total}
          loading={showingLedger ? ledgerLoading : loading}
          complete={complete}
          atHardCap={atHardCap}
          drawing={drawing}
          unit={showingLedger ? "Ledger edges" : "specifications"}
        />
      </div>

      <ViewSwitcher active={view} counts={viewCounts} onChange={changeView} />

      <Legend
        present={present}
        termPresent={
          !connectorsAreLayoutOnly &&
          viewGraph.nodes.some((node) => node.nodeKind === "term")
        }
        edgePresent={presentEdges}
        supportContextCount={supportContexts.contexts.length}
        contextualizedNodeCount={supportContexts.contextualizedNodeCount}
        sharedFoundationCount={supportContexts.sharedFoundationCount}
      />

      <RelationPanel
        mode={view}
        nodes={viewGraph.nodes}
        edges={viewGraph.edges}
        population={view === "isolated" ? isolatedNodes : specifications}
        populationComplete={reachedEnd}
        onSelect={setSelected}
      />

      {selected && (
        <div className={view === "all" ? "detail panel" : "detail panel detail-with-panel"}>
          <button
            className="close"
            onClick={() => setSelected(null)}
            aria-label="close"
          >
            ×
          </button>
          <div className="kicker">
            <span
              className="dot"
              style={{
                width: 9,
                height: 9,
                borderRadius: "50%",
                display: "inline-block",
                background:
                  selected.nodeKind === "term"
                    ? TERM_NODE_COLOR
                    : selected.nodeKind === "specification"
                      ? SPEECH_ACT_COLORS[selected.speechAct]
                      : DERIVED_NODE_COLORS[selected.nodeKind],
              }}
            />
            {selected.nodeKind === "term"
              ? "Written term form · lexical connector"
              : selected.nodeKind === "specification"
                ? `${SPEECH_ACT_LABELS[selected.speechAct]} · ${selected.evaluationState ?? (selected.current ? "current" : "receded")} · fitness ${selected.supportScore >= 0 ? "+" : ""}${selected.supportScore} (${selected.structuralScore ?? 0} structural, ${selected.evidenceScore >= 0 ? "+" : ""}${selected.evidenceScore} Evidence, -${selected.conflictPressure ?? 0} conflict) · ${selected.policyVersion || "policy unavailable"}`
                : `${selected.nodeKind[0].toUpperCase()}${selected.nodeKind.slice(1)} node · shared content-addressed projection`}
          </div>
          <div className="statement">{selected.statement}</div>
          {selectedSupportContexts.length > 0 && (
            <div className="support-context-detail">
              <strong>
                {selectedSupportContexts.length === 1
                  ? "Support context"
                  : `${selectedSupportContexts.length} overlapping support contexts`}
              </strong>
              {selectedSupportContexts.slice(0, 4).map((context) => (
                <div key={context.id}>
                  <span>{context.memberIds.length} specifications</span>
                  {context.anchorIds.includes(selected.id)
                    ? " · anchor"
                    : " · supports"}{" "}
                  “{context.anchorStatement}”
                </div>
              ))}
              {selectedSupportContexts.length > 4 && (
                <div>+{selectedSupportContexts.length - 4} more contexts</div>
              )}
            </div>
          )}
          {selected.nodeKind === "specification" && (
            <div className="fitness-detail">
              {selected.contributions.map((contribution) => (
                <div key={`${contribution.edgeId}-${contribution.kind}`}>
                  <strong>
                    {contribution.points >= 0 ? "+" : ""}
                    {contribution.points} · {contribution.kind}
                  </strong>{" "}
                  {contribution.detail}
                </div>
              ))}
              {selected.exclusions.map((exclusion, index) => (
                <div key={`${exclusion.edgeId ?? "score"}-${exclusion.kind}-${index}`}>
                  <strong>Excluded · {exclusion.kind}</strong> {exclusion.detail}
                </div>
              ))}
            </div>
          )}
          <div className="id">{selected.id}</div>
        </div>
      )}

      {!loading &&
        overviewSpecificationCount > 0 &&
        viewGraph.nodes.length === 0 &&
        view !== "all" &&
        !error && (
          <div className="view-empty">
            <div className="panel">
              <h2>No result in this view</h2>
              <p>{copy.description}</p>
            </div>
          </div>
        )}

      {!loading && overviewSpecificationCount === 0 && !error && (
        <div className="overlay">
          <div className="panel">
            <h2>No nodes yet</h2>
            <p>
              The specification graph is empty. Add one with{" "}
              <code>spec add &quot;The pump shall stop.&quot;</code> and reload.
            </p>
          </div>
        </div>
      )}

      {error && (
        <div className="overlay">
          <div className="panel">
            <h2>Could not load the graph</h2>
            <p>{error}</p>
            <p>
              Is <code>specd</code> running and reachable at{" "}
              <code>SPEC_ORACLE_GRPC_ADDR</code>?
            </p>
          </div>
        </div>
      )}
    </main>
  );
}
