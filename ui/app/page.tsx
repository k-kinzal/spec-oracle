"use client";

import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import dynamic from "next/dynamic";
import Legend from "@/components/Legend";
import RelationPanel from "@/components/RelationPanel";
import StatusBar from "@/components/StatusBar";
import ViewSwitcher from "@/components/ViewSwitcher";
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

// The Three.js/WebGL renderer and its 3D layout Worker are browser-only.
const GraphView = dynamic(() => import("@/components/GraphView"), {
  ssr: false,
});

// --- Scale discipline -------------------------------------------------------
// Fetching and drawing are deliberately separate. The browser receives the
// candidate set in small pages, while the canvas grows a bounded connected
// overview on its own fixed rendering cadence.
const PAGE_SIZE = 100;
const LEDGER_BATCH_EDGES = 4000;
const RENDER_CAP = 50000;
const OVERVIEW_NODE_LIMIT = 1200;
const OVERVIEW_EDGE_LIMIT = 1800;
const TERM_HUB_LIMIT = 36;
const TERM_NEIGHBOR_LIMIT = 10;
const UNCONNECTED_SAMPLE_LIMIT = 320;

const VIEW_COPY: Record<GraphViewMode, { title: string; description: string }> = {
  all: {
    title: "Largest connected candidate neighborhood",
    description:
      "The largest connected semantic and shared-term neighborhood; all candidates remain loaded for the diagnostic views.",
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
  nextToken: string;
  total: number;
  reachedEnd: boolean;
};

type VisibleGraph = { nodes: GraphNode[]; edges: GraphEdge[] };

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
    .slice(0, TERM_HUB_LIMIT)
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

function largestConnectedComponent(graph: VisibleGraph): VisibleGraph {
  if (graph.nodes.length === 0) return graph;
  const adjacent = new Map(graph.nodes.map((node) => [node.id, new Set<string>()]));
  for (const edge of graph.edges) {
    adjacent.get(edge.source)?.add(edge.target);
    adjacent.get(edge.target)?.add(edge.source);
  }

  const unvisited = new Set(graph.nodes.map((node) => node.id));
  let largest = new Set<string>();
  while (unvisited.size > 0) {
    const first = unvisited.values().next().value as string | undefined;
    if (!first) break;
    const component = new Set<string>();
    const queue = [first];
    unvisited.delete(first);
    while (queue.length > 0) {
      const id = queue.shift();
      if (!id) continue;
      component.add(id);
      for (const neighbor of adjacent.get(id) ?? []) {
        if (!unvisited.delete(neighbor)) continue;
        queue.push(neighbor);
      }
    }
    if (component.size > largest.size) largest = component;
  }

  return {
    nodes: graph.nodes.filter((node) => largest.has(node.id)),
    edges: graph.edges.filter(
      (edge) => largest.has(edge.source) && largest.has(edge.target),
    ),
  };
}

function overviewCandidates(pool: GraphNode[], candidateEdges: GraphEdge[]): GraphEdge[] {
  const backbone = candidateEdges.filter(
    (edge) => edge.family === "semantic" || edge.family === "selection",
  );
  const lexical = strongestTermNeighborhoods(
    pool,
    candidateEdges.filter((edge) => edge.family === "lexical"),
  );
  const connected = new Set<string>();
  for (const edge of [...backbone, ...lexical]) {
    connected.add(edge.source);
    connected.add(edge.target);
  }
  const projections = candidateEdges
    .filter(
      (edge) =>
        edge.family === "projection" &&
        (connected.has(edge.source) || connected.has(edge.target)),
    )
    .slice(0, 180);
  return [...backbone, ...lexical, ...projections];
}

function candidateOverview(pool: GraphNode[], candidateEdges: GraphEdge[]): VisibleGraph {
  return largestConnectedComponent(
    boundedTopology(pool, overviewCandidates(pool, candidateEdges)),
  );
}

// Once a node has appeared in the overview, keep it there. Later acquisition
// pages may extend the connected neighborhood, but they must not replace the
// viewer's existing spatial landmarks with a newly ranked graph.
function extendCandidateOverview(
  previous: VisibleGraph,
  pool: GraphNode[],
  candidateEdges: GraphEdge[],
): VisibleGraph {
  if (previous.nodes.length === 0) return candidateOverview(pool, candidateEdges);

  const byId = new Map(pool.map((node) => [node.id, node]));
  const edgeById = new Map(candidateEdges.map((edge) => [edge.id, edge]));
  const selectedIds = new Set(
    previous.nodes.filter((node) => byId.has(node.id)).map((node) => node.id),
  );
  const selectedEdgeIds = new Set(
    previous.edges.filter((edge) => edgeById.has(edge.id)).map((edge) => edge.id),
  );
  const nextNodeIds = previous.nodes
    .map((node) => node.id)
    .filter((id) => selectedIds.has(id));
  const nextEdgeIds = previous.edges
    .map((edge) => edge.id)
    .filter((id) => selectedEdgeIds.has(id));
  const candidates = overviewCandidates(pool, candidateEdges);
  let changed = false;

  // First retain every newly discovered relationship between visible nodes.
  for (const edge of candidates) {
    if (nextEdgeIds.length >= OVERVIEW_EDGE_LIMIT) break;
    if (selectedEdgeIds.has(edge.id)) continue;
    if (!selectedIds.has(edge.source) || !selectedIds.has(edge.target)) continue;
    selectedEdgeIds.add(edge.id);
    nextEdgeIds.push(edge.id);
    changed = true;
  }

  // Then grow only from the existing component. Repeating the pass allows a
  // newly attached node to become an anchor for another node in the same page.
  let extended = true;
  while (
    extended &&
    nextNodeIds.length < OVERVIEW_NODE_LIMIT &&
    nextEdgeIds.length < OVERVIEW_EDGE_LIMIT
  ) {
    extended = false;
    for (const edge of candidates) {
      if (
        nextNodeIds.length >= OVERVIEW_NODE_LIMIT ||
        nextEdgeIds.length >= OVERVIEW_EDGE_LIMIT
      ) {
        break;
      }
      if (selectedEdgeIds.has(edge.id)) continue;
      const sourceSelected = selectedIds.has(edge.source);
      const targetSelected = selectedIds.has(edge.target);
      if (sourceSelected === targetSelected) continue;
      const newId = sourceSelected ? edge.target : edge.source;
      if (!byId.has(newId)) continue;
      selectedIds.add(newId);
      nextNodeIds.push(newId);
      selectedEdgeIds.add(edge.id);
      nextEdgeIds.push(edge.id);
      extended = true;
      changed = true;
    }
  }

  if (!changed) return previous;
  return {
    nodes: nextNodeIds.flatMap((id) => {
      const node = byId.get(id);
      return node ? [node] : [];
    }),
    edges: nextEdgeIds.flatMap((id) => {
      const edge = edgeById.get(id);
      return edge ? [edge] : [];
    }),
  };
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
  const [ledgerNodes, setLedgerNodes] = useState<GraphNode[]>([]);
  const [ledgerEdges, setLedgerEdges] = useState<GraphEdge[]>([]);
  const [ledgerTotal, setLedgerTotal] = useState(0);
  const [ledgerReachedEnd, setLedgerReachedEnd] = useState(false);
  const [ledgerLoading, setLedgerLoading] = useState(false);
  const [overviewGraph, setOverviewGraph] = useState<VisibleGraph>({
    nodes: [],
    edges: [],
  });
  const [drawProgress, setDrawProgress] = useState({
    nodes: 0,
    edges: 0,
    actualFps: 0,
    renderMs: 0,
  });

  // Acquisition may advance as fast as the service responds; GraphView reveals
  // the resulting topology on its own 24 fps cadence.
  const acc = useRef<LoadState>({
    nodes: new Map(),
    edges: new Map(),
    nextToken: "",
    total: 0,
    reachedEnd: false,
  });
  const inFlight = useRef(false);
  const ledgerAcc = useRef({
    nodes: new Map<string, GraphNode>(),
    edges: new Map<string, GraphEdge>(),
    nextToken: "",
    total: 0,
    reachedEnd: false,
  });
  const ledgerInFlight = useRef(false);

  const publishGraph = useCallback(() => {
    const accumulated = acc.current;
    const nextNodes = Array.from(accumulated.nodes.values()).slice(0, RENDER_CAP);
    const visible = new Set(nextNodes.map((node) => node.id));
    setNodes(nextNodes);
    const nextEdges = Array.from(accumulated.edges.values()).filter(
      (edge) =>
        visible.has(edge.source) &&
        visible.has(edge.target) &&
        (!edge.reliedSpecId || visible.has(edge.reliedSpecId)),
    );
    setEdges(nextEdges);
    setOverviewGraph((previous) =>
      extendCandidateOverview(previous, nextNodes, nextEdges),
    );
    setTotal(accumulated.total);
    setReachedEnd(accumulated.reachedEnd);
  }, []);

  // Fetch exactly one page per request. The continuation effect starts the next
  // request immediately; it never waits for the drawing queue to catch up.
  const loadBatch = useCallback(async () => {
    if (inFlight.current) return;
    if (acc.current.reachedEnd) return;
    if (acc.current.nodes.size >= RENDER_CAP) return;
    inFlight.current = true;
    setLoading(true);
    setError(null);

    try {
      const params = new URLSearchParams({ pageSize: String(PAGE_SIZE) });
      if (acc.current.nextToken) params.set("pageToken", acc.current.nextToken);
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
      for (const n of page.nodes) acc.current.nodes.set(n.id, n);
      for (const e of page.edges) acc.current.edges.set(e.id, e);
      acc.current.total = page.totalNodes;
      acc.current.nextToken = page.nextPageToken;
      if (!page.nextPageToken) acc.current.reachedEnd = true;
      publishGraph();
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
    if (error || reachedEnd || nodes.length >= RENDER_CAP || inFlight.current) {
      return;
    }
    const timer = window.setTimeout(() => void loadBatch(), 0);
    return () => window.clearTimeout(timer);
  }, [error, loadBatch, loading, nodes.length, reachedEnd]);

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

  const specifications = useMemo(
    () => nodes.filter((node) => node.nodeKind === "specification"),
    [nodes],
  );
  const semanticEdges = useMemo(
    () => edges.filter((edge) => edge.family === "semantic"),
    [edges],
  );
  const vocabularyEdges = useMemo(
    () => edges.filter((edge) => edge.family === "lexical"),
    [edges],
  );
  const selectionEdges = useMemo(
    () => edges.filter((edge) => edge.family === "selection"),
    [edges],
  );
  const pairingEdges = useMemo(
    () => semanticEdges.filter((edge) => PAIRING_EDGE_KINDS.has(edge.kind)),
    [semanticEdges],
  );
  const contractEdges = useMemo(() => {
    const targets = new Set(pairingEdges.map((edge) => edge.target));
    const projections = edges.filter(
      (edge) =>
        targets.has(edge.source) &&
        (edge.kind === "has_assumption" || edge.kind === "has_guarantee"),
    );
    return [...pairingEdges, ...projections];
  }, [edges, pairingEdges]);
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
        return overviewGraph;
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
    overviewGraph,
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

  const present = useMemo(() => {
    const s = new Set<SpeechAct>();
    for (const n of viewGraph.nodes) {
      if (n.nodeKind === "specification") s.add(n.speechAct);
    }
    return s;
  }, [viewGraph.nodes]);
  const loadedSpecifications = specifications.length;
  const presentEdges = useMemo(
    () => new Set<EdgeKind>(viewGraph.edges.map((edge) => edge.kind)),
    [viewGraph.edges],
  );
  const viewCounts = useMemo<Record<GraphViewMode, number | null>>(
    () => ({
      all: specifications.length,
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
    : nodes.length >= RENDER_CAP && !reachedEnd;
  const copy = VIEW_COPY[view];

  const changeView = useCallback((next: GraphViewMode) => {
    setSelected(null);
    setDrawProgress({ nodes: 0, edges: 0, actualFps: 0, renderMs: 0 });
    setView(next);
  }, []);
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
    drawProgress.nodes < viewGraph.nodes.length ||
    drawProgress.edges < viewGraph.edges.length;

  return (
    <main className="stage">
      {viewGraph.nodes.length > 0 && (
        <GraphView
          key={view}
          nodes={viewGraph.nodes}
          links={viewGraph.edges}
          onSelect={setSelected}
          onDrawProgress={updateDrawProgress}
          withInspector={view !== "all"}
        />
      )}

      <div className="topbar">
        <div className="title panel">
          <h1>spec-oracle · graph view</h1>
          <p>
            <strong>{copy.title}</strong> · {copy.description}
            <span className="scope">
              Drawing {drawProgress.nodes.toLocaleString()} of{" "}
              {viewGraph.nodes.length.toLocaleString()} nodes ·{" "}
              {drawProgress.edges.toLocaleString()} of{" "}
              {viewGraph.edges.length.toLocaleString()} edges · 3D · target 24 fps
              {drawProgress.actualFps > 0
                ? ` · actual ${drawProgress.actualFps.toFixed(1)} fps · submit ${drawProgress.renderMs.toFixed(1)} ms`
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
        termPresent={viewGraph.nodes.some((node) => node.nodeKind === "term")}
        edgePresent={presentEdges}
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
                ? `${SPEECH_ACT_LABELS[selected.speechAct]} · ${selected.current ? "current" : "non-current"} · fitness ${selected.supportScore >= 0 ? "+" : ""}${selected.supportScore} (${selected.evidenceScore >= 0 ? "+" : ""}${selected.evidenceScore} Evidence, ${selected.relationScore >= 0 ? "+" : ""}${selected.relationScore} relations) · ${selected.policyVersion || "policy unavailable"}`
                : `${selected.nodeKind[0].toUpperCase()}${selected.nodeKind.slice(1)} node · shared content-addressed projection`}
          </div>
          <div className="statement">{selected.statement}</div>
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
        nodes.length > 0 &&
        viewGraph.nodes.length === 0 &&
        !error && (
          <div className="view-empty">
            <div className="panel">
              <h2>No result in this view</h2>
              <p>{copy.description}</p>
            </div>
          </div>
        )}

      {!loading && nodes.length === 0 && !error && (
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
