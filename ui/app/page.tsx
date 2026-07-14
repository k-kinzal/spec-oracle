"use client";

import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import dynamic from "next/dynamic";
import Legend from "@/components/Legend";
import RelationPanel from "@/components/RelationPanel";
import StatusBar from "@/components/StatusBar";
import ViewSwitcher from "@/components/ViewSwitcher";
import {
  CONFLICT_EDGE_KINDS,
  DERIVED_NODE_COLORS,
  SPEECH_ACT_COLORS,
  SPEECH_ACT_LABELS,
  TERM_NODE_COLOR,
  type GraphEdge,
  type EdgeKind,
  type GraphNode,
  type GraphPage,
  type GraphViewMode,
  type SpeechAct,
} from "@/lib/types";

// Cosmograph is WebGL/browser-only, so load it without SSR.
const GraphView = dynamic(() => import("@/components/GraphView"), {
  ssr: false,
});

// --- Scale discipline -------------------------------------------------------
// The graph can hold billions of nodes; the browser cannot. So we never ask for
// "everything": we pull the graph in bounded pages and cap what we render.
//   PAGE_SIZE     — nodes per gRPC page (the daemon's own hard maximum).
//   BATCH_NODES   — nodes pulled per auto-load / "Load more" (several pages).
//   RENDER_CAP    — absolute ceiling on nodes held in the browser, to protect it.
const PAGE_SIZE = 1000;
const BATCH_NODES = 4000;
const RENDER_CAP = 50000;

const VIEW_COPY: Record<GraphViewMode, { title: string; description: string }> = {
  all: {
    title: "Complete loaded graph",
    description: "Specifications, written term forms, and every current checked Edge.",
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
  current: {
    title: "Current specification set",
    description: "Reserved for a selected view once support and selection semantics exist.",
  },
};

type LoadState = {
  nodes: Map<string, GraphNode>;
  edges: Map<string, GraphEdge>;
  nextToken: string;
  total: number;
  reachedEnd: boolean;
};

export default function Page() {
  const [nodes, setNodes] = useState<GraphNode[]>([]);
  const [edges, setEdges] = useState<GraphEdge[]>([]);
  const [total, setTotal] = useState(0);
  const [reachedEnd, setReachedEnd] = useState(false);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [selected, setSelected] = useState<GraphNode | null>(null);
  const [view, setView] = useState<GraphViewMode>("all");

  // The accumulator lives in a ref so paging never races the React state, which
  // we publish once per batch (re-rendering the WebGL graph on every page would
  // thrash the simulation).
  const acc = useRef<LoadState>({
    nodes: new Map(),
    edges: new Map(),
    nextToken: "",
    total: 0,
    reachedEnd: false,
  });
  const inFlight = useRef(false);

  const publish = useCallback(() => {
    const a = acc.current;
    setNodes(Array.from(a.nodes.values()));
    // A semantic Edge is emitted on one deterministic endpoint's page and its
    // other endpoint may arrive later. Retain it in the accumulator but expose
    // it to Cosmograph only after both endpoints are loaded.
    setEdges(
      Array.from(a.edges.values()).filter(
        (edge) => a.nodes.has(edge.source) && a.nodes.has(edge.target),
      ),
    );
    setTotal(a.total);
    setReachedEnd(a.reachedEnd);
  }, []);

  // Pull one bounded batch (up to BATCH_NODES new nodes, several pages), then
  // publish. Guarded so overlapping calls (mount + click) cannot double-load.
  const loadBatch = useCallback(async () => {
    if (inFlight.current) return;
    if (acc.current.reachedEnd) return;
    if (acc.current.nodes.size >= RENDER_CAP) return;
    inFlight.current = true;
    setLoading(true);
    setError(null);

    const start = acc.current.nodes.size;
    try {
      while (
        !acc.current.reachedEnd &&
        acc.current.nodes.size - start < BATCH_NODES &&
        acc.current.nodes.size < RENDER_CAP
      ) {
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
      }
      publish();
    } catch (e) {
      setError(e instanceof Error ? e.message : "failed to load the graph");
    } finally {
      inFlight.current = false;
      setLoading(false);
    }
  }, [publish]);

  // Initial load on mount.
  useEffect(() => {
    void loadBatch();
  }, [loadBatch]);

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

  const viewGraph = useMemo(() => {
    const endpoints = (selectedEdges: GraphEdge[]) => {
      const ids = new Set<string>();
      for (const edge of selectedEdges) {
        ids.add(edge.source);
        ids.add(edge.target);
      }
      return nodes.filter((node) => ids.has(node.id));
    };
    switch (view) {
      case "all":
        return { nodes, edges };
      case "semantic":
        return { nodes: specifications, edges: semanticEdges };
      case "vocabulary":
        return { nodes: endpoints(vocabularyEdges), edges: vocabularyEdges };
      case "refinement":
        return { nodes: endpoints(refinementEdges), edges: refinementEdges };
      case "conflicts":
        return { nodes: endpoints(conflictEdges), edges: conflictEdges };
      case "isolated":
        return { nodes: isolatedNodes, edges: [] as GraphEdge[] };
      case "selection":
        return { nodes: endpoints(selectionEdges), edges: selectionEdges };
      case "current":
        return { nodes: [] as GraphNode[], edges: [] as GraphEdge[] };
    }
  }, [
    conflictEdges,
    edges,
    isolatedNodes,
    nodes,
    refinementEdges,
    semanticEdges,
    selectionEdges,
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
      all: nodes.length,
      semantic: semanticEdges.length,
      vocabulary: vocabularyEdges.length,
      refinement: refinementEdges.length,
      conflicts: conflictEdges.length,
      isolated: isolatedNodes.length,
      selection: selectionEdges.length,
      current: null,
    }),
    [
      conflictEdges.length,
      isolatedNodes.length,
      nodes.length,
      refinementEdges.length,
      semanticEdges.length,
      selectionEdges.length,
      vocabularyEdges.length,
    ],
  );

  const selectedSemanticRelations = useMemo(
    () =>
      selected
        ? semanticEdges.filter(
            (edge) => edge.source === selected.id || edge.target === selected.id,
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

  const atHardCap = nodes.length >= RENDER_CAP && !reachedEnd;
  const canLoadMore = !reachedEnd && !atHardCap;
  const copy = VIEW_COPY[view];

  const changeView = useCallback((next: GraphViewMode) => {
    setSelected(null);
    setView(next);
  }, []);

  return (
    <main className="stage">
      {viewGraph.nodes.length > 0 && (
        <GraphView
          key={view}
          nodes={viewGraph.nodes}
          links={viewGraph.edges}
          onSelect={setSelected}
        />
      )}

      <div className="topbar">
        <div className="title panel">
          <h1>spec-oracle · graph view</h1>
          <p>
            <strong>{copy.title}</strong> · {copy.description}
          </p>
        </div>
        <StatusBar
          loaded={loadedSpecifications}
          total={total}
          loading={loading}
          canLoadMore={canLoadMore}
          atHardCap={atHardCap}
          onLoadMore={() => void loadBatch()}
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
                ? `${SPEECH_ACT_LABELS[selected.speechAct]} · ${selectedSemanticRelations} semantic relation(s) · ${selectedSelectionRelations} selection relation(s) · ${selected.evidenceCount} evidence captured`
                : `${selected.nodeKind[0].toUpperCase()}${selected.nodeKind.slice(1)} node · shared content-addressed projection`}
          </div>
          <div className="statement">{selected.statement}</div>
          <div className="id">{selected.id}</div>
        </div>
      )}

      {!loading &&
        nodes.length > 0 &&
        view !== "current" &&
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
