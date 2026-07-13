"use client";

import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import dynamic from "next/dynamic";
import Legend from "@/components/Legend";
import StatusBar from "@/components/StatusBar";
import {
  SPEECH_ACT_COLORS,
  SPEECH_ACT_LABELS,
  type GraphEdge,
  type GraphNode,
  type GraphPage,
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
    setEdges(Array.from(a.edges.values()));
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

  const present = useMemo(() => {
    const s = new Set<SpeechAct>();
    for (const n of nodes) {
      if (n.nodeKind === "specification") s.add(n.speechAct);
    }
    return s;
  }, [nodes]);
  const loadedSpecifications = useMemo(
    () => nodes.filter((node) => node.nodeKind === "specification").length,
    [nodes],
  );

  const atHardCap = nodes.length >= RENDER_CAP && !reachedEnd;
  const canLoadMore = !reachedEnd && !atHardCap;

  return (
    <main className="stage">
      {nodes.length > 0 && (
        <GraphView nodes={nodes} links={edges} onSelect={setSelected} />
      )}

      <div className="topbar">
        <div className="title panel">
          <h1>spec-oracle · graph view</h1>
          <p>Grounded specifications connected through written term forms.</p>
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

      <Legend
        present={present}
        termPresent={nodes.some((node) => node.nodeKind === "term")}
      />

      {selected && (
        <div className="detail panel">
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
                background: SPEECH_ACT_COLORS[selected.speechAct],
              }}
            />
            {selected.nodeKind === "term"
              ? "Written term form · lexical connector"
              : `${SPEECH_ACT_LABELS[selected.speechAct]} · ${selected.evidenceCount} evidence captured · ${selected.evidenceRequestCount} request(s)`}
          </div>
          <div className="statement">{selected.statement}</div>
          <div className="id">{selected.id}</div>
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
