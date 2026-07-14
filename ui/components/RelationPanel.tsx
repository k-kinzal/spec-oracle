"use client";

import {
  DIRECTED_EDGE_KINDS,
  EDGE_FAMILY_LABELS,
  EDGE_KIND_COLORS,
  EDGE_KIND_DESCRIPTIONS,
  EDGE_KIND_LABELS,
  ENDPOINT_ROLE_LABELS,
  type GraphEdge,
  type GraphNode,
  type GraphViewMode,
} from "@/lib/types";

const DISPLAY_LIMIT = 80;

function endpointRoles(edge: GraphEdge): {
  source: string;
  target: string;
  reading: string;
} {
  const readings: Record<GraphEdge["kind"], string> = {
    mentions_term: "mentioner mentions mentioned term",
    refines: "refiner refines refined",
    equivalent: "equivalent peers",
    hard_contradiction: "conflicting peers",
    advisory_tension: "conflicting peers",
    descriptive_conflict: "conflicting peers",
    envelope_conflict: "conflicting peers",
    supports: "supporter supports supported",
    defeats: "defeater defeats defeated",
    supersedes: "superseder supersedes superseded",
    unspecified: "unspecified relationship",
  };
  return {
    source: `${ENDPOINT_ROLE_LABELS[edge.sourceRole]} · argument 1`,
    target: `${ENDPOINT_ROLE_LABELS[edge.targetRole]} · argument 2`,
    reading: readings[edge.kind],
  };
}

function panelTitle(mode: GraphViewMode): string {
  switch (mode) {
    case "semantic":
      return "Proved meaning relations";
    case "vocabulary":
      return "Lexical incidence";
    case "refinement":
      return "Refinement pairs";
    case "conflicts":
      return "Conflict pairs";
    case "isolated":
      return "Semantically isolated";
    case "selection":
      return "Selection relations";
    case "current":
      return "Current specification set";
    case "all":
      return "Relations";
  }
}

export default function RelationPanel({
  mode,
  nodes,
  edges,
  onSelect,
}: {
  mode: GraphViewMode;
  nodes: GraphNode[];
  edges: GraphEdge[];
  onSelect: (node: GraphNode) => void;
}) {
  if (mode === "all") return null;

  if (mode === "current") {
    return (
      <aside className="relation-panel panel" data-testid="relation-panel">
        <div className="relation-panel-heading">
          <span className="eyebrow">Selection view</span>
          <h2>{panelTitle(mode)}</h2>
        </div>
        <div className="not-derived">
          <span className="not-derived-mark">∅</span>
          <h3>Not derivable yet</h3>
          <p>
            No selection policy exists. Semantic relations and versioned
            selection relations are now separate families, but no rule yet
            resolves them into one current specification set.
          </p>
          <p>
            This view becomes valid only when a versioned policy defines
            equivalence deduplication, conflict resolution, refinement choice,
            and the effect of Supports, Defeats, and Supersedes.
          </p>
        </div>
      </aside>
    );
  }

  if (mode === "isolated") {
    return (
      <aside className="relation-panel panel" data-testid="relation-panel">
        <div className="relation-panel-heading">
          <span className="eyebrow">Coverage diagnostic</span>
          <h2>{panelTitle(mode)}</h2>
          <p>
            Specifications with no current semantic Edge. Lexical term incidence
            is deliberately ignored.
          </p>
        </div>
        <div className="isolated-list">
          {nodes.slice(0, DISPLAY_LIMIT).map((node) => (
            <button
              type="button"
              className="isolated-item"
              key={node.id}
              onClick={() => onSelect(node)}
            >
              <span>{node.statement}</span>
              <small>{node.id}</small>
            </button>
          ))}
        </div>
        {nodes.length > DISPLAY_LIMIT && (
          <div className="panel-footnote">
            Showing {DISPLAY_LIMIT.toLocaleString()} of {nodes.length.toLocaleString()} loaded nodes.
          </div>
        )}
      </aside>
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const visible = edges.slice(0, DISPLAY_LIMIT);

  return (
    <aside className="relation-panel panel" data-testid="relation-panel">
      <div className="relation-panel-heading">
        <span className="eyebrow">
          {mode === "selection"
            ? "Versioned selection family"
            : "Current derivation versions"}
        </span>
        <h2>{panelTitle(mode)}</h2>
        <p>
          {edges.length.toLocaleString()} relation{edges.length === 1 ? "" : "s"} in the loaded graph.
        </p>
      </div>
      {visible.length === 0 ? (
        <div className="relation-empty">
          {mode === "selection"
            ? "No current selection relation has been recorded."
            : "No matching relation has been proved."}
        </div>
      ) : (
        <div className="relation-list">
          {visible.map((edge) => {
            const source = nodeById.get(edge.source);
            const target = nodeById.get(edge.target);
            if (!source || !target) return null;
            const roles = endpointRoles(edge);
            const directed = DIRECTED_EDGE_KINDS.has(edge.kind);
            return (
              <article
                className="relation-card"
                key={edge.id}
                style={{ borderTopColor: EDGE_KIND_COLORS[edge.kind] }}
              >
                <div className="relation-kind">
                  <span
                    className="relation-swatch"
                    style={{ background: EDGE_KIND_COLORS[edge.kind] }}
                  />
                  <strong>{EDGE_KIND_LABELS[edge.kind]}</strong>
                  <span>
                    {EDGE_FAMILY_LABELS[edge.family]} ·{" "}
                    {directed ? "directed" : "symmetric"}
                  </span>
                </div>
                <p className="relation-description">
                  {EDGE_KIND_DESCRIPTIONS[edge.kind]}
                </p>
                <div className="relation-derivation">
                  {edge.derivationMethod || "unknown method"} ·{" "}
                  {edge.derivationVersion || "unknown version"}
                </div>
                <div className="relation-endpoints">
                  <button type="button" onClick={() => onSelect(source)}>
                    <small>{roles.source}</small>
                    <span>{source.statement}</span>
                  </button>
                  <div className={directed ? "relation-arrow" : "relation-line"}>
                    <span>{directed ? "→" : "—"}</span>
                    <small>{roles.reading}</small>
                  </div>
                  <button type="button" onClick={() => onSelect(target)}>
                    <small>{roles.target}</small>
                    <span>{target.statement}</span>
                  </button>
                </div>
              </article>
            );
          })}
        </div>
      )}
      {edges.length > DISPLAY_LIMIT && (
        <div className="panel-footnote">
          Showing {DISPLAY_LIMIT.toLocaleString()} of {edges.length.toLocaleString()} loaded relations.
        </div>
      )}
    </aside>
  );
}
