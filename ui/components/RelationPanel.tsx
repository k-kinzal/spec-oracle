"use client";

import {
  CONFLICT_EDGE_KINDS,
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
    occurrence_reliance: "reliance evidence conditions reliant contract",
    guarantee_discharge: "guarantee discharges target contract assumption",
    admissibility_envelope: "permission bounds target contract environment",
    supports: "supporter supports supported",
    defeats: "defeater defeats defeated",
    supersedes: "superseder supersedes superseded",
    grounded_by: "grounded specification is grounded by evidence",
    has_assumption: "contract specification has assumption",
    has_guarantee: "contract specification has guarantee",
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
    case "fitness":
      return "Candidate fitness";
    case "contracts":
      return "Assume–guarantee pairings";
    case "ledger":
      return "Append-only Ledger";
    case "current":
      return "Current specification graph";
    case "all":
      return "Relations";
  }
}

export default function RelationPanel({
  mode,
  nodes,
  edges,
  population,
  populationComplete = false,
  onSelect,
}: {
  mode: GraphViewMode;
  nodes: GraphNode[];
  edges: GraphEdge[];
  population?: GraphNode[];
  populationComplete?: boolean;
  onSelect: (node: GraphNode) => void;
}) {
  if (mode === "all") return null;

  if (mode === "fitness") {
    const ranked = [...nodes].sort(
      (left, right) =>
        right.supportScore - left.supportScore || left.id.localeCompare(right.id),
    );
    return (
      <aside className="relation-panel panel" data-testid="relation-panel">
        <div className="relation-panel-heading">
          <span className="eyebrow">
            {ranked[0]?.policyVersion || "Selection policy unavailable"}
          </span>
          <h2>{panelTitle(mode)}</h2>
          <p>
            Admission creates candidates. Evidence and grounded Supports create fitness;
            competition and explicit decisions explain exclusions.
          </p>
        </div>
        <div className="isolated-list">
          {ranked.slice(0, DISPLAY_LIMIT).map((node) => (
            <button
              type="button"
              className="isolated-item"
              key={node.id}
              onClick={() => onSelect(node)}
            >
              <span>
                {node.current ? "◆" : "◇"} {node.statement}
              </span>
              <small>
                fitness {node.supportScore >= 0 ? "+" : ""}
                {node.supportScore} · Evidence {node.evidenceScore >= 0 ? "+" : ""}
                {node.evidenceScore} · relations {node.relationScore >= 0 ? "+" : ""}
                {node.relationScore}
                {node.exclusions.length > 0
                  ? ` · ${node.exclusions.map((reason) => reason.kind).join(", ")}`
                  : " · current"}
              </small>
            </button>
          ))}
        </div>
      </aside>
    );
  }

  if (mode === "isolated" || mode === "current") {
    const specifications = nodes.filter((node) => node.nodeKind === "specification");
    const candidates = (population ?? specifications).filter(
      (node) => node.nodeKind === "specification",
    );
    const ungrounded = candidates.filter((node) => node.evidenceScore === 0).length;
    const countered = candidates.filter((node) => node.evidenceScore < 0).length;
    const supportOnly = candidates.filter(
      (node) => node.current && node.evidenceScore <= 0 && node.relationScore > 0,
    ).length;
    const selectedConflicts = edges.filter((edge) =>
      CONFLICT_EDGE_KINDS.has(edge.kind),
    ).length;
    return (
      <aside className="relation-panel panel" data-testid="relation-panel">
        <div className="relation-panel-heading">
          <span className="eyebrow">
            {mode === "current" ? "Versioned fitness selection" : "Relation diagnostic"}
          </span>
          <h2>{panelTitle(mode)}</h2>
          <p>
            {mode === "current"
              ? "The selected specifications and every current relationship or projection that remains attached to them."
              : "Specifications with no current semantic Edge. Lexical term incidence is deliberately ignored."}
          </p>
          {mode === "current" && (
            <p>
              {populationComplete ? "Whole population" : "Loaded population"}: {specifications.length}
              /{candidates.length} selected · {ungrounded} without direct Evidence · {countered}
              with net Counter Evidence · {supportOnly} selected by transferred support only ·{" "}
              {selectedConflicts} selected conflict Edges. These observations identify where
              further accumulation or relation derivation can change the current graph.
            </p>
          )}
        </div>
        <div className="isolated-list">
          {specifications.slice(0, DISPLAY_LIMIT).map((node) => (
            <button
              type="button"
              className="isolated-item"
              key={node.id}
              onClick={() => onSelect(node)}
            >
              <span>{node.statement}</span>
              <small>
                {mode === "current" ? `fitness ${node.supportScore} · ` : ""}
                {node.id}
              </small>
            </button>
          ))}
        </div>
        {specifications.length > DISPLAY_LIMIT && (
          <div className="panel-footnote">
            Showing {DISPLAY_LIMIT.toLocaleString()} of {specifications.length.toLocaleString()} loaded specifications.
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
            : mode === "contracts"
              ? "Well-formed proved pairings"
              : mode === "ledger"
                ? "Immutable history and current selection"
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
            const relied = edge.reliedSpecId
              ? nodeById.get(edge.reliedSpecId)
              : undefined;
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
                    {edge.current ? "Current derivation" : "Ledger history"} ·{" "}
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
                {relied && (
                  <button
                    type="button"
                    className="isolated-item"
                    onClick={() => onSelect(relied)}
                  >
                    <small>Explicit relied specification · exact awaited assertion</small>
                    <span>{relied.statement}</span>
                  </button>
                )}
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
