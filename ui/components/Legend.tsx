"use client";

import {
  DIRECTED_EDGE_KINDS,
  EDGE_FAMILY_LABELS,
  EDGE_KIND_COLORS,
  EDGE_KIND_FAMILIES,
  EDGE_KIND_LABELS,
  EDGE_KIND_ORDER,
  SPEECH_ACT_COLORS,
  SPEECH_ACT_LABELS,
  SPEECH_ACT_ORDER,
  TERM_NODE_COLOR,
  type EdgeKind,
  type SpeechAct,
} from "@/lib/types";

/** The speech-act color key. Only shows acts actually present on screen, so the
 *  legend describes the graph you are looking at rather than the whole schema. */
export default function Legend({
  present,
  termPresent,
  edgePresent,
  supportContextCount,
  contextualizedNodeCount,
  sharedFoundationCount,
}: {
  present: Set<SpeechAct>;
  termPresent: boolean;
  edgePresent: Set<EdgeKind>;
  supportContextCount: number;
  contextualizedNodeCount: number;
  sharedFoundationCount: number;
}) {
  const rows = SPEECH_ACT_ORDER.filter((a) => present.has(a));
  const edgeRows = EDGE_KIND_ORDER.filter((kind) => edgePresent.has(kind));
  if (
    rows.length === 0 &&
    !termPresent &&
    edgeRows.length === 0 &&
    supportContextCount === 0
  ) {
    return null;
  }
  return (
    <div className="legend panel">
      {supportContextCount > 0 && (
        <>
          <h2>Selection context</h2>
          <div className="row">
            <span className="context-boundary-swatch" />
            <span>
              {supportContextCount.toLocaleString()} support basins ·{" "}
              {contextualizedNodeCount.toLocaleString()} specifications
              {sharedFoundationCount > 0
                ? ` · ${sharedFoundationCount.toLocaleString()} shared`
                : ""}
            </span>
          </div>
        </>
      )}
      <h2>Speech act</h2>
      {rows.map((act) => (
        <div className="row" key={act}>
          <span className="dot" style={{ background: SPEECH_ACT_COLORS[act] }} />
          <span>{SPEECH_ACT_LABELS[act]}</span>
        </div>
      ))}
      {termPresent && (
        <div className="row">
          <span className="dot" style={{ background: TERM_NODE_COLOR }} />
          <span>Written term form</span>
        </div>
      )}
      {edgeRows.length > 0 && <h2>Edge</h2>}
      {edgeRows.map((kind) => (
        <div className="row" key={kind}>
          <span className="dot" style={{ background: EDGE_KIND_COLORS[kind] }} />
          <span>
            {DIRECTED_EDGE_KINDS.has(kind) ? "→ " : "— "}
            {EDGE_FAMILY_LABELS[EDGE_KIND_FAMILIES[kind]]} ·{" "}
            {EDGE_KIND_LABELS[kind]}
          </span>
        </div>
      ))}
    </div>
  );
}
