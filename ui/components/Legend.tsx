"use client";

import {
  SPEECH_ACT_COLORS,
  SPEECH_ACT_LABELS,
  SPEECH_ACT_ORDER,
  TERM_NODE_COLOR,
  type SpeechAct,
} from "@/lib/types";

/** The speech-act color key. Only shows acts actually present on screen, so the
 *  legend describes the graph you are looking at rather than the whole schema. */
export default function Legend({
  present,
  termPresent,
}: {
  present: Set<SpeechAct>;
  termPresent: boolean;
}) {
  const rows = SPEECH_ACT_ORDER.filter((a) => present.has(a));
  if (rows.length === 0 && !termPresent) return null;
  return (
    <div className="legend panel">
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
    </div>
  );
}
