"use client";

/** The scale indicator: how many authored specifications have been acquired while
 *  bounded batches load automatically. Derived adjacent term nodes are
 *  deliberately outside this progress count. */
export default function StatusBar({
  loaded,
  total,
  loading,
  complete,
  atHardCap,
  drawing,
  unit = "specifications",
}: {
  loaded: number;
  total: number;
  loading: boolean;
  complete: boolean;
  atHardCap: boolean;
  drawing: boolean;
  unit?: string;
}) {
  const pct = total > 0 ? Math.min(100, (loaded / total) * 100) : 0;
  return (
    <div className="status panel">
      {(loading || drawing) && <span className="spinner" aria-label="loading" />}
      <span className="count">
        <strong>{loaded.toLocaleString()}</strong>{" "}
        <span className="muted">of {total.toLocaleString()} {unit}</span>
      </span>
      <span className="bar" aria-hidden>
        <span style={{ width: `${pct}%` }} />
      </span>
      {atHardCap ? (
        <span className="muted">render cap reached</span>
      ) : complete && drawing ? (
        <span className="muted">Growing 3D graph · 24 fps target</span>
      ) : complete ? (
        <span className="muted">All loaded</span>
      ) : (
        <span className="muted">Loading remaining pages</span>
      )}
    </div>
  );
}
