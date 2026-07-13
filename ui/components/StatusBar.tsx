"use client";

/** The scale indicator: how many authored specifications are on screen,
 *  plus the control to pull the next bounded batch. Derived adjacent term
 *  nodes are deliberately outside this progress count. This is where the
 *  "never load everything" contract is made visible to the user. */
export default function StatusBar({
  loaded,
  total,
  loading,
  canLoadMore,
  atHardCap,
  onLoadMore,
}: {
  loaded: number;
  total: number;
  loading: boolean;
  canLoadMore: boolean;
  atHardCap: boolean;
  onLoadMore: () => void;
}) {
  const pct = total > 0 ? Math.min(100, (loaded / total) * 100) : 0;
  return (
    <div className="status panel">
      {loading && <span className="spinner" aria-label="loading" />}
      <span className="count">
        <strong>{loaded.toLocaleString()}</strong>{" "}
        <span className="muted">of {total.toLocaleString()} specifications</span>
      </span>
      <span className="bar" aria-hidden>
        <span style={{ width: `${pct}%` }} />
      </span>
      {atHardCap ? (
        <span className="muted">render cap reached</span>
      ) : (
        <button
          className="btn"
          onClick={onLoadMore}
          disabled={loading || !canLoadMore}
        >
          {canLoadMore ? "Load more" : "All loaded"}
        </button>
      )}
    </div>
  );
}
