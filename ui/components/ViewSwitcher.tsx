"use client";

import type { GraphViewMode } from "@/lib/types";

const OPTIONS: Array<{
  mode: GraphViewMode;
  label: string;
  countKind: "nodes" | "relations" | "none";
}> = [
  { mode: "all", label: "Graph", countKind: "nodes" },
  { mode: "semantic", label: "Meaning", countKind: "relations" },
  { mode: "vocabulary", label: "Vocabulary", countKind: "relations" },
  { mode: "refinement", label: "Refinement", countKind: "relations" },
  { mode: "conflicts", label: "Conflicts", countKind: "relations" },
  { mode: "isolated", label: "Isolated", countKind: "nodes" },
  { mode: "selection", label: "Selection", countKind: "relations" },
  { mode: "current", label: "Current set", countKind: "none" },
];

export default function ViewSwitcher({
  active,
  counts,
  onChange,
}: {
  active: GraphViewMode;
  counts: Record<GraphViewMode, number | null>;
  onChange: (mode: GraphViewMode) => void;
}) {
  return (
    <nav className="view-switcher panel" aria-label="Graph views">
      {OPTIONS.map(({ mode, label, countKind }) => {
        const count = counts[mode];
        return (
          <button
            key={mode}
            className={mode === active ? "view-tab active" : "view-tab"}
            type="button"
            aria-pressed={mode === active}
            onClick={() => onChange(mode)}
          >
            <span>{label}</span>
            {countKind !== "none" && count !== null && (
              <span className="view-count">{count.toLocaleString()}</span>
            )}
            {mode === "current" && <span className="view-pending">pending</span>}
          </button>
        );
      })}
    </nav>
  );
}
