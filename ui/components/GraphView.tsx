"use client";

// The WebGL graph canvas. Cosmograph runs the force layout on the GPU and
// renders with WebGL, so it is browser-only — this module is imported with
// `ssr: false` and never runs on the server.

import { useCallback } from "react";
import { Cosmograph, CosmographProvider } from "@cosmograph/react";
import {
  SPEECH_ACT_COLORS,
  TERM_NODE_COLOR,
  type GraphEdge,
  type GraphNode,
} from "@/lib/types";

export default function GraphView({
  nodes,
  links,
  onSelect,
}: {
  nodes: GraphNode[];
  links: GraphEdge[];
  onSelect: (node: GraphNode | null) => void;
}) {
  // Color a node by its speech act — the dimension that clusters the graph.
  const nodeColor = useCallback(
    (n: GraphNode) =>
      n.nodeKind === "term"
        ? TERM_NODE_COLOR
        : SPEECH_ACT_COLORS[n.speechAct] ?? SPEECH_ACT_COLORS.unknown,
    [],
  );

  // Size by evidence: better-grounded claims read as heavier nodes. Bounded so a
  // single very-cited node cannot dominate the view.
  const nodeSize = useCallback(
    (n: GraphNode) =>
      n.nodeKind === "term" ? 2.1 : 2.5 + Math.min(n.evidenceCount, 8) * 0.9,
    [],
  );

  const nodeLabel = useCallback((n: GraphNode) => n.statement, []);

  const handleClick = useCallback(
    (node?: GraphNode) => onSelect(node ?? null),
    [onSelect],
  );

  return (
    <div className="graph-fill">
      {/* The provider establishes the Cosmograph context the component's
          internal hooks read from (rendering standalone otherwise warns). */}
      <CosmographProvider<GraphNode, GraphEdge> nodes={nodes} links={links}>
        <Cosmograph<GraphNode, GraphEdge>
          nodeColor={nodeColor}
          nodeSize={nodeSize}
          nodeLabelAccessor={nodeLabel}
          linkColor={() => "rgba(150, 150, 160, 0.22)"}
          linkWidth={0.4}
          linkArrows={false}
          backgroundColor="#0f0f10"
          nodeGreyoutOpacity={0.08}
          hoveredNodeRingColor="#ffffff"
          focusedNodeRingColor="#ffffff"
          // A calm, spread-out force layout close to the reference look.
          simulationFriction={0.86}
          simulationLinkSpring={0.4}
          simulationLinkDistance={4}
          simulationRepulsion={0.9}
          simulationGravity={0.18}
          simulationDecay={2000}
          fitViewOnInit
          onClick={handleClick}
        />
      </CosmographProvider>
    </div>
  );
}
