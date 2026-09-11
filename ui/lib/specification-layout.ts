import type {GraphEdge, GraphNode} from "@/lib/types";
import {layoutSpecificationEvidenceGraph} from "./specification-evidence-layout";

export type SpecificationLayoutInputNode = {
  id: string;
  nodeKind: GraphNode["nodeKind"];
  statement: string;
  radius: number;
  visible: boolean;
  /** Evaluation-only masks for view-derived features; production leaves empty. */
  excludedViewFeatureIds?: readonly string[];
};

export type SpecificationLayoutInputEdge = Pick<
  GraphEdge,
  "id" | "source" | "target" | "current" | "family"
>;

export type SpecificationLayoutResult = {
  ids: string[];
  positions: Float32Array;
  featureCount: number;
  routeCount: number;
  iterations: number;
};

/**
 * Synchronous execution of the same objective used by the stateful production
 * Worker. Tests and offline diagnostics use this form; the UI preserves the
 * objective's coordinates and continues it as graph evidence accumulates.
 */
export function layoutSpecificationGraph(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
): SpecificationLayoutResult {
  return layoutSpecificationEvidenceGraph(nodes, edges);
}
