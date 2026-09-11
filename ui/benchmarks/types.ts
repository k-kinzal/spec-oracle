import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";

export type Point2D = {x: number; y: number};

export type FixtureRole =
  | {kind: "context"; context: string; parent?: string}
  | {kind: "overlap"; contexts: [string, string]}
  | {kind: "bridge"; contexts: [string, string]}
  | {kind: "unlabeled"};

export type LayoutFixture = {
  id: string;
  seed: number;
  nodes: SpecificationLayoutInputNode[];
  edges: SpecificationLayoutInputEdge[];
  specificationIds: string[];
  roles: ReadonlyMap<string, FixtureRole>;
  contextIds: string[];
};

export type LayoutCandidate = {
  id: string;
  description: string;
  layout: (
    nodes: SpecificationLayoutInputNode[],
    edges: SpecificationLayoutInputEdge[],
  ) => SpecificationLayoutResult;
};

export type LayoutCoordinates = ReadonlyMap<string, Point2D>;

export function resultCoordinates(
  result: SpecificationLayoutResult,
): Map<string, Point2D> {
  return new Map(
    result.ids.map((id, index) => [
      id,
      {
        x: result.positions[index * 3],
        y: result.positions[index * 3 + 1],
      },
    ]),
  );
}

