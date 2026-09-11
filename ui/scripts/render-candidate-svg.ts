import {layoutCandidates} from "../benchmarks/candidates";
import {selectDefaultSpecificationGraph} from "../lib/specification-proximity";
import type {GraphEdge, GraphNode} from "../lib/types";

const endpoint =
  process.env.GRAPH_ENDPOINT ?? "http://127.0.0.1:3000/api/graph";

function argument(name: string) {
  const prefix = `--${name}=`;
  return process.argv.find((value) => value.startsWith(prefix))?.slice(prefix.length);
}

async function loadGraph() {
  const nodes = new Map<string, GraphNode>();
  const edges = new Map<string, GraphEdge>();
  let pageToken = "";
  do {
    const url = new URL(endpoint);
    url.searchParams.set("pageSize", "1000");
    if (pageToken) url.searchParams.set("pageToken", pageToken);
    const response = await fetch(url);
    if (!response.ok) throw new Error(`${response.status} ${await response.text()}`);
    const page = await response.json();
    for (const node of page.nodes as GraphNode[]) nodes.set(node.id, node);
    for (const edge of page.edges as GraphEdge[]) edges.set(edge.id, edge);
    pageToken = page.nextPageToken;
  } while (pageToken);
  return {nodes: [...nodes.values()], edges: [...edges.values()]};
}

async function main() {
  const candidateId = argument("candidate") ?? "failed-baseline";
  const candidate = layoutCandidates.get(candidateId);
  if (!candidate) throw new Error(`Unknown candidate ${candidateId}`);
  const loaded = await loadGraph();
  const graph = selectDefaultSpecificationGraph(loaded.nodes, loaded.edges);
  const inputNodes = graph.nodes.map((node) => ({
  id: node.id,
  nodeKind: node.nodeKind,
  statement: node.statement,
  radius: 4,
  visible: node.nodeKind === "specification",
}));
  const result = candidate.layout(inputNodes, graph.edges);
  const specificationIds = new Set(
  inputNodes
    .filter((node) => node.nodeKind === "specification")
    .map((node) => node.id),
);
  const points = result.ids.flatMap((id, index) =>
  specificationIds.has(id)
    ? [
        {
          x: result.positions[index * 3],
          y: result.positions[index * 3 + 1],
        },
      ]
    : [],
);
  const minimumX = Math.min(...points.map((point) => point.x));
  const maximumX = Math.max(...points.map((point) => point.x));
  const minimumY = Math.min(...points.map((point) => point.y));
  const maximumY = Math.max(...points.map((point) => point.y));
  const width = 1200;
  const height = 1200;
  const margin = 36;
  const scale = Math.min(
  (width - margin * 2) / Math.max(1e-9, maximumX - minimumX),
  (height - margin * 2) / Math.max(1e-9, maximumY - minimumY),
);
  const offsetX = (width - (maximumX - minimumX) * scale) / 2;
  const offsetY = (height - (maximumY - minimumY) * scale) / 2;
  const circles = points
  .map((point) => {
    const x = offsetX + (point.x - minimumX) * scale;
    const y = offsetY + (point.y - minimumY) * scale;
    return `<circle cx="${x.toFixed(2)}" cy="${y.toFixed(2)}" r="1.65"/>`;
  })
  .join("");
  process.stdout.write(
    `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">` +
      `<rect width="100%" height="100%" fill="#0c0d0f"/>` +
      `<g fill="#4da3ef" fill-opacity="0.82">${circles}</g>` +
      `</svg>`,
  );
}

void main();
