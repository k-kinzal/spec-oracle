import {
  forceCenter,
  forceCollide,
  forceLink,
  forceManyBody,
  forceSimulation,
  forceX,
  forceY,
  forceZ,
  type SimulationLinkDatum,
  type SimulationNodeDatum,
} from "d3-force-3d";
import type { GraphEdge, GraphNode } from "@/lib/types";

type LayoutNode = SimulationNodeDatum & {
  id: string;
  x: number;
  y: number;
  z: number;
  radius: number;
  kind: GraphNode["nodeKind"];
};

type LayoutEdge = SimulationLinkDatum<LayoutNode> & {
  id: string;
  source: string | LayoutNode;
  target: string | LayoutNode;
  kind: GraphEdge["kind"];
};

type WorkerInput =
  | { type: "reset"; generation: number }
  | {
      type: "append";
      generation: number;
      nodes: LayoutNode[];
      edges: Array<{
        id: string;
        source: string;
        target: string;
        kind: GraphEdge["kind"];
      }>;
    };

const nodes: LayoutNode[] = [];
const nodeIds = new Set<string>();
const edges = new Map<string, LayoutEdge>();
let generation = 0;
let sequence = 0;
let lastPublished = 0;

const linkForce = forceLink<LayoutNode, LayoutEdge>([])
  .id((node) => node.id)
  .distance((edge) => (edge.kind === "mentions_term" ? 23 : 54))
  .strength((edge) => (edge.kind === "mentions_term" ? 0.2 : 0.38));

const simulation = forceSimulation<LayoutNode>(nodes, 3)
  .stop()
  .alphaMin(0.0025)
  .alphaDecay(0.032)
  .velocityDecay(0.42)
  .force("links", linkForce)
  .force(
    "charge",
    forceManyBody<LayoutNode>()
      .strength((node) => (node.kind === "term" ? -18 : -42))
      .theta(0.92)
      .distanceMin(3)
      .distanceMax(440),
  )
  .force(
    "collision",
    forceCollide<LayoutNode>()
      .radius((node) => node.radius * 1.28 + 1.4)
      .strength(0.55),
  )
  .force("center", forceCenter<LayoutNode>(0, 0, 0).strength(0.055))
  .force("x", forceX<LayoutNode>(0).strength(0.0025))
  .force("y", forceY<LayoutNode>(0).strength(0.0025))
  .force("z", forceZ<LayoutNode>(0).strength(0.0025));

simulation.on("tick", () => {
  const now = performance.now();
  if (now - lastPublished < 30) return;
  lastPublished = now;
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const node = nodes[index];
    positions[index * 3] = node.x;
    positions[index * 3 + 1] = node.y;
    positions[index * 3 + 2] = node.z;
  }
  self.postMessage(
    { type: "positions", generation, sequence: sequence++, positions },
    { transfer: [positions.buffer] },
  );
});

simulation.on("end", () => {
  self.postMessage({ type: "settled", generation });
});

self.addEventListener("message", (event: MessageEvent<WorkerInput>) => {
  const message = event.data;
  if (message.type === "reset") {
    generation = message.generation;
    sequence = 0;
    lastPublished = 0;
    simulation.stop();
    nodes.length = 0;
    nodeIds.clear();
    edges.clear();
    simulation.nodes(nodes);
    linkForce.links([]);
    return;
  }
  if (message.generation !== generation) return;

  for (const node of message.nodes) {
    if (nodeIds.has(node.id)) continue;
    nodeIds.add(node.id);
    nodes.push(node);
  }
  for (const edge of message.edges) {
    if (
      edges.has(edge.id) ||
      !nodeIds.has(edge.source) ||
      !nodeIds.has(edge.target)
    ) {
      continue;
    }
    edges.set(edge.id, edge);
  }
  simulation.nodes(nodes);
  linkForce.links([...edges.values()]);
  simulation.alpha(Math.max(simulation.alpha(), 0.16)).restart();
});

export {};
