"use client";

import { useEffect, useRef } from "react";
import {
  Box3,
  BufferAttribute,
  BufferGeometry,
  Color,
  DynamicDrawUsage,
  GridHelper,
  IcosahedronGeometry,
  InstancedBufferAttribute,
  InstancedMesh,
  LineBasicMaterial,
  LineSegments,
  Matrix4,
  MeshBasicMaterial,
  PerspectiveCamera,
  Raycaster,
  Scene,
  Vector2,
  Vector3,
  WebGLRenderer,
} from "three";
import { OrbitControls } from "three/examples/jsm/controls/OrbitControls.js";
import {
  DIRECTED_EDGE_KINDS,
  DERIVED_NODE_COLORS,
  EDGE_KIND_COLORS,
  SPEECH_ACT_COLORS,
  TERM_NODE_COLOR,
  type GraphEdge,
  type GraphNode,
} from "@/lib/types";

const DRAW_FPS = 24;
const DRAW_INTERVAL = 1000 / DRAW_FPS;
const NODES_PER_DRAW = 2;
const EDGES_PER_DRAW = 4;
const GROWTH_FRAMES = 5;
const NODE_CAPACITY = 4096;
const EDGE_CAPACITY = 8192;
const CAMERA_HOLD_MS = 5000;

type LayoutNode = {
  id: string;
  x: number;
  y: number;
  z: number;
  radius: number;
  kind: GraphNode["nodeKind"];
};

type LayoutEdge = {
  id: string;
  source: string;
  target: string;
  kind: GraphEdge["kind"];
};

type LayoutMessage =
  | {
      type: "positions";
      generation: number;
      sequence: number;
      positions: Float32Array;
    }
  | { type: "settled"; generation: number };

const CLUSTER_CENTERS: Record<string, [number, number, number]> = {
  definition: [-92, -54, -48],
  description: [0, -82, 12],
  obligation: [92, -54, 48],
  prohibition: [-92, 48, 42],
  recommendation: [0, 82, -44],
  permission: [92, 48, -20],
  unknown: [0, 0, 0],
  term: [0, 0, 0],
  evidence: [-38, 0, 48],
  assumption: [0, -34, -44],
  guarantee: [38, 0, 42],
};

function stableHash(value: string): number {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function initialPosition(node: GraphNode): [number, number, number] {
  const key = node.nodeKind === "specification" ? node.speechAct : node.nodeKind;
  const center = CLUSTER_CENTERS[key] ?? CLUSTER_CENTERS.unknown;
  const hash = stableHash(node.id);
  const theta = ((hash % 4096) / 4096) * Math.PI * 2;
  const phi = Math.acos(2 * (((hash >>> 12) % 2048) / 2048) - 1);
  const radius = 9 + Math.sqrt(((hash >>> 20) % 4096) / 4096) * 31;
  return [
    center[0] + Math.sin(phi) * Math.cos(theta) * radius,
    center[1] + Math.sin(phi) * Math.sin(theta) * radius,
    center[2] + Math.cos(phi) * radius,
  ];
}

function positionNear(
  node: GraphNode,
  anchor: [number, number, number],
): [number, number, number] {
  const hash = stableHash(node.id);
  const theta = ((hash % 4096) / 4096) * Math.PI * 2;
  const z = (((hash >>> 12) % 2048) / 1024) - 1;
  const radial = Math.sqrt(Math.max(0, 1 - z * z));
  const distance = 8 + ((hash >>> 22) % 900) / 100;
  return [
    anchor[0] + Math.cos(theta) * radial * distance,
    anchor[1] + Math.sin(theta) * radial * distance,
    anchor[2] + z * distance,
  ];
}

function nodeColor(node: GraphNode): Color {
  if (node.nodeKind === "term") return new Color(TERM_NODE_COLOR);
  if (node.nodeKind !== "specification") {
    return new Color(DERIVED_NODE_COLORS[node.nodeKind]);
  }
  return new Color(SPEECH_ACT_COLORS[node.speechAct] ?? SPEECH_ACT_COLORS.unknown);
}

function baseNodeSize(node: GraphNode): number {
  return node.nodeKind === "specification"
    ? 4 + Math.min(Math.max(node.supportScore, 0), 24) * 0.24
    : 3;
}

function edgeColor(edge: GraphEdge): Color {
  const css = EDGE_KIND_COLORS[edge.kind];
  const rgba = css.match(
    /rgba?\((\d+),\s*(\d+),\s*(\d+)(?:,\s*([\d.]+))?/,
  );
  const color = rgba
    ? new Color(
        Number(rgba[1]) / 255,
        Number(rgba[2]) / 255,
        Number(rgba[3]) / 255,
      )
    : new Color(css);
  const authoredOpacity = rgba?.[4] ? Number(rgba[4]) : 1;
  return color.multiplyScalar(
    authoredOpacity * (edge.current ? 0.95 : 0.38),
  );
}

function easeOutCubic(progress: number): number {
  return 1 - Math.pow(1 - progress, 3);
}

function queueTopology(
  nodes: GraphNode[],
  links: GraphEdge[],
  queued: Set<string>,
  pending: string[],
) {
  const targetIds = new Set(nodes.map((node) => node.id));
  const adjacent = new Map<string, string[]>();
  for (const link of links) {
    if (!targetIds.has(link.source) || !targetIds.has(link.target)) continue;
    const source = adjacent.get(link.source) ?? [];
    source.push(link.target);
    adjacent.set(link.source, source);
    const target = adjacent.get(link.target) ?? [];
    target.push(link.source);
    adjacent.set(link.target, target);
  }

  const unseen = new Set(
    nodes.map((node) => node.id).filter((id) => !queued.has(id)),
  );
  const enqueueComponent = (seed: string) => {
    const breadthFirst = [seed];
    unseen.delete(seed);
    while (breadthFirst.length > 0) {
      const id = breadthFirst.shift();
      if (!id || queued.has(id)) continue;
      queued.add(id);
      pending.push(id);
      for (const neighbor of adjacent.get(id) ?? []) {
        if (!unseen.delete(neighbor)) continue;
        breadthFirst.push(neighbor);
      }
    }
  };

  for (const anchor of queued) {
    for (const neighbor of adjacent.get(anchor) ?? []) {
      if (unseen.has(neighbor)) enqueueComponent(neighbor);
    }
  }
  const seeds = [...unseen].sort(
    (left, right) =>
      (adjacent.get(right)?.length ?? 0) - (adjacent.get(left)?.length ?? 0) ||
      left.localeCompare(right),
  );
  for (const seed of seeds) {
    if (unseen.has(seed)) enqueueComponent(seed);
  }
}

export default function GraphView({
  nodes,
  links,
  onSelect,
  onDrawProgress,
  withInspector,
}: {
  nodes: GraphNode[];
  links: GraphEdge[];
  onSelect: (node: GraphNode | null) => void;
  onDrawProgress: (
    nodes: number,
    edges: number,
    actualFps: number,
    renderMs: number,
  ) => void;
  withInspector: boolean;
}) {
  const container = useRef<HTMLDivElement>(null);
  const tooltip = useRef<HTMLDivElement>(null);
  const onSelectRef = useRef(onSelect);
  const onProgressRef = useRef(onDrawProgress);
  const targetNodes = useRef(new Map<string, GraphNode>());
  const targetEdges = useRef(new Map<string, GraphEdge>());
  const incidentEdges = useRef(new Map<string, string[]>());
  const queuedNodes = useRef(new Set<string>());
  const queuedEdges = useRef(new Set<string>());
  const pendingNodes = useRef<string[]>([]);
  const waitingEdges = useRef(new Set<string>());
  const readyEdges = useRef<string[]>([]);
  const readyEdgeIds = useRef(new Set<string>());
  const visibleNodes = useRef<GraphNode[]>([]);
  const visibleEdges = useRef<GraphEdge[]>([]);
  const visibleEdgeIds = useRef(new Set<string>());
  const nodeIndices = useRef(new Map<string, number>());
  const nodeProgress = useRef(new Float32Array(NODE_CAPACITY));
  const edgeProgress = useRef(new Float32Array(EDGE_CAPACITY));
  const currentPositions = useRef(new Float32Array(NODE_CAPACITY * 3));
  const targetPositions = useRef(new Float32Array(NODE_CAPACITY * 3));
  const latestLayout = useRef<LayoutMessage | null>(null);
  const appliedLayoutSequence = useRef(-1);
  const layoutGeneration = useRef(0);
  const layoutActive = useRef(false);
  const workerRef = useRef<Worker | null>(null);
  const resetRequested = useRef(false);
  const userControlledUntil = useRef(0);

  onSelectRef.current = onSelect;
  onProgressRef.current = onDrawProgress;

  useEffect(() => {
    const host = container.current;
    if (!host) return;

    const scene = new Scene();
    scene.background = new Color(0x0f0f10);

    const camera = new PerspectiveCamera(47, 1, 0.1, 10000);
    camera.position.set(180, 110, 340);

    const renderer = new WebGLRenderer({
      antialias: true,
      alpha: false,
      powerPreference: "high-performance",
    });
    renderer.setPixelRatio(1);
    renderer.setSize(host.clientWidth, host.clientHeight, false);
    renderer.domElement.className = "graph-canvas";
    host.appendChild(renderer.domElement);

    const controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.1;
    controls.rotateSpeed = 0.55;
    controls.zoomSpeed = 0.8;
    controls.panSpeed = 0.7;
    controls.target.set(0, 0, 0);

    const grid = new GridHelper(520, 26, 0x27313d, 0x181c22);
    const gridMaterial = grid.material;
    gridMaterial.transparent = true;
    gridMaterial.opacity = 0.34;
    grid.position.y = -92;
    scene.add(grid);

    const nodeGeometry = new IcosahedronGeometry(1, 1);
    // InstancedMesh enables its instance-color shader path from the
    // instanceColor attribute itself. Enabling material vertexColors here
    // would also request a per-vertex geometry color, which this shared
    // geometry deliberately does not carry and would multiply every instance
    // down to black.
    const nodeMaterial = new MeshBasicMaterial({ toneMapped: false });
    const nodeMesh = new InstancedMesh(
      nodeGeometry,
      nodeMaterial,
      NODE_CAPACITY,
    );
    nodeMesh.count = 0;
    nodeMesh.instanceMatrix.setUsage(DynamicDrawUsage);
    nodeMesh.instanceColor = new InstancedBufferAttribute(
      new Float32Array(NODE_CAPACITY * 3),
      3,
    );
    nodeMesh.instanceColor.setUsage(DynamicDrawUsage);
    nodeMesh.frustumCulled = false;
    scene.add(nodeMesh);

    const edgePositions = new Float32Array(EDGE_CAPACITY * 6);
    const edgeColors = new Float32Array(EDGE_CAPACITY * 6);
    const edgeBaseColors = new Float32Array(EDGE_CAPACITY * 6);
    const edgeGeometry = new BufferGeometry();
    const edgePositionAttribute = new BufferAttribute(edgePositions, 3);
    const edgeColorAttribute = new BufferAttribute(edgeColors, 3);
    edgePositionAttribute.setUsage(DynamicDrawUsage);
    edgeColorAttribute.setUsage(DynamicDrawUsage);
    edgeGeometry.setAttribute("position", edgePositionAttribute);
    edgeGeometry.setAttribute("color", edgeColorAttribute);
    edgeGeometry.setDrawRange(0, 0);
    const edgeMaterial = new LineBasicMaterial({
      vertexColors: true,
      transparent: true,
      opacity: 0.78,
      depthWrite: false,
    });
    const edgeLines = new LineSegments(edgeGeometry, edgeMaterial);
    edgeLines.frustumCulled = false;
    scene.add(edgeLines);

    const worker = new Worker(
      new URL("../workers/graph-layout.worker.ts", import.meta.url),
      { type: "module", name: "spec-oracle-3d-layout" },
    );
    workerRef.current = worker;
    worker.postMessage({ type: "reset", generation: layoutGeneration.current });
    worker.onmessage = (event: MessageEvent<LayoutMessage>) => {
      const message = event.data;
      if (message.generation !== layoutGeneration.current) return;
      if (message.type === "positions") latestLayout.current = message;
      if (message.type === "settled") layoutActive.current = false;
    };

    const dummyMatrix = new Matrix4();
    const dummyPosition = new Vector3();
    const dummyScale = new Vector3();
    const bounds = new Box3();
    const boundsCenter = new Vector3();
    const boundsSize = new Vector3();
    const cameraDirection = new Vector3();
    const yAxis = new Vector3(0, 1, 0);
    const raycaster = new Raycaster();
    const pointer = new Vector2();
    let animationFrame = 0;
    let lastTick = performance.now();
    let lastReport = lastTick;
    let lastRender = 0;
    let renderRequested = true;
    let nodeColorsDirty = false;
    let motionTicksRemaining = 0;
    let hoverCheckAt = 0;
    const frameIntervals: number[] = [];
    const renderDurations: number[] = [];

    const holdCamera = () => {
      userControlledUntil.current = performance.now() + CAMERA_HOLD_MS;
      renderRequested = true;
    };
    controls.addEventListener("start", holdCamera);
    controls.addEventListener("change", () => {
      renderRequested = true;
    });

    const resize = () => {
      const width = Math.max(1, host.clientWidth);
      const height = Math.max(1, host.clientHeight);
      camera.aspect = width / height;
      camera.updateProjectionMatrix();
      renderer.setSize(width, height, false);
      renderRequested = true;
    };
    const resizeObserver = new ResizeObserver(resize);
    resizeObserver.observe(host);

    const reset = () => {
      visibleNodes.current = [];
      visibleEdges.current = [];
      visibleEdgeIds.current.clear();
      nodeIndices.current.clear();
      nodeProgress.current.fill(0);
      edgeProgress.current.fill(0);
      currentPositions.current.fill(0);
      targetPositions.current.fill(0);
      nodeMesh.count = 0;
      nodeColorsDirty = false;
      motionTicksRemaining = 0;
      edgeGeometry.setDrawRange(0, 0);
      layoutGeneration.current += 1;
      latestLayout.current = null;
      appliedLayoutSequence.current = -1;
      layoutActive.current = false;
      worker.postMessage({
        type: "reset",
        generation: layoutGeneration.current,
      });
      controls.target.set(0, 0, 0);
      camera.position.set(180, 110, 340);
      renderRequested = true;
    };

    const makeEdgeReady = (edgeId: string) => {
      if (!waitingEdges.current.has(edgeId)) return;
      const edge = targetEdges.current.get(edgeId);
      if (!edge) return;
      if (
        !nodeIndices.current.has(edge.source) ||
        !nodeIndices.current.has(edge.target)
      ) {
        return;
      }
      waitingEdges.current.delete(edgeId);
      if (readyEdgeIds.current.has(edgeId)) return;
      readyEdgeIds.current.add(edgeId);
      readyEdges.current.push(edgeId);
    };

    const appendGrowth = () => {
      const layoutNodes: LayoutNode[] = [];
      const layoutEdges: LayoutEdge[] = [];

      for (
        let count = 0;
        count < NODES_PER_DRAW && pendingNodes.current.length > 0;
        count += 1
      ) {
        const id = pendingNodes.current.shift();
        const node = id ? targetNodes.current.get(id) : undefined;
        if (!id || !node || nodeIndices.current.has(id)) continue;
        if (visibleNodes.current.length >= NODE_CAPACITY) break;

        const index = visibleNodes.current.length;
        let position = initialPosition(node);
        for (const edgeId of incidentEdges.current.get(id) ?? []) {
          const edge = targetEdges.current.get(edgeId);
          if (!edge) continue;
          const neighborId = edge.source === id ? edge.target : edge.source;
          const neighborIndex = nodeIndices.current.get(neighborId);
          if (neighborIndex === undefined) continue;
          position = positionNear(node, [
            currentPositions.current[neighborIndex * 3],
            currentPositions.current[neighborIndex * 3 + 1],
            currentPositions.current[neighborIndex * 3 + 2],
          ]);
          break;
        }

        visibleNodes.current.push(node);
        nodeIndices.current.set(id, index);
        nodeProgress.current[index] = 1 / GROWTH_FRAMES;
        currentPositions.current.set(position, index * 3);
        targetPositions.current.set(position, index * 3);
        nodeMesh.setColorAt(index, nodeColor(node));
        nodeColorsDirty = true;
        layoutNodes.push({
          id,
          x: position[0],
          y: position[1],
          z: position[2],
          radius: baseNodeSize(node),
          kind: node.nodeKind,
        });

        for (const edgeId of incidentEdges.current.get(id) ?? []) {
          makeEdgeReady(edgeId);
        }
      }

      for (
        let count = 0;
        count < EDGES_PER_DRAW && readyEdges.current.length > 0;
        count += 1
      ) {
        const id = readyEdges.current.shift();
        if (id) readyEdgeIds.current.delete(id);
        const edge = id ? targetEdges.current.get(id) : undefined;
        if (!id || !edge) continue;
        if (visibleEdgeIds.current.has(id)) continue;
        if (visibleEdges.current.length >= EDGE_CAPACITY) break;
        if (
          !nodeIndices.current.has(edge.source) ||
          !nodeIndices.current.has(edge.target)
        ) {
          waitingEdges.current.add(id);
          continue;
        }
        const index = visibleEdges.current.length;
        visibleEdges.current.push(edge);
        visibleEdgeIds.current.add(id);
        edgeProgress.current[index] = 1 / GROWTH_FRAMES;
        const color = edgeColor(edge);
        const directed = DIRECTED_EDGE_KINDS.has(edge.kind);
        const sourceColor = directed ? color.clone().multiplyScalar(0.34) : color;
        edgeBaseColors.set(sourceColor.toArray(), index * 6);
        edgeBaseColors.set(color.toArray(), index * 6 + 3);
        layoutEdges.push({
          id,
          source: edge.source,
          target: edge.target,
          kind: edge.kind,
        });
      }

      if (layoutNodes.length > 0 || layoutEdges.length > 0) {
        layoutActive.current = true;
        worker.postMessage({
          type: "append",
          generation: layoutGeneration.current,
          nodes: layoutNodes,
          edges: layoutEdges,
        });
      }
      return layoutNodes.length > 0 || layoutEdges.length > 0;
    };

    const applyLayout = () => {
      const message = latestLayout.current;
      if (
        !message ||
        message.type !== "positions" ||
        message.sequence === appliedLayoutSequence.current
      ) {
        return false;
      }
      appliedLayoutSequence.current = message.sequence;
      const coordinateCount = Math.min(
        message.positions.length,
        visibleNodes.current.length * 3,
      );
      targetPositions.current.set(
        message.positions.subarray(0, coordinateCount),
        0,
      );
      return true;
    };

    const updateBuffers = () => {
      const nodeCount = visibleNodes.current.length;
      bounds.makeEmpty();
      let growing = false;
      for (let index = 0; index < nodeCount; index += 1) {
        const offset = index * 3;
        for (let axis = 0; axis < 3; axis += 1) {
          const current = currentPositions.current[offset + axis];
          const target = targetPositions.current[offset + axis];
          currentPositions.current[offset + axis] =
            current + (target - current) * 0.38;
        }
        if (nodeProgress.current[index] < 1) {
          nodeProgress.current[index] = Math.min(
            1,
            nodeProgress.current[index] + 1 / GROWTH_FRAMES,
          );
          growing = true;
        }
        const node = visibleNodes.current[index];
        const scale =
          baseNodeSize(node) * easeOutCubic(nodeProgress.current[index]);
        dummyPosition.fromArray(currentPositions.current, offset);
        dummyScale.setScalar(scale);
        dummyMatrix.makeScale(dummyScale.x, dummyScale.y, dummyScale.z);
        dummyMatrix.setPosition(dummyPosition);
        nodeMesh.setMatrixAt(index, dummyMatrix);
        bounds.expandByPoint(dummyPosition);
      }
      nodeMesh.count = nodeCount;
      if (nodeCount > 0) {
        nodeMesh.instanceMatrix.needsUpdate = true;
        if (nodeColorsDirty && nodeMesh.instanceColor) {
          nodeMesh.instanceColor.needsUpdate = true;
          nodeColorsDirty = false;
        }
      }

      const edgeCount = visibleEdges.current.length;
      let edgeColorsDirty = false;
      for (let index = 0; index < edgeCount; index += 1) {
        if (edgeProgress.current[index] < 1) {
          edgeProgress.current[index] = Math.min(
            1,
            edgeProgress.current[index] + 1 / GROWTH_FRAMES,
          );
          growing = true;
          edgeColorsDirty = true;
        }
        const edge = visibleEdges.current[index];
        const sourceIndex = nodeIndices.current.get(edge.source);
        const targetIndex = nodeIndices.current.get(edge.target);
        if (sourceIndex === undefined || targetIndex === undefined) continue;
        const positionOffset = index * 6;
        edgePositions.set(
          currentPositions.current.subarray(
            sourceIndex * 3,
            sourceIndex * 3 + 3,
          ),
          positionOffset,
        );
        edgePositions.set(
          currentPositions.current.subarray(
            targetIndex * 3,
            targetIndex * 3 + 3,
          ),
          positionOffset + 3,
        );
        const brightness = easeOutCubic(edgeProgress.current[index]);
        for (let component = 0; component < 6; component += 1) {
          edgeColors[positionOffset + component] =
            edgeBaseColors[positionOffset + component] * brightness;
        }
      }
      edgeGeometry.setDrawRange(0, edgeCount * 2);
      if (edgeCount > 0) {
        edgePositionAttribute.needsUpdate = true;
        if (edgeColorsDirty) edgeColorAttribute.needsUpdate = true;
      }
      return growing;
    };

    const fitCamera = (now: number) => {
      if (
        visibleNodes.current.length === 0 ||
        now < userControlledUntil.current ||
        bounds.isEmpty()
      ) {
        return;
      }
      bounds.getCenter(boundsCenter);
      bounds.getSize(boundsSize);
      const radius = Math.max(22, boundsSize.length() * 0.5);
      const desiredDistance = Math.max(
        90,
        (radius / Math.sin((camera.fov * Math.PI) / 360)) * 1.18,
      );
      cameraDirection.copy(camera.position).sub(controls.target).normalize();
      cameraDirection.applyAxisAngle(yAxis, 0.0018);
      controls.target.lerp(boundsCenter, 0.12);
      const currentDistance = camera.position.distanceTo(controls.target);
      const distance = currentDistance + (desiredDistance - currentDistance) * 0.1;
      camera.position
        .copy(controls.target)
        .addScaledVector(cameraDirection, distance);
      camera.near = Math.max(0.1, distance - radius * 2.5);
      camera.far = Math.max(2000, distance + radius * 4);
      camera.updateProjectionMatrix();
    };

    const report = (now: number) => {
      if (now - lastReport < 500) return;
      lastReport = now;
      const average = (values: number[]) =>
        values.length > 0
          ? values.reduce((sum, value) => sum + value, 0) / values.length
          : 0;
      const interval = average(frameIntervals);
      onProgressRef.current(
        visibleNodes.current.length,
        visibleEdges.current.length,
        interval > 0 ? 1000 / interval : 0,
        average(renderDurations),
      );
    };

    const draw = (now: number) => {
      const elapsed = now - lastTick;
      if (elapsed >= DRAW_INTERVAL) {
        lastTick = now - (elapsed % DRAW_INTERVAL);
        if (resetRequested.current) {
          resetRequested.current = false;
          reset();
        }
        const grew = appendGrowth();
        const moved = applyLayout();
        if (grew || moved) motionTicksRemaining = 10;
        const buffersChanged = motionTicksRemaining > 0 || layoutActive.current;
        const growing = buffersChanged ? updateBuffers() : false;
        if (motionTicksRemaining > 0) motionTicksRemaining -= 1;
        if (buffersChanged) fitCamera(now);
        const controlsMoving = controls.update();

        const active =
          grew ||
          moved ||
          growing ||
          buffersChanged ||
          controlsMoving ||
          pendingNodes.current.length > 0 ||
          readyEdges.current.length > 0 ||
          now < userControlledUntil.current ||
          renderRequested;
        if (active) {
          const renderStarted = performance.now();
          renderer.render(scene, camera);
          const renderedAt = performance.now();
          if (lastRender > 0) {
            const interval = renderedAt - lastRender;
            if (interval < 250) {
              frameIntervals.push(interval);
              if (frameIntervals.length > 48) frameIntervals.shift();
            }
          }
          lastRender = renderedAt;
          renderDurations.push(renderedAt - renderStarted);
          if (renderDurations.length > 48) renderDurations.shift();
          renderRequested = false;
        }
        report(now);
      }
      animationFrame = window.requestAnimationFrame(draw);
    };

    const pick = (event: PointerEvent, select: boolean) => {
      const now = performance.now();
      if (!select && now - hoverCheckAt < 80) return;
      hoverCheckAt = now;
      const rectangle = renderer.domElement.getBoundingClientRect();
      pointer.x = ((event.clientX - rectangle.left) / rectangle.width) * 2 - 1;
      pointer.y = -((event.clientY - rectangle.top) / rectangle.height) * 2 + 1;
      raycaster.setFromCamera(pointer, camera);
      const hit = raycaster.intersectObject(nodeMesh, false)[0];
      const instance = hit?.instanceId;
      const node = instance === undefined ? undefined : visibleNodes.current[instance];
      if (select) {
        onSelectRef.current(node ?? null);
        return;
      }
      if (!tooltip.current) return;
      if (!node) {
        tooltip.current.hidden = true;
        renderer.domElement.style.cursor = "grab";
        return;
      }
      tooltip.current.hidden = false;
      tooltip.current.textContent = node.statement;
      tooltip.current.style.transform = `translate(${event.clientX + 12}px, ${event.clientY + 12}px)`;
      renderer.domElement.style.cursor = "pointer";
    };
    const handlePointerMove = (event: PointerEvent) => pick(event, false);
    const handleClick = (event: PointerEvent) => pick(event, true);
    renderer.domElement.addEventListener("pointermove", handlePointerMove);
    renderer.domElement.addEventListener("click", handleClick);

    animationFrame = window.requestAnimationFrame(draw);
    return () => {
      window.cancelAnimationFrame(animationFrame);
      resizeObserver.disconnect();
      controls.dispose();
      worker.terminate();
      workerRef.current = null;
      renderer.domElement.removeEventListener("pointermove", handlePointerMove);
      renderer.domElement.removeEventListener("click", handleClick);
      nodeGeometry.dispose();
      nodeMaterial.dispose();
      edgeGeometry.dispose();
      edgeMaterial.dispose();
      grid.geometry.dispose();
      gridMaterial.dispose();
      renderer.dispose();
      renderer.domElement.remove();
    };
  }, []);

  useEffect(() => {
    const nextNodes = new Map(nodes.map((node) => [node.id, node]));
    const nextEdges = new Map(links.map((edge) => [edge.id, edge]));
    const removed =
      [...queuedNodes.current].some((id) => !nextNodes.has(id)) ||
      [...queuedEdges.current].some((id) => !nextEdges.has(id));

    targetNodes.current = nextNodes;
    targetEdges.current = nextEdges;
    const incidents = new Map<string, string[]>();
    for (const edge of links) {
      const source = incidents.get(edge.source) ?? [];
      source.push(edge.id);
      incidents.set(edge.source, source);
      const target = incidents.get(edge.target) ?? [];
      target.push(edge.id);
      incidents.set(edge.target, target);
    }
    incidentEdges.current = incidents;

    if (removed) {
      queuedNodes.current.clear();
      queuedEdges.current.clear();
      pendingNodes.current = [];
      waitingEdges.current.clear();
      readyEdges.current = [];
      readyEdgeIds.current.clear();
      resetRequested.current = true;
    }

    queueTopology(nodes, links, queuedNodes.current, pendingNodes.current);
    for (const edge of links) {
      if (queuedEdges.current.has(edge.id)) continue;
      queuedEdges.current.add(edge.id);
      waitingEdges.current.add(edge.id);
      const sourceVisible = nodeIndices.current.has(edge.source);
      const targetVisible = nodeIndices.current.has(edge.target);
      if (sourceVisible && targetVisible && !resetRequested.current) {
        waitingEdges.current.delete(edge.id);
        readyEdgeIds.current.add(edge.id);
        readyEdges.current.push(edge.id);
      }
    }
  }, [links, nodes]);

  const holdCamera = () => {
    userControlledUntil.current = performance.now() + CAMERA_HOLD_MS;
  };

  return (
    <div
      ref={container}
      className={withInspector ? "graph-fill graph-with-inspector" : "graph-fill"}
      onPointerDown={holdCamera}
      onWheel={holdCamera}
    >
      <div ref={tooltip} className="graph-tooltip" hidden />
    </div>
  );
}
