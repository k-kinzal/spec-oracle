"use client";

import {useEffect, useRef} from "react";
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
import {OrbitControls} from "three/examples/jsm/controls/OrbitControls.js";
import {
  buildSupportContextBoundaries,
  supportContextLayoutEdges,
  type SupportContextModel,
} from "@/lib/specification-context";
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
const POSITION_EASING = 0.22;
const NODE_CAPACITY = 65536;
const EDGE_CAPACITY = 65536;
const CONTEXT_SEGMENT_CAPACITY = 65536;
const CONTEXT_RENDER_LIMIT = 512;
const CAMERA_HOLD_MS = 5000;

type LayoutPositionMessage = {
  type: "positions";
  generation: number;
  sequence: number;
  ids: string[];
  positions: Float32Array;
  featureCount: number;
  routeCount: number;
  iterations: number;
  objectiveUpdates: number;
  alpha: number;
  elapsedMs: number;
  topologyComplete: boolean;
  settled: boolean;
};

type LayoutStatusMessage = {
  type: "status";
  generation: number;
  sequence: number;
  topologyComplete: boolean;
  settled: boolean;
  objectiveUpdates: number;
  alpha: number;
};

type LayoutMessage = LayoutPositionMessage | LayoutStatusMessage;

function nodeColor(node: GraphNode): Color {
  if (node.nodeKind === "term") return new Color(TERM_NODE_COLOR);
  if (node.nodeKind !== "specification") {
    return new Color(DERIVED_NODE_COLORS[node.nodeKind]);
  }
  const color = new Color(
    SPEECH_ACT_COLORS[node.speechAct] ?? SPEECH_ACT_COLORS.unknown,
  );
  if (node.evaluationState === "receded" || !node.current) {
    color.multiplyScalar(0.34);
  } else if (node.evaluationState === "unknown") {
    color.multiplyScalar(0.62);
  }
  return color;
}

function baseNodeSize(node: GraphNode): number {
  return node.nodeKind === "specification"
    ? 2.2 + Math.min(Math.max(node.supportScore, 0), 24) * 0.11
    : 1.8;
}

function layoutNodeRadius(node: GraphNode): number {
  return node.nodeKind === "specification"
    ? 4 + Math.min(Math.max(node.supportScore, 0), 24) * 0.24
    : 3;
}

function easeOutCubic(progress: number): number {
  return 1 - Math.pow(1 - progress, 3);
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

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function supportContextColor(contextId: string) {
  const hue = 0.34 + ((stableHash(contextId) % 10_000) / 10_000) * 0.42;
  return new Color().setHSL(hue, 0.66, 0.58);
}

export default function GraphView({
  nodes,
  links,
  supportContexts,
  onSelect,
  onDrawProgress,
  withInspector,
  hideLayoutConnectors,
  topologyComplete,
}: {
  nodes: GraphNode[];
  links: GraphEdge[];
  supportContexts: SupportContextModel;
  onSelect: (node: GraphNode | null) => void;
  onDrawProgress: (
    nodes: number,
    edges: number,
    actualFps: number,
    renderMs: number,
  ) => void;
  withInspector: boolean;
  hideLayoutConnectors: boolean;
  topologyComplete: boolean;
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
  const sentNodes = useRef(new Set<string>());
  const sentEdges = useRef(new Set<string>());
  const sentContextEdges = useRef(new Set<string>());
  const sentTopologyComplete = useRef(false);
  const drawableNodeCount = useRef(0);
  const drawableEdgeCount = useRef(0);
  const visibleNodes = useRef<GraphNode[]>([]);
  const visibleEdges = useRef<GraphEdge[]>([]);
  const visibleEdgeIds = useRef(new Set<string>());
  const nodeIndices = useRef(new Map<string, number>());
  const nodeProgress = useRef(new Float32Array(NODE_CAPACITY));
  const edgeProgress = useRef(new Float32Array(EDGE_CAPACITY));
  const positions = useRef(new Float32Array(NODE_CAPACITY * 3));
  const targetPositions = useRef(new Float32Array(NODE_CAPACITY * 3));
  const finalPositions = useRef(new Map<string, [number, number, number]>());
  const pendingNodes = useRef<string[]>([]);
  const pendingNodeCursor = useRef(0);
  const waitingEdges = useRef(new Set<string>());
  const readyEdges = useRef<string[]>([]);
  const readyEdgeCursor = useRef(0);
  const readyEdgeIds = useRef(new Set<string>());
  const layoutGeneration = useRef(0);
  const layoutReady = useRef(false);
  const topologyCompleteRef = useRef(topologyComplete);
  const motionActive = useRef(false);
  const workerRef = useRef<Worker | null>(null);
  const userControlledUntil = useRef(0);
  const supportContextsRef = useRef(supportContexts);

  onSelectRef.current = onSelect;
  onProgressRef.current = onDrawProgress;

  useEffect(() => {
    const host = container.current;
    if (!host) return;

    const scene = new Scene();
    scene.background = new Color(0x0f0f10);

    const camera = new PerspectiveCamera(47, 1, 0.1, 10000);
    camera.position.set(0, 0, 420);

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
    controls.enableRotate = false;
    controls.target.set(0, 0, 0);

    const grid = new GridHelper(520, 26, 0x27313d, 0x181c22);
    const gridMaterial = grid.material;
    gridMaterial.transparent = true;
    gridMaterial.opacity = 0.34;
    grid.rotation.x = Math.PI / 2;
    grid.position.z = -2;
    scene.add(grid);

    const contextBoundaryPositions = new Float32Array(
      CONTEXT_SEGMENT_CAPACITY * 6,
    );
    const contextBoundaryColors = new Float32Array(
      CONTEXT_SEGMENT_CAPACITY * 6,
    );
    const contextBoundaryGeometry = new BufferGeometry();
    const contextBoundaryPositionAttribute = new BufferAttribute(
      contextBoundaryPositions,
      3,
    );
    const contextBoundaryColorAttribute = new BufferAttribute(
      contextBoundaryColors,
      3,
    );
    contextBoundaryPositionAttribute.setUsage(DynamicDrawUsage);
    contextBoundaryColorAttribute.setUsage(DynamicDrawUsage);
    contextBoundaryGeometry.setAttribute(
      "position",
      contextBoundaryPositionAttribute,
    );
    contextBoundaryGeometry.setAttribute("color", contextBoundaryColorAttribute);
    contextBoundaryGeometry.setDrawRange(0, 0);
    const contextBoundaryMaterial = new LineBasicMaterial({
      vertexColors: true,
      transparent: true,
      opacity: 0.62,
      depthWrite: false,
    });
    const contextBoundaryLines = new LineSegments(
      contextBoundaryGeometry,
      contextBoundaryMaterial,
    );
    contextBoundaryLines.frustumCulled = false;
    contextBoundaryLines.renderOrder = -1;
    scene.add(contextBoundaryLines);

    const nodeGeometry = new IcosahedronGeometry(1, 0);
    const nodeMaterial = new MeshBasicMaterial({toneMapped: false});
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
      {type: "module", name: "spec-oracle-xy-layout"},
    );
    workerRef.current = worker;
    worker.postMessage({type: "reset", generation: layoutGeneration.current});
    let layoutReceivedAt = 0;
    let positionUpdateCount = 0;
    let precompletePositionUpdateCount = 0;
    let precompleteMaximumResultNodes = 0;
    let statusUpdateCount = 0;
    const motionSamples: Array<{
      sequence: number;
      nodes: number;
      objectiveUpdates: number;
      topologyComplete: boolean;
      settled: boolean;
      alpha: number;
      sharedNodes: number;
      meanDisplacement: number;
      maximumDisplacement: number;
    }> = [];
    worker.onmessage = (event: MessageEvent<LayoutMessage>) => {
      const message = event.data;
      if (message.generation !== layoutGeneration.current) return;
      host.dataset.layoutObjectiveUpdates = String(message.objectiveUpdates);
      host.dataset.layoutAlpha = message.alpha.toFixed(6);
      if (message.type === "status") {
        statusUpdateCount += 1;
        host.dataset.layoutStatusUpdates = String(statusUpdateCount);
        layoutReady.current = message.topologyComplete && message.settled;
        host.dataset.layoutState = layoutReady.current ? "settled" : "streaming";
        host.dataset.layoutTopologyComplete = String(message.topologyComplete);
        if (layoutReady.current) {
          layoutReceivedAt = performance.now();
          renderRequested = true;
        }
        return;
      }
      positionUpdateCount += 1;
      if (!message.topologyComplete) {
        precompletePositionUpdateCount += 1;
        precompleteMaximumResultNodes = Math.max(
          precompleteMaximumResultNodes,
          message.ids.length,
        );
      }
      let displacementSum = 0;
      let maximumDisplacement = 0;
      let sharedNodes = 0;
      for (let index = 0; index < message.ids.length; index += 1) {
        const previous = finalPositions.current.get(message.ids[index]);
        if (previous) {
          const displacement = Math.hypot(
            message.positions[index * 3] - previous[0],
            message.positions[index * 3 + 1] - previous[1],
          );
          displacementSum += displacement;
          maximumDisplacement = Math.max(maximumDisplacement, displacement);
          sharedNodes += 1;
        }
        finalPositions.current.set(message.ids[index], [
          message.positions[index * 3],
          message.positions[index * 3 + 1],
          0,
        ]);
        const node = targetNodes.current.get(message.ids[index]);
        if (
          node &&
          (!hideLayoutConnectors || node.nodeKind === "specification") &&
          !queuedNodes.current.has(node.id)
        ) {
          queuedNodes.current.add(node.id);
          pendingNodes.current.push(node.id);
        }
      }
      motionSamples.push({
        sequence: message.sequence,
        nodes: message.ids.length,
        objectiveUpdates: message.objectiveUpdates,
        topologyComplete: message.topologyComplete,
        settled: message.settled,
        alpha: message.alpha,
        sharedNodes,
        meanDisplacement:
          sharedNodes > 0 ? displacementSum / sharedNodes : 0,
        maximumDisplacement,
      });
      if (motionSamples.length > 256) motionSamples.shift();
      host.dataset.layoutMotionSamples = JSON.stringify(motionSamples);
      for (let index = 0; index < visibleNodes.current.length; index += 1) {
        const target = finalPositions.current.get(visibleNodes.current[index].id);
        if (target) targetPositions.current.set(target, index * 3);
      }
      layoutReady.current = message.topologyComplete && message.settled;
      motionActive.current = true;
      const receivedAt = performance.now();
      if (layoutReady.current) layoutReceivedAt = receivedAt;
      host.dataset.layoutState = layoutReady.current ? "settled" : "streaming";
      host.dataset.layoutTopologyComplete = String(message.topologyComplete);
      host.dataset.layoutReceivedAt = receivedAt.toFixed(3);
      host.dataset.layoutResultBytes = String(message.positions.byteLength);
      host.dataset.layoutResultNodes = String(message.ids.length);
      host.dataset.layoutDrawableNodes = String(message.ids.length);
      host.dataset.layoutDrawableEdges = String(drawableEdgeCount.current);
      if (!message.settled) delete host.dataset.layoutCompleteFrameMs;
      host.dataset.layoutFeatures = String(message.featureCount);
      host.dataset.layoutRoutes = String(message.routeCount);
      host.dataset.layoutIterations = String(message.iterations);
      host.dataset.layoutMs = message.elapsedMs.toFixed(1);
      host.dataset.layoutPositionUpdates = String(positionUpdateCount);
      host.dataset.layoutPrecompletePositionUpdates = String(
        precompletePositionUpdateCount,
      );
      host.dataset.layoutPrecompleteMaximumResultNodes = String(
        precompleteMaximumResultNodes,
      );
    };
    worker.onerror = (event) => {
      host.dataset.layoutError = event.message;
      console.error("specification layout Worker failed", event);
    };

    const dummyMatrix = new Matrix4();
    const dummyPosition = new Vector3();
    const dummyScale = new Vector3();
    const bounds = new Box3();
    const boundsCenter = new Vector3();
    const boundsSize = new Vector3();
    const cameraDirection = new Vector3();
    const raycaster = new Raycaster();
    const pointer = new Vector2();
    let animationFrame = 0;
    let lastTick = performance.now();
    let lastReport = lastTick;
    let lastRender = 0;
    let renderRequested = true;
    let hoverCheckAt = 0;
    let presentedNodeCount = 0;
    let presentedEdgeCount = 0;
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

    const makeEdgeReady = (edgeId: string) => {
      if (!waitingEdges.current.has(edgeId)) return;
      const edge = targetEdges.current.get(edgeId);
      if (
        !edge ||
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
      let changed = false;
      let nodesChanged = false;
      let edgesChanged = false;
      for (
        let count = 0;
        count < NODES_PER_DRAW &&
        pendingNodeCursor.current < pendingNodes.current.length;
        count += 1
      ) {
        const id = pendingNodes.current[pendingNodeCursor.current];
        pendingNodeCursor.current += 1;
        const node = id ? targetNodes.current.get(id) : undefined;
        if (!id || !node || nodeIndices.current.has(id)) continue;
        if (visibleNodes.current.length >= NODE_CAPACITY) break;
        const index = visibleNodes.current.length;
        const position = finalPositions.current.get(id);
        if (!position) continue;
        visibleNodes.current.push(node);
        nodeIndices.current.set(id, index);
        positions.current.set(position, index * 3);
        targetPositions.current.set(position, index * 3);
        nodeProgress.current[index] = 1 / GROWTH_FRAMES;
        nodeMesh.setColorAt(index, nodeColor(node));
        nodesChanged = true;
        if (!hideLayoutConnectors || node.nodeKind === "specification") {
          presentedNodeCount += 1;
        }
        for (const edgeId of incidentEdges.current.get(id) ?? []) {
          makeEdgeReady(edgeId);
        }
        changed = true;
      }

      for (
        let count = 0;
        count < EDGES_PER_DRAW &&
        readyEdgeCursor.current < readyEdges.current.length;
        count += 1
      ) {
        const id = readyEdges.current[readyEdgeCursor.current];
        readyEdgeCursor.current += 1;
        if (id) readyEdgeIds.current.delete(id);
        const edge = id ? targetEdges.current.get(id) : undefined;
        if (!id || !edge || visibleEdgeIds.current.has(id)) continue;
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
        const layoutOnlyEdge =
          hideLayoutConnectors &&
          (targetNodes.current.get(edge.source)?.nodeKind !== "specification" ||
            targetNodes.current.get(edge.target)?.nodeKind !== "specification");
        if (layoutOnlyEdge) {
          edgeBaseColors.fill(0, index * 6, index * 6 + 6);
        } else {
          const color = edgeColor(edge);
          const directed = DIRECTED_EDGE_KINDS.has(edge.kind);
          const sourceColor = directed
            ? color.clone().multiplyScalar(0.34)
            : color;
          edgeBaseColors.set(sourceColor.toArray(), index * 6);
          edgeBaseColors.set(color.toArray(), index * 6 + 3);
          presentedEdgeCount += 1;
        }
        edgesChanged = true;
        changed = true;
      }
      if (nodesChanged) {
        if (nodeMesh.instanceColor) nodeMesh.instanceColor.needsUpdate = true;
      }
      if (nodesChanged || edgesChanged) motionActive.current = true;
      return changed;
    };

    const updateBuffers = () => {
      const nodeCount = visibleNodes.current.length;
      let moving = false;
      bounds.makeEmpty();
      for (let index = 0; index < nodeCount; index += 1) {
        const offset = index * 3;
        for (let axis = 0; axis < 3; axis += 1) {
          const current = positions.current[offset + axis];
          const target = targetPositions.current[offset + axis];
          const delta = target - current;
          if (Math.abs(delta) > 0.02) {
            positions.current[offset + axis] =
              current + delta * POSITION_EASING;
            moving = true;
          } else {
            positions.current[offset + axis] = target;
          }
        }
        if (nodeProgress.current[index] < 1) {
          nodeProgress.current[index] = Math.min(
            1,
            nodeProgress.current[index] + 1 / GROWTH_FRAMES,
          );
          moving = true;
        }
        const scale =
          baseNodeSize(visibleNodes.current[index]) *
          easeOutCubic(nodeProgress.current[index]);
        dummyPosition.fromArray(positions.current, offset);
        dummyScale.setScalar(scale);
        dummyMatrix.makeScale(dummyScale.x, dummyScale.y, dummyScale.z);
        dummyMatrix.setPosition(dummyPosition);
        nodeMesh.setMatrixAt(index, dummyMatrix);
        bounds.expandByPoint(dummyPosition);
      }
      nodeMesh.count = nodeCount;
      if (nodeCount > 0) nodeMesh.instanceMatrix.needsUpdate = true;

      const contextPositions = new Map<string, {x: number; y: number}>();
      const renderedContexts = [...supportContextsRef.current.contexts]
        .sort(
          (left, right) =>
            right.totalPoints - left.totalPoints ||
            right.memberIds.length - left.memberIds.length ||
            left.id.localeCompare(right.id),
        )
        .slice(0, CONTEXT_RENDER_LIMIT);
      for (const context of renderedContexts) {
        for (const memberId of context.memberIds) {
          if (contextPositions.has(memberId)) continue;
          const memberIndex = nodeIndices.current.get(memberId);
          if (memberIndex === undefined) continue;
          contextPositions.set(memberId, {
            x: positions.current[memberIndex * 3],
            y: positions.current[memberIndex * 3 + 1],
          });
        }
      }
      const boundaries = buildSupportContextBoundaries(
        renderedContexts,
        contextPositions,
      );
      let contextSegmentCount = 0;
      for (const boundary of boundaries) {
        const color = supportContextColor(boundary.contextId);
        for (
          let pointIndex = 0;
          pointIndex < boundary.points.length &&
          contextSegmentCount < CONTEXT_SEGMENT_CAPACITY;
          pointIndex += 1
        ) {
          const current = boundary.points[pointIndex];
          const next =
            boundary.points[(pointIndex + 1) % boundary.points.length];
          const offset = contextSegmentCount * 6;
          contextBoundaryPositions.set([current.x, current.y, -0.8], offset);
          contextBoundaryPositions.set([next.x, next.y, -0.8], offset + 3);
          contextBoundaryColors.set(color.toArray(), offset);
          contextBoundaryColors.set(color.toArray(), offset + 3);
          contextSegmentCount += 1;
        }
      }
      contextBoundaryGeometry.setDrawRange(0, contextSegmentCount * 2);
      if (contextSegmentCount > 0) {
        contextBoundaryPositionAttribute.needsUpdate = true;
        contextBoundaryColorAttribute.needsUpdate = true;
      }
      host.dataset.supportContexts = String(boundaries.length);
      host.dataset.supportContextSegments = String(contextSegmentCount);
      host.dataset.supportContextNodes = String(
        supportContextsRef.current.contextualizedNodeCount,
      );
      host.dataset.supportContextSharedNodes = String(
        supportContextsRef.current.sharedFoundationCount,
      );

      const edgeCount = visibleEdges.current.length;
      for (let index = 0; index < edgeCount; index += 1) {
        if (edgeProgress.current[index] < 1) {
          edgeProgress.current[index] = Math.min(
            1,
            edgeProgress.current[index] + 1 / GROWTH_FRAMES,
          );
          moving = true;
        }
        const edge = visibleEdges.current[index];
        const sourceIndex = nodeIndices.current.get(edge.source);
        const targetIndex = nodeIndices.current.get(edge.target);
        if (sourceIndex === undefined || targetIndex === undefined) continue;
        const positionOffset = index * 6;
        edgePositions.set(
          positions.current.subarray(sourceIndex * 3, sourceIndex * 3 + 3),
          positionOffset,
        );
        edgePositions.set(
          positions.current.subarray(targetIndex * 3, targetIndex * 3 + 3),
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
        edgeColorAttribute.needsUpdate = true;
      }
      return moving;
    };

    const fitCamera = (now: number, immediate = false) => {
      if (
        visibleNodes.current.length === 0 ||
        now < userControlledUntil.current ||
        bounds.isEmpty()
      ) {
        return;
      }
      bounds.getCenter(boundsCenter);
      bounds.getSize(boundsSize);
      const halfVertical = boundsSize.y * 0.5;
      const halfHorizontalInVerticalUnits =
        (boundsSize.x * 0.5) / Math.max(0.1, camera.aspect);
      const framingHalfExtent = Math.max(
        22,
        halfVertical,
        halfHorizontalInVerticalUnits,
      );
      const desiredDistance = Math.max(
        90,
        (framingHalfExtent / Math.tan((camera.fov * Math.PI) / 360)) * 1.16,
      );
      cameraDirection.copy(camera.position).sub(controls.target).normalize();
      if (immediate) {
        controls.target.copy(boundsCenter);
        camera.position
          .copy(controls.target)
          .addScaledVector(cameraDirection, desiredDistance);
        return;
      }
      controls.target.lerp(boundsCenter, 0.12);
      const currentDistance = camera.position.distanceTo(controls.target);
      const distance = currentDistance + (desiredDistance - currentDistance) * 0.1;
      camera.position
        .copy(controls.target)
        .addScaledVector(cameraDirection, distance);
    };

    const report = (now: number, force = false) => {
      if (!force && now - lastReport < 500) return;
      lastReport = now;
      const average = (values: number[]) =>
        values.length > 0
          ? values.reduce((sum, value) => sum + value, 0) / values.length
          : 0;
      const interval = average(frameIntervals);
      onProgressRef.current(
        presentedNodeCount,
        presentedEdgeCount,
        interval > 0 ? 1000 / interval : 0,
        average(renderDurations),
      );
      host.dataset.layoutLoadedNodes = String(drawableNodeCount.current);
      host.dataset.layoutPresentedNodes = String(presentedNodeCount);
      host.dataset.layoutBufferedNodes = String(
        Math.max(0, pendingNodes.current.length - pendingNodeCursor.current),
      );
    };

    const draw = (now: number) => {
      const elapsed = now - lastTick;
      if (elapsed >= DRAW_INTERVAL) {
        lastTick = now - (elapsed % DRAW_INTERVAL);
        const grew = appendGrowth();
        if (grew) {
          host.dataset.layoutPresentedNodes = String(presentedNodeCount);
          host.dataset.layoutBufferedNodes = String(
            Math.max(0, pendingNodes.current.length - pendingNodeCursor.current),
          );
        }
        const buffersChanged = motionActive.current;
        const moving = buffersChanged ? updateBuffers() : false;
        motionActive.current = moving;
        if (grew || moving) fitCamera(now);
        const controlsMoving = controls.update();
        const active =
          grew ||
          buffersChanged ||
          moving ||
          controlsMoving ||
          pendingNodeCursor.current < pendingNodes.current.length ||
          readyEdgeCursor.current < readyEdges.current.length ||
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
          if (
            presentedNodeCount > 0 &&
            host.dataset.layoutFirstDrawAt === undefined
          ) {
            host.dataset.layoutFirstDrawAt = renderedAt.toFixed(3);
            host.dataset.layoutFirstDrawNodes = String(presentedNodeCount);
            host.dataset.layoutFirstDrawTopologyComplete = String(
              topologyCompleteRef.current,
            );
          }
          if (
            layoutReady.current &&
            layoutReceivedAt > 0 &&
            host.dataset.layoutCompleteFrameMs === undefined &&
            pendingNodeCursor.current >= pendingNodes.current.length &&
            readyEdgeCursor.current >= readyEdges.current.length &&
            waitingEdges.current.size === 0 &&
            !moving &&
            nodeProgress.current
              .subarray(0, visibleNodes.current.length)
              .every((progress) => progress >= 1) &&
            edgeProgress.current
              .subarray(0, visibleEdges.current.length)
              .every((progress) => progress >= 1)
          ) {
            host.dataset.layoutState = "complete-frame";
            host.dataset.layoutCompleteFrameMs = (
              renderedAt - layoutReceivedAt
            ).toFixed(3);
            host.dataset.layoutPresentedNodes = String(presentedNodeCount);
            host.dataset.layoutPresentedEdges = String(presentedEdgeCount);
            report(renderedAt, true);
          }
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
      tooltip.current.style.transform =
        `translate(${event.clientX + 12}px, ${event.clientY + 12}px)`;
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
      contextBoundaryGeometry.dispose();
      contextBoundaryMaterial.dispose();
      edgeGeometry.dispose();
      edgeMaterial.dispose();
      grid.geometry.dispose();
      gridMaterial.dispose();
      renderer.dispose();
      renderer.domElement.remove();
    };
  }, [hideLayoutConnectors]);

  useEffect(() => {
    supportContextsRef.current = supportContexts;
    const nextNodes = targetNodes.current;
    const nextEdges = targetEdges.current;
    for (const node of nodes) nextNodes.set(node.id, node);
    for (const edge of links) {
      const known = nextEdges.has(edge.id);
      nextEdges.set(edge.id, edge);
      if (known) continue;
      const source = incidentEdges.current.get(edge.source) ?? [];
      source.push(edge.id);
      incidentEdges.current.set(edge.source, source);
      const target = incidentEdges.current.get(edge.target) ?? [];
      target.push(edge.id);
      incidentEdges.current.set(edge.target, target);
    }
    for (const edge of links) {
      const drawable =
        !hideLayoutConnectors ||
        (nextNodes.get(edge.source)?.nodeKind === "specification" &&
          nextNodes.get(edge.target)?.nodeKind === "specification");
      if (!drawable || queuedEdges.current.has(edge.id)) continue;
      queuedEdges.current.add(edge.id);
      if (
        nodeIndices.current.has(edge.source) &&
        nodeIndices.current.has(edge.target)
      ) {
        readyEdgeIds.current.add(edge.id);
        readyEdges.current.push(edge.id);
      } else {
        waitingEdges.current.add(edge.id);
      }
    }
    drawableEdgeCount.current = queuedEdges.current.size;
    drawableNodeCount.current = [...nextNodes.values()].reduce(
      (count, node) =>
        count +
        Number(!hideLayoutConnectors || node.nodeKind === "specification"),
      0,
    );
    const host = container.current;
    if (host) host.dataset.layoutLoadedNodes = String(drawableNodeCount.current);
    topologyCompleteRef.current = topologyComplete;
    const worker = workerRef.current;
    if (!worker) return;
    const appendedNodes = nodes.flatMap((node) => {
      if (sentNodes.current.has(node.id)) return [];
      sentNodes.current.add(node.id);
      return [
        {
          id: node.id,
          nodeKind: node.nodeKind,
          statement: node.statement,
          radius: layoutNodeRadius(node),
          visible:
            !hideLayoutConnectors || node.nodeKind === "specification",
        },
      ];
    });
    const appendedEdges = links.flatMap((edge) => {
      if (sentEdges.current.has(edge.id)) return [];
      sentEdges.current.add(edge.id);
      return [
        {
          id: edge.id,
          source: edge.source,
          target: edge.target,
          current: edge.current,
          family: edge.family,
        },
      ];
    });
    const appendedContextEdges = supportContextLayoutEdges(
      supportContexts,
    ).flatMap((edge) => {
      if (sentContextEdges.current.has(edge.id)) return [];
      sentContextEdges.current.add(edge.id);
      return [edge];
    });
    const topologyChanged =
      sentTopologyComplete.current !== topologyComplete;
    if (
      appendedNodes.length === 0 &&
      appendedEdges.length === 0 &&
      appendedContextEdges.length === 0 &&
      !topologyChanged
    ) {
      return;
    }
    sentTopologyComplete.current = topologyComplete;
    if (host && host.dataset.layoutRequestedAt === undefined) {
      host.dataset.layoutRequestedAt = performance.now().toFixed(3);
      host.dataset.layoutState = "streaming";
      delete host.dataset.layoutError;
    }
    worker.postMessage({
      type: "append",
      generation: layoutGeneration.current,
      nodes: appendedNodes,
      edges: [...appendedEdges, ...appendedContextEdges],
      topologyComplete,
    });
    motionActive.current = true;
  }, [hideLayoutConnectors, links, nodes, supportContexts, topologyComplete]);

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
