import {
  createSpecificationEvidenceSimulation,
  readSpecificationEvidenceSimulation,
  resumeSpecificationEvidenceSimulation,
  updateSpecificationEvidenceSimulation,
  type SpecificationEvidenceSimulation,
} from "@/lib/specification-evidence-layout";
import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
} from "@/lib/specification-layout";

type WorkerInput =
  | {type: "reset"; generation: number}
  | {
      type: "append";
      generation: number;
      nodes: SpecificationLayoutInputNode[];
      edges: SpecificationLayoutInputEdge[];
      topologyComplete: boolean;
    };

let generation = 0;
let sequence = 0;
let active: SpecificationEvidenceSimulation | null = null;
let topologyComplete = false;
let settled = true;
let ticks = 0;
let startedAt = 0;
let lastPublished = 0;
let awaitingTickAfterAppend = false;
let appendTimer: ReturnType<typeof setTimeout> | null = null;
const pendingAppends: Array<Extract<WorkerInput, {type: "append"}>> = [];
const PUBLISH_INTERVAL = 1000 / 24;

function publishPositions(isSettled: boolean) {
  const state = active;
  if (!state) return;
  const result = readSpecificationEvidenceSimulation(state, ticks, true);
  self.postMessage(
    {
      type: "positions",
      generation,
      sequence: sequence++,
      ids: result.ids,
      positions: result.positions,
      featureCount: result.featureCount,
      routeCount: result.routeCount,
      iterations: result.iterations,
      objectiveUpdates: state.objectiveUpdates,
      alpha: state.simulation.alpha(),
      elapsedMs: performance.now() - startedAt,
      topologyComplete,
      settled: isSettled,
    },
    {transfer: [result.positions.buffer]},
  );
}

function publishStatus() {
  const state = active;
  if (!state) return;
  self.postMessage({
    type: "status",
    generation,
    sequence: sequence++,
    topologyComplete,
    settled,
    objectiveUpdates: state.objectiveUpdates,
    alpha: state.simulation.alpha(),
  });
}

function createActiveSimulation() {
  const state = createSpecificationEvidenceSimulation();
  active = state;
  settled = true;
  ticks = 0;
  startedAt = performance.now();
  lastPublished = 0;
  state.simulation.on("tick", () => {
    if (active !== state) return;
    settled = false;
    ticks += 1;
    const now = performance.now();
    if (awaitingTickAfterAppend) {
      // Every append is followed by an observable step of this same
      // simulation before the next append can update its forces. Do not let a
      // fast Worker tick flood the main thread between presentation frames:
      // retain this append until its moved state can be published at the same
      // maximum cadence as the renderer.
      if (now - lastPublished < PUBLISH_INTERVAL) return;
      awaitingTickAfterAppend = false;
      lastPublished = now;
      publishPositions(false);
      scheduleNextAppend();
      return;
    }
    if (now - lastPublished < PUBLISH_INTERVAL) return;
    lastPublished = now;
    publishPositions(false);
  });
  state.simulation.on("end", () => {
    if (active !== state) return;
    settled = true;
    if (awaitingTickAfterAppend) {
      awaitingTickAfterAppend = false;
      lastPublished = performance.now();
      publishPositions(true);
      scheduleNextAppend();
      return;
    }
    publishPositions(true);
  });
}

function scheduleNextAppend() {
  if (awaitingTickAfterAppend || appendTimer !== null) return;
  appendTimer = setTimeout(processNextAppend, 0);
}

function processNextAppend() {
  appendTimer = null;
  if (awaitingTickAfterAppend) return;
  const message = pendingAppends.shift();
  if (!message) return;
  const state = active;
  if (!state || message.generation !== generation) {
    scheduleNextAppend();
    return;
  }

  // Completion becomes visible only when its place in the append stream is
  // reached. It remains status and never mutates the objective by itself.
  const topologyChanged = message.topologyComplete !== topologyComplete;
  topologyComplete = message.topologyComplete;
  const update = updateSpecificationEvidenceSimulation(
    state,
    message.nodes,
    message.edges,
  );
  if (update.changed) {
    settled = false;
    awaitingTickAfterAppend = true;
    resumeSpecificationEvidenceSimulation(state);
    return;
  }
  if (topologyChanged) publishStatus();
  scheduleNextAppend();
}

self.addEventListener("message", (event: MessageEvent<WorkerInput>) => {
  const message = event.data;
  if (message.type === "reset") {
    active?.simulation.stop();
    generation = message.generation;
    sequence = 0;
    topologyComplete = false;
    awaitingTickAfterAppend = false;
    pendingAppends.length = 0;
    if (appendTimer !== null) clearTimeout(appendTimer);
    appendTimer = null;
    createActiveSimulation();
    return;
  }
  if (message.generation !== generation) return;
  if (!active) createActiveSimulation();
  pendingAppends.push(message);
  scheduleNextAppend();
});

export {};
