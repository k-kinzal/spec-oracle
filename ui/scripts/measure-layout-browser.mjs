import {spawn, execFile} from "node:child_process";
import {mkdtemp, readFile, rm, writeFile} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join} from "node:path";
import {promisify} from "node:util";
import net from "node:net";

const execFileAsync = promisify(execFile);
const url = process.argv.find((value) => value.startsWith("--url="))?.slice(6) ??
  "http://127.0.0.1:3000";
const chromePath =
  process.env.CHROME_PATH ??
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
const timeoutMs = Number(
  process.argv.find((value) => value.startsWith("--timeout="))?.slice(10) ??
    120_000,
);
const streamingWindowMs = Number(
  process.argv
    .find((value) => value.startsWith("--streaming-window="))
    ?.slice(19) ?? 0,
);
const screenshotPath = process.argv
  .find((value) => value.startsWith("--screenshot="))
  ?.slice(13);
const progressiveScreenshotPath = process.argv
  .find((value) => value.startsWith("--progressive-screenshot="))
  ?.slice(25);
const graphFixturePath = process.argv
  .find((value) => value.startsWith("--graph-fixture="))
  ?.slice(16);

async function availablePort() {
  const server = net.createServer();
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", resolve);
  });
  const address = server.address();
  if (!address || typeof address === "string") throw new Error("No debug port");
  await new Promise((resolve) => server.close(resolve));
  return address.port;
}

async function waitForJson(endpoint, deadline) {
  let error;
  while (Date.now() < deadline) {
    try {
      const response = await fetch(endpoint);
      if (response.ok) return await response.json();
    } catch (value) {
      error = value;
    }
    await new Promise((resolve) => setTimeout(resolve, 50));
  }
  throw error ?? new Error(`Timed out waiting for ${endpoint}`);
}

class CdpConnection {
  constructor(url) {
    this.socket = new WebSocket(url);
    this.nextId = 1;
    this.pending = new Map();
    this.listeners = new Set();
  }

  async open() {
    await new Promise((resolve, reject) => {
      this.socket.addEventListener("open", resolve, {once: true});
      this.socket.addEventListener("error", reject, {once: true});
    });
    this.socket.addEventListener("message", (event) => {
      const message = JSON.parse(String(event.data));
      if (message.id !== undefined) {
        const pending = this.pending.get(message.id);
        if (!pending) return;
        this.pending.delete(message.id);
        if (message.error) pending.reject(new Error(JSON.stringify(message.error)));
        else pending.resolve(message.result ?? {});
        return;
      }
      for (const listener of this.listeners) listener(message);
    });
  }

  send(method, params = {}, sessionId) {
    const id = this.nextId++;
    const message = {id, method, params};
    if (sessionId) message.sessionId = sessionId;
    return new Promise((resolve, reject) => {
      this.pending.set(id, {resolve, reject});
      this.socket.send(JSON.stringify(message));
    });
  }

  onEvent(listener) {
    this.listeners.add(listener);
    return () => this.listeners.delete(listener);
  }

  close() {
    this.socket.close();
  }
}

async function processTreeRss(rootPid) {
  const {stdout} = await execFileAsync("ps", ["-axo", "pid=,ppid=,rss="]);
  const rows = stdout
    .trim()
    .split("\n")
    .flatMap((line) => {
      const [pid, parent, rss] = line.trim().split(/\s+/).map(Number);
      return Number.isFinite(pid) ? [{pid, parent, rss}] : [];
    });
  const descendants = new Set([rootPid]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const row of rows) {
      if (!descendants.has(row.parent) || descendants.has(row.pid)) continue;
      descendants.add(row.pid);
      changed = true;
    }
  }
  return rows
    .filter((row) => descendants.has(row.pid))
    .reduce((sum, row) => sum + row.rss * 1024, 0);
}

const profile = await mkdtemp(join(tmpdir(), "spec-oracle-layout-chrome-"));
const port = await availablePort();
const chrome = spawn(
  chromePath,
  [
    "--headless=new",
    `--remote-debugging-port=${port}`,
    `--user-data-dir=${profile}`,
    "--no-first-run",
    "--no-default-browser-check",
    "--enable-unsafe-swiftshader",
    "--use-angle=swiftshader",
    "about:blank",
  ],
  {stdio: "ignore"},
);
const chromeExited = new Promise((resolve) => chrome.once("exit", resolve));

let connection;
try {
  const deadline = Date.now() + timeoutMs;
  const version = await waitForJson(
    `http://127.0.0.1:${port}/json/version`,
    deadline,
  );
  connection = new CdpConnection(version.webSocketDebuggerUrl);
  await connection.open();

  const workerSessions = new Map();
  connection.onEvent((event) => {
    if (
      event.method === "Target.attachedToTarget" &&
      event.params?.targetInfo?.type === "worker"
    ) {
      workerSessions.set(event.params.sessionId, event.params.targetInfo);
    }
  });
  await connection.send("Target.setAutoAttach", {
    autoAttach: true,
    waitForDebuggerOnStart: false,
    flatten: true,
  });
  const {targetId} = await connection.send("Target.createTarget", {
    url: "about:blank",
  });
  const {sessionId} = await connection.send("Target.attachToTarget", {
    targetId,
    flatten: true,
  });
  await connection.send("Page.enable", {}, sessionId);
  await connection.send("Runtime.enable", {}, sessionId);
  if (graphFixturePath) {
    const graphFixture = await readFile(graphFixturePath);
    await connection.send(
      "Fetch.enable",
      {patterns: [{urlPattern: "*://*/api/graph*", requestStage: "Request"}]},
      sessionId,
    );
    connection.onEvent((event) => {
      if (
        event.sessionId !== sessionId ||
        event.method !== "Fetch.requestPaused"
      ) {
        return;
      }
      void connection
        .send(
          "Fetch.fulfillRequest",
          {
            requestId: event.params.requestId,
            responseCode: 200,
            responseHeaders: [
              {name: "content-type", value: "application/json"},
              {name: "cache-control", value: "no-store"},
            ],
            body: graphFixture.toString("base64"),
          },
          sessionId,
        )
        .catch(() => {});
    });
  }
  await connection.send(
    "Emulation.setDeviceMetricsOverride",
    {width: 1200, height: 1000, deviceScaleFactor: 1, mobile: false},
    sessionId,
  );
  await connection.send(
    "Target.setAutoAttach",
    {
      autoAttach: true,
      waitForDebuggerOnStart: false,
      flatten: true,
    },
    sessionId,
  );
  await connection.send(
    "Page.addScriptToEvaluateOnNewDocument",
    {
      source: `
        globalThis.__specOracleLongTasks = [];
        if (typeof PerformanceObserver !== "undefined") {
          try {
            new PerformanceObserver((list) => {
              for (const entry of list.getEntries()) {
                globalThis.__specOracleLongTasks.push({
                  startTime: entry.startTime,
                  duration: entry.duration,
                  name: entry.name,
                });
              }
            }).observe({type: "longtask", buffered: true});
          } catch {}
        }
      `,
    },
    sessionId,
  );

  const baselineRss = await processTreeRss(chrome.pid);
  let peakRss = baselineRss;
  const rssSamples = [];
  let sampling = true;
  const memorySampler = (async () => {
    while (sampling) {
      const rss = await processTreeRss(chrome.pid);
      const sampledAt = Date.now();
      rssSamples.push({sampledAt, rss});
      peakRss = Math.max(peakRss, rss);
      await new Promise((resolve) => setTimeout(resolve, 25));
    }
  })();

  await connection.send("Page.navigate", {url}, sessionId);
  let snapshot;
  let progressiveScreenshotCaptured = false;
  let requestObservedAt = 0;
  let resultObservedAt = 0;
  let lastTimelineKey = "";
  const timeline = [];
  while (Date.now() < deadline) {
    const response = await connection.send(
      "Runtime.evaluate",
      {
        expression: `(() => {
          const host = document.querySelector(".graph-fill");
          return {
            readyState: document.readyState,
            dataset: host ? {...host.dataset} : null,
            statusText: document.querySelector(".status")?.textContent ?? null,
            scopeText: document.querySelector(".scope")?.textContent ?? null,
            longTasks: globalThis.__specOracleLongTasks ?? [],
            error: document.querySelector("nextjs-portal")?.textContent ?? null,
          };
        })()`,
        returnByValue: true,
      },
      sessionId,
    );
    snapshot = response.result?.value;
    const timelineKey = snapshot?.dataset
      ? [
          snapshot.dataset.layoutPositionUpdates,
          snapshot.dataset.layoutStatusUpdates,
          snapshot.dataset.layoutObjectiveUpdates,
          snapshot.dataset.layoutTopologyComplete,
          snapshot.dataset.layoutState,
          snapshot.dataset.layoutLoadedNodes,
          snapshot.dataset.layoutPresentedNodes,
          snapshot.dataset.layoutBufferedNodes,
        ].join(":")
      : "";
    if (timelineKey && timelineKey !== lastTimelineKey) {
      lastTimelineKey = timelineKey;
      timeline.push({
        observedAt: Date.now(),
        resultNodes: Number(snapshot.dataset.layoutResultNodes ?? 0),
        positionUpdates: Number(snapshot.dataset.layoutPositionUpdates ?? 0),
        statusUpdates: Number(snapshot.dataset.layoutStatusUpdates ?? 0),
        objectiveUpdates: Number(snapshot.dataset.layoutObjectiveUpdates ?? 0),
        alpha: Number(snapshot.dataset.layoutAlpha ?? 0),
        topologyComplete:
          snapshot.dataset.layoutTopologyComplete === "true",
        state: snapshot.dataset.layoutState ?? null,
        loadedNodes: Number(snapshot.dataset.layoutLoadedNodes ?? 0),
        presentedNodes: Number(snapshot.dataset.layoutPresentedNodes ?? 0),
        bufferedNodes: Number(snapshot.dataset.layoutBufferedNodes ?? 0),
      });
    }
    if (
      progressiveScreenshotPath &&
      !progressiveScreenshotCaptured &&
      snapshot?.dataset?.layoutFirstDrawAt &&
      snapshot?.dataset?.layoutFirstDrawTopologyComplete === "false"
    ) {
      const screenshot = await connection.send(
        "Page.captureScreenshot",
        {format: "png", fromSurface: true, captureBeyondViewport: false},
        sessionId,
      );
      await writeFile(
        progressiveScreenshotPath,
        Buffer.from(screenshot.data, "base64"),
      );
      progressiveScreenshotCaptured = true;
    }
    if (snapshot?.dataset?.layoutRequestedAt && requestObservedAt === 0) {
      requestObservedAt = Date.now();
    }
    if (snapshot?.dataset?.layoutReceivedAt && resultObservedAt === 0) {
      resultObservedAt = Date.now();
    }
    if (snapshot?.dataset?.layoutState === "complete-frame") break;
    if (
      streamingWindowMs > 0 &&
      requestObservedAt > 0 &&
      Date.now() - requestObservedAt >= streamingWindowMs
    ) {
      break;
    }
    if (snapshot?.dataset?.layoutError) {
      throw new Error(snapshot.dataset.layoutError);
    }
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  sampling = false;
  await memorySampler;
  const completedFrame = snapshot?.dataset?.layoutState === "complete-frame";
  const completedStreamingWindow =
    streamingWindowMs > 0 &&
    requestObservedAt > 0 &&
    Date.now() - requestObservedAt >= streamingWindowMs;
  if (!completedFrame && !completedStreamingWindow) {
    throw new Error(
      `Layout did not submit a complete frame: ${JSON.stringify(snapshot)}`,
    );
  }
  if (screenshotPath) {
    const screenshot = await connection.send(
      "Page.captureScreenshot",
      {format: "png", fromSurface: true, captureBeyondViewport: false},
      sessionId,
    );
    await writeFile(screenshotPath, Buffer.from(screenshot.data, "base64"));
  }

  const requestedAt = Number(snapshot.dataset.layoutRequestedAt);
  const motionSamples = JSON.parse(
    snapshot.dataset.layoutMotionSamples ?? "[]",
  );
  const firstCompleteMotion = motionSamples.find(
    (sample) => sample.topologyComplete,
  );
  const lastPrecompleteMotion = motionSamples.findLast(
    (sample) => !sample.topologyComplete,
  );
  const completeMotionSamples = motionSamples.filter(
    (sample) => sample.topologyComplete,
  );
  const observedObjectiveUpdates = [
    ...new Set(motionSamples.map((sample) => sample.objectiveUpdates)),
  ].sort((left, right) => left - right);
  const intermediateMovement = observedObjectiveUpdates.slice(0, -1).map(
    (objectiveUpdate) => {
      const samples = motionSamples.filter(
        (sample) => sample.objectiveUpdates === objectiveUpdate,
      );
      return {
        objectiveUpdate,
        moved: samples.some((sample) => sample.meanDisplacement > 0),
      };
    },
  );
  const presentationTimeline = timeline.filter(
    (entry, index) =>
      index === 0 || entry.presentedNodes !== timeline[index - 1].presentedNodes,
  );
  const presentationIncrements = presentationTimeline.slice(1).map(
    (entry, index) =>
      entry.presentedNodes - presentationTimeline[index].presentedNodes,
  );
  const relevantLongTasks = (snapshot.longTasks ?? []).filter(
    (task) => task.startTime >= requestedAt,
  );
  const workerHeaps = [];
  for (const [workerSessionId, info] of workerSessions) {
    try {
      const heap = await connection.send(
        "Runtime.getHeapUsage",
        {},
        workerSessionId,
      );
      workerHeaps.push({url: info.url, ...heap});
    } catch {
      // A Worker can terminate between frame completion and heap inspection.
    }
  }
  const beforeLayoutSamples = rssSamples.filter(
    (sample) =>
      sample.sampledAt >= requestObservedAt - 750 &&
      sample.sampledAt <= requestObservedAt - 100,
  );
  const layoutSamples = rssSamples.filter(
    (sample) =>
      sample.sampledAt >= requestObservedAt - 100 &&
      sample.sampledAt <= resultObservedAt + 100,
  );
  const layoutWindowBaseline = Math.min(
    ...(beforeLayoutSamples.length > 0
      ? beforeLayoutSamples.map((sample) => sample.rss)
      : [baselineRss]),
  );
  const layoutWindowPeak = Math.max(
    ...(layoutSamples.length > 0
      ? layoutSamples.map((sample) => sample.rss)
      : [peakRss]),
  );
  const result = {
    url,
    dataset: Object.fromEntries(
      Object.entries(snapshot.dataset).filter(
        ([key]) => key !== "layoutMotionSamples",
      ),
    ),
    statusText: snapshot.statusText,
    scopeText: snapshot.scopeText,
    screenshotPath: screenshotPath ?? null,
    progressiveScreenshotPath:
      progressiveScreenshotCaptured ? progressiveScreenshotPath : null,
    streaming: {
      completedFrame,
      observationWindowMs: streamingWindowMs || null,
      timeline: timeline.filter(
        (entry, index) =>
          index === 0 ||
          entry.objectiveUpdates !== timeline[index - 1].objectiveUpdates ||
          entry.topologyComplete !== timeline[index - 1].topologyComplete ||
          entry.state !== timeline[index - 1].state ||
          entry.presentedNodes !== timeline[index - 1].presentedNodes,
      ),
      presentationSamples: presentationTimeline.length,
      presentationMonotonic: presentationIncrements.every(
        (increment) => increment > 0,
      ),
      minimumPresentationIncrement:
        presentationIncrements.length > 0
          ? Math.min(...presentationIncrements)
          : 0,
      maximumPresentationIncrement: Math.max(
        0,
        ...presentationIncrements,
      ),
      loadingLedPresentation: timeline.some(
        (entry) => entry.loadedNodes > entry.presentedNodes,
      ),
      retainedMotionSamples: motionSamples.length,
      lastPrecompleteMotion: lastPrecompleteMotion ?? null,
      firstCompleteMotion: firstCompleteMotion ?? null,
      completionObjectiveDelta:
        firstCompleteMotion && lastPrecompleteMotion
          ? firstCompleteMotion.objectiveUpdates -
            lastPrecompleteMotion.objectiveUpdates
          : 0,
      observedIntermediateUpdates: intermediateMovement.length,
      intermediateUpdatesMovedBeforeNext: intermediateMovement.filter(
        (sample) => sample.moved,
      ).length,
      intermediateUpdatesWithoutMovement: intermediateMovement
        .filter((sample) => !sample.moved)
        .map((sample) => sample.objectiveUpdate),
      maximumRetainedMeanDisplacement: Math.max(
        0,
        ...motionSamples.map((sample) => sample.meanDisplacement),
      ),
      maximumCompleteMeanDisplacement: Math.max(
        0,
        ...completeMotionSamples.map((sample) => sample.meanDisplacement),
      ),
      maximumRetainedNodeDisplacement: Math.max(
        0,
        ...motionSamples.map((sample) => sample.maximumDisplacement),
      ),
    },
    performance: {
      completeFrameMs: Number(snapshot.dataset.layoutCompleteFrameMs),
      maximumMainThreadLongTaskMs: Math.max(
        0,
        ...relevantLongTasks.map((task) => task.duration),
      ),
      longTasks: relevantLongTasks,
      browserTreeBaselineBytes: baselineRss,
      browserTreePeakBytes: peakRss,
      browserTreePeakAdditionalBytes: Math.max(0, peakRss - baselineRss),
      layoutWindowBaselineBytes: layoutWindowBaseline,
      layoutWindowPeakBytes: layoutWindowPeak,
      layoutWindowPeakAdditionalBytes: Math.max(
        0,
        layoutWindowPeak - layoutWindowBaseline,
      ),
      workerHeapsAfterComplete: workerHeaps,
    },
  };
  console.log(
    JSON.stringify(
      {
        ...result,
        purpose:
          "Runtime observations for the production path; no threshold defines layout quality or completion.",
      },
      null,
      2,
    ),
  );
} finally {
  connection?.close();
  if (chrome.exitCode === null) chrome.kill("SIGTERM");
  await Promise.race([
    chromeExited,
    new Promise((resolve) => setTimeout(resolve, 5_000)),
  ]);
  if (chrome.exitCode === null) {
    chrome.kill("SIGKILL");
    await chromeExited;
  }
  await rm(profile, {
    recursive: true,
    force: true,
    maxRetries: 5,
    retryDelay: 100,
  });
}
