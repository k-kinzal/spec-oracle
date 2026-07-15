# spec-oracle UI — graph view

A Next.js app that visualizes the spec-oracle specification graph as a
force-directed 3D cloud. Three.js renders nodes as one instanced WebGL draw and
edges as one dynamic line-segment draw; a persistent `d3-force-3d` Worker owns
the three-dimensional layout. Each
specification node is one grounded sentence; derived term-form nodes connect
specifications through vocabulary they actually share, Evidence nodes expose
captured grounding, Assumption/Guarantee nodes expose the ingest contract, and
proved semantic Edges show refinement, equivalence, and force-aware conflicts.

The UI exposes bounded projections of the loaded Ledger rather than treating
one all-purpose graph as every answer:

- **Graph** — specifications, term, Evidence, Assumption, and Guarantee nodes,
  and every Edge selected by its current derivation/projection policy.
- **Meaning** — specification-to-specification semantic Edges only.
- **Vocabulary** — lexical `source mentions target` incidence, explicitly not
  support.
- **Refinement** — directed pairs with the stronger/refining source and the
  weaker/refined target named on every card.
- **Conflicts** — symmetric conflict pairs, isolated from unrelated topology.
- **Isolated** — specifications with no current semantic Edge; lexical mentions
  do not make a specification semantically connected.
- **Selection** — independently versioned Supports, Defeats, and Supersedes
  relations already present in the Ledger.
- **Fitness** — every candidate ranked by `selection/fitness-v4`, with the
  effective Evidence/support point sum and all survival or exclusion reasons.
- **Contracts** — proved pairing relations together with the target's
  current Assumption/Guarantee projections. Each pairing card names the source
  evidence, the explicit relied authored assertion, and the target contract;
  the Assumption node shows the relied words (or their conjunction), while its
  wire value also carries the canonical formula JSON.
- **Ledger** — every immutable Edge version, fetched lazily from the separate
  Edge-keyset API. Current derivations retain their colors; superseded derivations
  and projections are dimmed and labeled `Ledger history`. This is where the
  provisional `⊤` Assumption remains observable after a paired Assumption
  becomes current.
- **Current set** — candidates with positive fitness and no selected explicit
  blocker or selected semantic competitor. Admission alone never makes a sentence
  current. The view is the induced graph of selected specifications, their
  current Evidence and meaning projections, and the relationships that remain
  between them. Its panel reports loaded-scope grounding, Counter Evidence,
  transferred-support-only, and selected-conflict diagnostics.
  The exact versioned calculation is documented in
  [`../docs/selection.md`](../docs/selection.md).
Directed Edges shade from a dim source endpoint to a bright target endpoint.
The relation panel also spells out the endpoint roles carried over the wire,
the Edge family, and its derivation method/version, so color ordering is never
the sole explanation of direction. Semantic direction is never reinterpreted
as support flow.

## Architecture

```
Browser (Three.js, instanced WebGL, 24 Hz presentation clock)
   │
   ├── d3-force-3d Web Worker (persistent 3D layout)
   │  JSON  GET /api/graph
   ▼
Next.js Route Handler  (app/api/graph/route.ts)  ── the BFF, Node runtime
   │  gRPC  GetGraph                              (lib/grpc.ts)
   ▼
specd  (spec_oracle.v1.SpecificationGraph)
```

`specd` stays gRPC-only. The browser cannot speak gRPC, so a thin Next.js
backend-for-frontend loads the shared `../so_protocol/proto` and proxies to the
daemon — mirroring `so_client`'s thin-client role, in TypeScript.

## Scale

The graph can hold billions of nodes; the browser cannot. Nothing here ever
requests "everything":

- **Keyset pagination** end to end — the daemon hard-caps a page at 1000 nodes
  and returns an opaque `next_page_token`; the BFF clamps the requested size too.
- The UI pulls the graph in **100-specification automatic pages** and
  **caps** what it renders (`RENDER_CAP`). Network pages feed a buffer while the
  canvas grows in small, stable increments, showing live "loaded X of TOTAL"
  progress without requiring a user action between batches (see `app/page.tsx`).
  Acquisition never waits for presentation. The 3D force layout runs in a
  Worker throughout growth and convergence. The main thread samples its latest
  coordinates, updates the two GPU batches, and renders at a 24 Hz target; it
  sleeps once settled and wakes for later data or pointer interaction. The UI
  reports measured fps and render time rather than claiming the target rate.

`GetGraph` returns a bounded specification page, adjacent term and projection
nodes, and checked edges. Teal term nodes mean only equal normalized written forms; they
do not assert referent identity. Shared terms are a versioned candidate search,
not a semantic boundary. The daemon persists only outcomes proved by its
current `assess` rules; Unknown, Independent, and unsearched pairs are not
topology, so Edge absence has no negative meaning. A semantic Edge may arrive
before its other endpoint on a later page; the UI retains it and renders it
once both endpoints are loaded.

## Run

```sh
cp .env.local.example .env.local     # point SPEC_ORACLE_GRPC_ADDR at specd
npm install
npm run dev                          # http://localhost:3000
```

`specd` must be running and reachable (default `127.0.0.1:50051`). Seed a few
nodes first with `spec add "..."`.

No ArangoDB handy? Run the daemon against its in-memory backend:
`specd --store memory` (non-persistent — for demos and local UI work).
