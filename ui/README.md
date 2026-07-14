# spec-oracle UI — graph view

A Next.js app that visualizes the spec-oracle specification graph as a
force-directed cloud (GPU/WebGL via [Cosmograph](https://cosmograph.app)). Each
specification node is one grounded sentence; derived term-form nodes connect
specifications through vocabulary they actually share, while proved semantic
Edges show refinement, equivalence, and force-aware conflicts.

The UI exposes bounded projections of the loaded Ledger rather than treating
one all-purpose graph as every answer:

- **Graph** — specifications, term nodes, and every current Edge.
- **Meaning** — specification-to-specification semantic Edges only.
- **Vocabulary** — lexical `source mentions target` incidence, explicitly not
  support.
- **Refinement** — directed pairs with the stronger/refining source and the
  weaker/refined target named on every card.
- **Conflicts** — symmetric conflict pairs, isolated from unrelated topology.
- **Isolated** — specifications with no current semantic Edge; lexical mentions
  do not make a specification semantically connected.
- **Selection** — independently versioned Supports, Defeats, and Supersedes
  relations. It is empty until a selection method produces those Edges.
- **Current set** — a deliberately non-derived diagnostic until support,
  deduplication, and selection semantics are defined.

Directed Edges have arrowheads in the canvas. The relation panel also spells
out the endpoint roles carried over the wire, the Edge family, and its
derivation method/version, so an arrow is never the sole explanation of
direction. Semantic arrow direction is never reinterpreted as support flow.

## Architecture

```
Browser (Cosmograph, WebGL)
   │  JSON  GET /api/graph?pageSize&pageToken
   ▼
Next.js Route Handler  (app/api/graph/route.ts)  ── the BFF, Node runtime
   │  gRPC  GetGraph(page_size, page_token)       (lib/grpc.ts)
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
- The UI pulls the graph in **bounded batches** (`BATCH_NODES`) and **caps** what
  it renders (`RENDER_CAP`), showing "loaded X of TOTAL" and a "Load more"
  control (see `app/page.tsx`).

`GetGraph` returns a bounded specification page, adjacent term nodes, and
checked edges. Teal term nodes mean only equal normalized written forms; they
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
