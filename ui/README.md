# spec-oracle UI — graph view

A Next.js app that visualizes the spec-oracle specification graph as a
force-directed cloud (GPU/WebGL via [Cosmograph](https://cosmograph.app)). Each
specification node is one grounded sentence; derived term-form nodes connect
specifications through vocabulary they actually share.

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
do not assert referent identity. Semantic spec-to-spec edges are not generated
until their graph-side establishment rules are defined.

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
