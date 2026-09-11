# spec-oracle UI — graph view

The Next.js UI renders the specification graph as an evidence-weighted XY
proximity view. Three.js submits Nodes as one instanced WebGL draw and persisted
Edges as one line-segment draw. Layout runs off the UI thread in a Worker. Every
layout coordinate has `z = 0`; no accidental force dimension is presented as
meaning.

The default view does not store, detect, label, or draw bounded contexts. It
places every loaded Specification directly. Repeated relationships can produce
dense regions and weakly related regions can leave whitespace, so a context is
at most an interpretation of Node density. There is no ring, hull, background
plane, cluster color, cluster label, aggregate set Node, or quotient graph.

## Views

- **Graph** — every loaded Specification, positioned by the single proximity
  algorithm below. Non-Specification connector Nodes are layout-only.
- **Meaning** — persisted Specification-to-Specification semantic Edges.
- **Vocabulary** — exact written-term incidence, explicitly not support.
- **Refinement** and **Conflicts** — focused semantic relation diagnostics.
- **Selection** and **Fitness** — persisted selection judgments and scores.
- **Contracts** — assume-guarantee projections and proved pairing relations.
- **Ledger** — immutable current and historical Edge versions.
- **Current set** — the selected specification graph.

Directed Edges shade from a dim source endpoint to a bright target endpoint.
The relation panel states endpoint roles, family, and derivation version, so
direction is not inferred from color or layout.

## One stateful layout objective

Acquisition, layout evolution, and rendering advance independently:

```text
100-Specification pages -> one evolving evidence objective -> 24 fps renderer
```

The Worker accumulates each page into one two-dimensional `d3-force-3d`
simulation. Newly accumulated Specifications enter that objective's
deterministic XY initialization and begin receiving its forces immediately.
When document frequency or connector degree changes, the same evidence weights
are rebuilt from the accumulated graph while preserving every existing
simulation Node, coordinate, velocity, current temperature, and elapsed
simulation history. The Worker applies one queued page, updates the mutable
forces, publishes at least one tick of movement, and only then applies the next
page. There is no provisional algorithm, terminal layout switch, or coordinate
replacement. Acquisition completion is a status notification and cannot
rebuild or reheat the simulation. The renderer reveals newly positioned GPU
instances from its own 24 fps queue while the Worker continues publishing the
same objective's coordinates.

The single simulation combines independently explainable signals:

1. Persisted semantic and selection Edges have the strongest link forces.
2. Shared persisted Term, Evidence, Assumption, Guarantee, Behavior, and Entity
   connectors supply weaker factual routes. Each incidence is normalized by
   `1 / sqrt(max(1, degree - 1))`; corpus-wide connectors therefore remain true
   without collapsing every Specification onto one hub.
3. Unicode word and adjacent-word features from Specification statements add
   view-only candidate proximity. Normalized inverse document frequency reduces
   grammar shared by most of the corpus. These features affect distance only:
   they are never materialized, persisted, or drawn as semantic support.
4. Repulsion and collision avoidance keep distinct visible Nodes legible.

Degree-normalized feature weights pass through the same bounded superlinear
force conversion. This preserves more contrast between a rare shared phrase
and a corpus-wide phrase without introducing a term-name allowlist. Sufficiently
sparse routes also add pair-local affinity; broad routes remain centroid forces
and cannot turn into a quadratic all-pairs expansion. Local repulsion and
collision use a deterministic uniform XY index, so convergence cost depends on
nearby visible Specifications rather than every connector pair.

Independent signals add force. Sharing several narrow connectors, wording
features, and a checked semantic Edge therefore produces more proximity than
sharing only one broad connector. The logical identity Assumption `⊤` may be
present in an acquired page, but it has no layout influence and is not rendered
in the default view because it carries no contextual information. It remains
available in diagnostic Contracts and Ledger data.

The algorithm contains no `context_id`, crate or command name, expected context
count, current corpus size, or authored threshold for a known data set. Its
stable uniform initialization supplies coordinates before enough relationships
exist to move a Node; all subsequent movement comes from the same declared
objective. Randomness is not evidence.

Only persisted Edges are rendered. A lexical feature can move two
Specifications closer but cannot manufacture a line between them.

## Loading and scale

`GET /api/graph` is a thin BFF over `specd`'s paged gRPC graph API. The browser
loads 100-Specification pages up to the UI safety capacity. The default view
retains every loaded Specification—there is no representative sampling or
cluster replacement. Diagnostic projections remain bounded where their purpose
is narrower than the default graph.

Each acquired page is appended immediately to a loading buffer. It is not a
render batch. The Worker returns coordinates for the accumulated graph, while
the main thread independently consumes at most two newly positioned
Specifications and four ready persisted Edges per 24 fps presentation cycle.
Acquisition never waits for that presentation queue, presentation never waits
for complete acquisition, and acquisition completion never flushes the queue.
Fast page responses use functional buffer appends, so React update coalescing
cannot replace or lose an earlier page. Diagnostic-view arrays and their
derived projections are not materialized while the default graph is growing;
they are hydrated from the acquisition store only when a diagnostic view is
opened.
If acquisition outpaces layout work, pages queue inside the Worker so each
applied append is followed by a force tick before the next append. The final
page follows the same path as every other page; only the existing simulation's
ordinary cooling continues afterward.

## Verification

`npm test` exercises the generic invariants: two local vocabularies remain
separate despite a global Term, a global Term alone does not create a partition,
independent routes increase proximity, semantic links dominate lexical
candidate proximity, `⊤` is absent from the default model, and every coordinate
has `z = 0`. Streaming tests additionally verify that append preserves the
simulation and existing Node objects, coordinates, velocities, and alpha, and
that an empty status-only update cannot rebuild, reheat, or move the objective.

With `specd` and the UI running, `npm run analyze:layout` lays out the actual
graph and reports all-Specification coverage, runtime, Z values, and post-hoc
nearest-neighbor enrichment for evaluation cohorts. Cohort phrases are metrics
only and never enter the layout.

`npm run measure:layout:browser` opens the production build in an isolated
headless Chrome profile. It records the first pre-completion draw, the number of
coordinate and objective updates produced before acquisition completes,
per-append movement, the completion transition, the converged Worker buffer,
main-thread long tasks, and the whole Chrome process tree. The
process-tree increase is a conservative upper bound on additional Worker memory
because it also includes concurrent browser allocation. These observations do
not by themselves establish that the layout reveals meaningful specification
subsets.

## Run

```sh
cp .env.local.example .env.local
npm install
npm test
npm run dev

# With specd and the UI running:
npm run analyze:layout
npm run measure:layout:browser
```

`specd` defaults to `127.0.0.1:50051`. For a non-persistent local demo it can be
started with `specd --store memory`.
