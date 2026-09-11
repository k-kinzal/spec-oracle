# spec-oracle

A **specification graph** in constrained natural language, read through
assume-guarantee contracts.

A specification is written in an EARS-derived controlled language — one or more
sentences, each performing one specification act (defining a term, describing
the system, or obliging/forbidding/recommending/permitting behavior). The raw
words are the stored truth; each behavioral sentence *denotes an assertion*,
and `so-reason::contract` forms a semantic **assume-guarantee contract** over
a dedicated classical Boolean assertion domain projected from the constrained
NL formula. A lone sentence forms the provisional contract `(⊤, G)`
deterministically. Its assumption, guarantee, and semantic Contract are
materialized as content-addressed projection Nodes while the authored words
remain the authority. Algebraically derived composition, quotient, and merge
results are Contract Nodes too. (Definitions establish vocabulary and permissions merely
*admit* behavior, so neither carries a lone-sentence contract; a permission
enters contracts only through pairing, on the environment side.) A Specification
Node is accepted before its requested Evidence is captured; the post-acceptance
Consumer appends the captured view and materializes shared Evidence Nodes.

> **Scope.** The tool ingests (`spec add` — parse exactly one sentence and
> persist exactly one Node), processes Evidence and graph structure through
> Event Consumers, and renders the same Ledger-derived graph through `spec graph show`.
> The `--current` graph view exposes the automatically selected specification
> set without adding a separate command surface.
> NodeAdded generation
> connects specifications through derived written-term vertices. Those lexical
> connectors are a versioned candidate search, not semantic identity. Candidate
> pairs that `so-reason::relate::assess` can prove become the first persisted
> semantic Edge family: refinement, equivalence, and force-aware conflicts.
> Unknown/Independent verdicts are audit records rather than topology, and Edge
> absence has no negative meaning. Formula-level and Contract-level judgments
> are separate audit records; proved A/G refinement/equivalence connects
> Contract Nodes rather than overloading sentence Edges. The trivial ingest
> contract is projected to Assumption, Guarantee, and Contract Nodes. A
> non-trivial pairing records its evidence
> source, target contract, and explicitly selected relied specification as
> distinct authored roles. Only structurally proved, well-formed aggregates are
> admitted; the paired Assumption supersedes `⊤` in the current projection
> while every prior projection remains in the append-only Ledger. Every Edge
> belongs to a lexical, semantic, projection, or epistemic family and carries
> explicit endpoint roles. Lexical, semantic, and projection Edges are produced
> by registered mechanical derivations; the only manual Edges are narrowly
> typed Evidence judgments. Its
> `source` and `target` are the ordered arguments of that typed relation, not a
> universal support-flow direction. There is no generic manual Edge-addition
> path and no manual Specification-to-Specification selection Edge.
> The `selection/fitness-v15` current-set policy keeps decaying external
> Evidence separate from recursive Specification support. Logical support uses
> proved refinement and composition. Realization support is discovered from
> persisted `Specification → Behavior → Entity` projections by comparing
> grammatical action, actor, object, means, scope, and direction. An explicit
> means anchors a lower-layer→upper-layer relation; compatible object
> refinements may extend that anchored path toward still lower layers. An
> affirmative binding object's exact Entity may also be elaborated by a
> lower-layer specification that makes that Entity its responsible subject, or
> continued by one that makes it an explicit trigger. This typed
> `WitnessesEntity ← Entity → EngagesEntity` composition is directed from the
> elaborating/continuing specification toward the binding specification and
> recursively composes across different actions. Means and state/scope guard
> incidence remain discovery facts only. Shared words, untyped Entity
> incidence, or object similarity alone never become support.
> Negative, permissive, advisory, and alternative-object claims do not enter
> this realization judgment. Admission creates a candidate, not automatic
> authority. All candidates and relationships remain in the Ledger, and there
> is no manual Specification-to-Specification support-Edge path.

## Architecture

spec-oracle is a Cargo workspace split into crates along a client/daemon seam.
The client and daemon talk **gRPC/protobuf** over a shared generated protocol;
they do not depend on each other.

| Crate        | Kind                 | Role                                                                                     |
| ------------ | -------------------- | ---------------------------------------------------------------------------------------- |
| `so-lang`    | lib                  | The constrained natural-language grammar and its *total* parser. No meaning interpretation or cross-specification reasoning lives here. |
| `so-reason`  | lib                  | Pure derived interpretations and structural reasoning over `so-lang` parse trees: speech acts, formulas, semantic A/G contracts and their formation, operational Behavior/Entity profiles, and conservative judgments. |
| `so-protocol` | lib                 | Generated `spec_oracle.v1` protobuf messages and tonic gRPC stubs only.                  |
| `so-daemon`  | lib + `specd`        | Domain model, evidence capture, persistence, domain/protobuf conversion, and gRPC service. |
| `so-client`  | lib                  | A thin gRPC client; resolves the caller's `@file`/`-`(stdin) input channels.              |
| `so-cli`     | bin `spec`           | The command-line front end over the client.                                              |
| `so-tracing` | lib                  | Shared tracing/OpenTelemetry setup and gRPC trace propagation.                           |
| `ui`         | Next.js app          | Instanced 3D graph visualization (Three.js/WebGL with a `d3-force-3d` Worker). A thin BFF speaks gRPC to `specd`; not a Cargo crate. See [`ui/README.md`](ui/README.md). |

**Acceptance and processing are separate.** The AddNode Command handler in `specd` parses
exactly one sentence and persists exactly one Node, retaining Evidence
descriptors verbatim. A successful save emits an in-process `NodeAdded` event;
registered Event Consumers then capture Evidence, store snapshot blobs, enrich origin, and
derive graph structure. Successful results are appended to Node Meta. The
client only resolves input
*channels* — reading the descriptor from its own files/stdin — and forwards the
specification plus the resolved evidence values. One consequence to keep in mind: **a file locator is
resolved against the daemon's filesystem/git**, so the daemon must run where
the evidence lives (or where a checkout of it is reachable).

```text
spec (CLI) ──▶ so-client ──gRPC──▶ specd Command Bus ──▶ Specification Node
  resolves @file/-/inline              │       AddNode Ack
                                       └─NodeAdded─▶ volatile Event Bus
                                                       ├─ Evidence Consumer
                                                       ├─ origin Consumer
                                                       └─ graph Consumers
```

## The language

`spec add` accepts exactly one constrained-NL sentence and rejects anything
else with a precise syntax or sentence-count error (the parser is *total* —
parseability is a language requirement, not a score). Each sentence performs
one of six speech acts — **definition, description, obligation, prohibition,
recommendation, permission** — under optional circumstance frames
(`Where`/`While`/`When`/`If`), an optional `unless` exception, and an optional
`so that` purpose:

```text
When the order is submitted, the system shall record the total.
```

See [`docs/grammar/`](docs/grammar/) for the full reference; the source of
truth is [`so_lang/src/parse.rs`](so_lang/src/parse.rs) and
[`so_lang/src/ast.rs`](so_lang/src/ast.rs).

## Persistence: one product across the deployment spectrum

Specification nodes live in **ArangoDB** — chosen because a single graph-database
product spans the whole deployment spectrum: it runs on a laptop to start, is
self-hostable on your own infrastructure, and is available as a managed cloud
service. You scale by *relocating* the same product up that spectrum, not by
swapping databases behind an abstraction layer. `compose.yml` is the *local* leg
of that spectrum.

Storage is split by concern (both owned by the daemon):

- **ArangoDB** holds graph topology, node properties, and a content-hash pointer
  per evidence snapshot.
- **A daemon-side, content-addressed blob store** (`./.spec-oracle/blobs/`) holds
  the snapshot *bytes*, keyed by their SHA-256. `Snapshot.content` is
  `#[serde(skip)]`, so bytes never travel into the database — or across the wire
  — only the hash does.

A Command submission receives a random `command_id` for identity and tracing,
but a Specification Node ID is a SHA-256 of its accepted sentence and
language version. Adding the same sentence again therefore returns the existing
Node; any new Evidence descriptors are merged into that Node's retryable input
set. Term, Evidence, Assumption, and Guarantee Nodes are likewise
content-addressed. Edge identity is derived from the complete typed relationship
except its recording time, so an identical Edge is reused even if a producer is
retried or supplies another incidental ID. Content-addressing applies to blobs
independently.

## Volatile Commands and Events

The Command Bus and Event Bus are process-local by design. The standard flow is
Command → handler completion/fresh Event → per-Consumer Delivery.
Each Consumer independently receives its Delivery, submits the next Command,
waits for that Command to complete, and explicitly Acks or Nacks the Delivery.
The Event Bus retains an accepted Event until every Consumer that was subscribed
at acceptance has acknowledged its independent Delivery. It does not start or
invoke Consumers, execute Plugins, submit Commands, interpret processing
results, or access the Ledger.

A Nack schedules bounded-backoff redelivery. An expired lease makes the same
Event and stable Delivery ID available for another attempt; an Ack from an
older attempt cannot complete the newer one. Consumer Commands use an ID
derived from Consumer ID, Event ID, and operation, so redelivery repeats the
same idempotent Command. A Consumer registered later does not receive older
retained Events.

Events are intentionally not replayed after restart: a new daemon starts a new,
empty stream. There is no generic Node-processing Event, startup Reconciler, or
historical Event replay. Graph re-entry is expressed by the concrete
`StartGraphRebuild` and `BeginNodeGraphRebuild` Commands below. A future
Evidence recapture or other lifecycle operation must likewise introduce a
concrete Command/Event pair that names the fact that occurred; it must not
synthesize `NodeAdded` or publish an implementation-level wake-up signal.

Graceful shutdown stops gRPC intake, drains Commands, derived Events, and all
accepted Deliveries. An EventTap separately copies accepted Events into
pluggable best-effort archives. The ArangoDB sink is enabled with the ArangoDB
store; sink failure or a full sink mailbox is observable but never participates
in Consumer Ack or recovery. Ledger Nodes and Edges remain the persistent
authority, not the transient queue or its archive.

Command handlers are the only publishers of processing Events:

| Command | Fresh Event |
| --- | --- |
| `AddNode` | `NodeAdded` |
| `AddEvidenceRelation` | `EvidenceRelationAdded` |
| `ReplaceEvidenceRequests` | `EvidenceRequestsReplaced` |
| `StartGraphRebuild` | `GraphRebuildStarted` |
| `BeginNodeGraphRebuild` | `NodeGraphRebuildStarted` |
| `CompleteGraphRebuildPage` | `GraphRebuildPageCompleted` |
| `DeriveContract` | `ContractDerived` |
| `EstablishOccurrenceReliance` | `OccurrenceRelianceEstablished` |
| `EstablishGuaranteeDischarge` | `GuaranteeDischargeEstablished` |
| `EstablishAdmissibilityEnvelope` | `AdmissibilityEnvelopeEstablished` |
| `AcceptDischargeCandidate` | `DischargeCandidateAccepted` |
| `ProjectNodeTerms` | `NodeTermsProjected` |
| `ProjectNodeContract` | `NodeContractProjected` |
| `CaptureEvidence` | `EvidenceCaptured` when capture applies |
| `PinGithubEvidenceToCommit` | `GithubEvidencePinnedToCommit` when pinning applies |
| `AssessNodeSemanticRelations` | `NodeSemanticRelationAssessmentCompleted` |
| `AssessNodeContractRelations` | `NodeContractRelationAssessmentCompleted` |
| `AssessNodeDischargeCandidates` | `NodeDischargeCandidateAssessmentCompleted` |

The 18 concrete Command kinds therefore map to 18 distinct concrete Event
kinds. Concrete Events are never rounded into names such as `ContractChanged`,
`EdgeAdded`, or `RelationAssessed`. Subscriptions may additionally select the
abstract categories `DomainEvent`, `GraphEvent`, `NodeEvent`, `EvidenceEvent`,
`ContractEvent`, `RelationEvent`, `ProjectionEvent`, and `AssessmentEvent`. A
category match delivers the original concrete Event once; it does not emit
another abstract Event. One concrete kind may belong to several categories.

The built-in Consumer subscriptions are:

| Consumer | Events received | Command submitted |
| --- | --- | --- |
| `graph-rebuild` | `GraphRebuildStarted`, `GraphRebuildPageCompleted` | bounded `BeginNodeGraphRebuild` Commands, then `CompleteGraphRebuildPage` |
| `term-projection` | `NodeAdded`, `NodeGraphRebuildStarted` | `ProjectNodeTerms` |
| `contract-projection` | `NodeAdded`, `NodeGraphRebuildStarted` | `ProjectNodeContract` |
| `evidence-capture` | `NodeAdded`, `EvidenceRequestsReplaced` | `CaptureEvidence` |
| `github-evidence` | `NodeAdded`, `EvidenceRequestsReplaced` | `PinGithubEvidenceToCommit` |
| `semantic-relation` | `NodeTermsProjected` | `AssessNodeSemanticRelations` |
| `contract-relation` | `NodeContractProjected`, the three established A/G relation Events, `DischargeCandidateAccepted` | `AssessNodeContractRelations` |
| `discharge-candidate` | contract projection, established A/G and selection facts, completed semantic/contract assessments | `AssessNodeDischargeCandidates` |

## Quickstart

Prerequisites: Rust (stable), a `protoc` on `PATH` (for the build-time protobuf
codegen), and Docker with the Compose v2 plugin.

```sh
# 1. Set the local ArangoDB password (one secret, feeds both DB and daemon).
cp .env.example .env          # then edit ARANGODB_PASSWORD

# 2. Start ArangoDB (published on http://localhost:8529).
docker compose up -d
docker compose ps             # wait until arangodb is "healthy"

# 3. Export the password for the daemon, which runs on the host.
#    This also exports the local OpenTelemetry defaults from .env.example.
set -a; . ./.env; set +a

# 4. Start the daemon. Evidence Consumers resolve files against its working
#    directory, so run it from the repo root. Listens on 127.0.0.1:50051.
cargo run --bin specd

# 5. In another shell, add your first specification. The Node is accepted first;
#    its Evidence Consumer then captures and hashes the file region.
cargo run --bin spec -- add \
  "When evidence is captured, the system shall record its content hash." \
  --evidence so_daemon/src/snapshot.rs:1
```

The `spec_oracle` database and its `nodes`, `term_nodes`, `derived_nodes`,
`edges`, and `relation_assessments` collections are created automatically by the daemon on
first connect — there is no init step in compose.

Reset everything (drops the database volume) with `docker compose down -v`. The
daemon-side blob store under `./.spec-oracle/` is separate and is removed by
deleting that directory.

### Reading the graph

`spec graph show` renders the one specification graph in the terminal. With no
required selector or starting Node, it reads the whole candidate population
under the current derivation policies and draws its Node/Edge topology directly
in the terminal:

```sh
# Read and draw the whole specification graph.
cargo run --bin spec -- graph show

# Set the terminal drawing width without changing the selected graph.
cargo run --bin spec -- graph show --width 160

# Draw the current-set projection: selected specifications and only the current
# relationships and projections that remain attached to them.
cargo run --bin spec -- graph show --current --width 160

# Audit every immutable Edge version; current derivations stay marked and
# historical derivations are dimmed. This includes the provisional ⊤
# projection after pairing.
cargo run --bin spec -- graph show --ledger --width 160
```

The daemon still returns bounded keyset pages because transport must remain
bounded. The CLI follows those pages to the end, combines their Specification
Nodes, connector and projection Nodes, and Edges, and then lays out that one graph. Refinement
and term mentions are directed by their explicit endpoint roles; equivalence
and conflicts are symmetric. Selection-family relationships retain their own
supporter/defeater/superseder roles rather than reversing semantic Edges.
Assume-guarantee Edges retain three separately visible facts: the arrow's
source is the evidence-bearing sentence, its target owns the conditioned
guarantee, and the `Pairing reliances` list names the authored specification
whose assertion is actually awaited. The target's current `has_assumption`
projection points at the resulting content-addressed Assumption Node; after a
successful pairing it is the relied authored text (or conjunction), not `⊤`.
Current specifications use `◆`; candidates outside the current set use `◇`. A
semantic Edge is owned by its lexically smaller endpoint for pagination, so it
may arrive before its other endpoint and is rendered after the complete walk.
Paging is an implementation detail of the read; it does not select a finite
subgraph. `spec graph show` uses the current derivation view across the candidate
population; `--current` renders its selected induced graph. `--ledger` instead
walks the separate Edge-id-keyset Ledger API and renders every recorded Edge
version. The Ledger header reports current and recorded Edge counts, and
historical edges are dimmed, so persistence history is visible without being
mistaken for the current specification graph. Future graph filters belong to
optional flags rather than required seeds. `--server` selects the daemon and
`--width` changes presentation only.

### Rebuilding graph derivations

`spec graph rebuild` asynchronously reapplies the installed graph derivations
to every authored Node currently visible to the daemon:

```sh
spec graph rebuild
spec graph rebuild --json
```

The Command Handler emits `GraphRebuildStarted`. The `graph-rebuild` Consumer
walks Nodes in bounded keyset pages and submits one idempotent
`BeginNodeGraphRebuild` Command per Node. That Command records the rebuild
entry on the Node and emits the concrete `NodeGraphRebuildStarted` fact;
ordinary graph Consumers receive it alongside `NodeAdded` and submit their
normal projection Commands. Evidence Consumers do not receive it, so rebuilding
the graph never repeats external Evidence capture.

Each bounded scan page ends with
`CompleteGraphRebuildPage → GraphRebuildPageCompleted`; the next page is
therefore another Event Delivery rather than one unbounded Consumer lease.
The rebuild is volatile across daemon restart, like every other Command/Event
chain. It does not replay `NodeAdded` and has no historical Event dependency.

Ledger Edges are never deleted. Reapplying an unchanged derivation is
idempotent, a changed derivation version appends new history and recedes the old
version from the current view, and a newly installed derivation appends the
Edges that older Nodes did not previously have. Thus “rebuild” replaces the
current derived graph semantically while preserving its audit history.

### Viewing the current specification set

The current-set projection is automatic, versioned and auditable. Under
`selection/fitness-v15`, every specification starts as an unselected candidate.
Typed `GroundedBy` Evidence supplies bounded, time-decaying external points.
Manual `EvidenceAffirms` and `EvidenceDenies` Edges supply the same bounded
external points with explicit polarity. An Evidence judgment may target another
Evidence Node: each denial flips the sign of the downstream path, so newer
Evidence can cancel obsolete or mistaken Evidence without deleting it. Cycles
remain finite and deterministic because the policy retains one shortest path
per Evidence and polarity; effective paths accompany their score contribution.
Independently, proved logical paths and derived realization paths recursively
supply structural points. A realization path starts from an explicit means
written in an upper-layer binding specification and discovers the compatible
lower-layer behavior that implements it. The view may then extend the path
toward more concrete behaviors through actor-domain and object refinement.
It may also compose an affirmative binding object with specifications that
govern the exact same Entity as their subject or react to it as a trigger.
Subject/trigger roles make this a constitutive path rather than lexical
similarity; Means and state/scope guards do not establish it. These judgments
use the persisted operational projection but are not persisted as manual or
synthetic support Edges. Shared words, Terms, untyped Entity incidence, and
unanchored object similarity alone never become support.

Population retrieval follows operational roles only in the inbound support
direction: from a binding object's witness to subject/trigger engagements that
can support it. It does not walk back from an engagement to specifications
that witness the same Entity, and it does not expand through Means or guard
incidence. Same-action Behaviors enter the closure only after `so-reason`
recognizes a layered-realization candidate. This preserves complete recursive
support without loading an undirected Entity component for each requested
view.

Contract support is evaluated directly over the persisted Contract/Proof
subgraph as a least fixed point. A current `HasContract` projection is a root;
each refinement is an alternative proof (OR), while all operand Edges belonging
to one content-addressed composition, quotient, or merge derivation are jointly
required (AND). Different derivation bases that happen to produce the same
Contract remain separate alternatives. The evaluator has no candidate-count,
proof-count, recursion-depth, iteration-count, or conflict-component cutoff.
Storage and RPC page sizes only batch a complete cursor traversal and therefore
do not change the resulting specification graph.

Mechanically proved conflicts subtract pressure, while equivalence and the
maximum-weight consistency selection explain why a viable candidate recedes;
no manually asserted selection relation participates. Every effective or
capped contribution and every exclusion is returned in the graph view. The
selected set itself is a usable output rather than a display-only flag:

```sh
# The selected specification set as a relationship-preserving graph.
spec graph show --current
```

`spec graph show --current` walks the daemon's bounded pages and rejects a changing
or incomplete walk instead of silently rendering a partial set. The UI Current-set
panel reports selected/loaded candidates, candidates without direct Evidence,
net Counter Evidence, and any selected conflict Edge. These diagnostics show
where further accumulation or newly derived relationships can change the
selected specification graph; they are not a completeness percentage for the
unreachable conceptual whole.

### Pairing assume-guarantee contracts

The domain service can append a non-trivial contract relation between existing
authored Specification Nodes. The explicit relied Node is not incidental basis:
its parsed assertion is exactly the formula conjoined into the target's
assumption. The source is separately checked as evidence for that formula.

The daemon accepts an assumption-side Edge only when `so-reason` proves
source ⇒ relied (`Yes`, never `Unknown`), the speech act/force is admissible,
the explicit source/target component direction passes the responsible-subject
guard, the aggregate assumption is not refuted as unsatisfiable, and its
permissions are not refuted as envelope-incompatible. A recommendation never
relieves a guarantee. An admissibility envelope remains compatibility data and
never becomes an assumption conjunct. Repeating a valid request is idempotent;
adding an aggregate that would be contradictory is rejected without deleting
the already accepted Ledger fact.

The graph read selects the aggregate paired Assumption for the target and
suppresses its provisional ingest `⊤` projection from the current view. Both
projections remain immutable Ledger history. The guarantee projection is
unchanged: pairing conditions what is owed; it does not rewrite the authored
guarantee.

A proved `G_source ⇒ A_target` opportunity is first stored as a
`DischargeCandidate` Assessment, not an Edge. It becomes the existing
`GuaranteeDischarge` relation only through explicit acceptance, which runs the
complete pairing validation again. Contract refinement/equivalence and
composition/quotient/merge operate over saturated A/G contracts.

### Graph view (`ui/`)

A Next.js app visualizes the graph as a force-directed 3D cloud (instanced
Three.js/WebGL with a `d3-force-3d` Worker), coloring authored nodes by speech
act and derived nodes by kind. It is an independent graph
view and is not launched or controlled by `spec graph show`. It pages in bounded
batches and caps what it renders. Its **Ledger** tab lazily walks the same
bounded historical Edge API: current derivations retain their relation colors while
superseded derivations and projections are dimmed and identified as `Ledger
history` in the relation panel; the panel labels the bright state `Current
derivation`, distinct from membership in the Current specification graph. A
thin Next.js backend-for-frontend speaks
gRPC to `specd`, so the browser never needs gRPC.

```sh
cd ui
cp .env.local.example .env.local     # SPEC_ORACLE_GRPC_ADDR → specd (default 127.0.0.1:50051)
npm install
npm run dev                          # http://localhost:3000
```

See [`ui/README.md`](ui/README.md) for details.

### Evidence

`--evidence` is repeatable. Each value is either:

- a **bare locator string** — recorded with kind `unknown` ("here is grounding,
  I am not classifying it now"); or
- a **JSON object** (or array) with `kind` and `locator`, plus optional `origin`.

A locator is an `http(s)://` URL (fetched and snapshotted) or a filesystem path
with an optional `:line[:col]` suffix (the cited region, with context, is
captured and hashed). The referenced file or URL is resolved **in the daemon**
by the asynchronous Evidence Consumer. An unreadable locator does not roll back the
accepted specification; the Delivery remains retryable.

Prefix a value with `@` to read the evidence *descriptor* from a file, or use `-`
to read it from stdin. These channels are resolved on the **client** (they name
the client's own streams); the resulting text is persisted verbatim on the
Node, then interpreted and captured by the daemon's Evidence Consumer. A successful
capture also creates or reuses a content-addressed Evidence Node and connects it
with a `grounded_by` projection Edge.

Manual Evidence judgments capture a new descriptor or reuse an existing
`evidence-…` id. The target may be a Specification or another Evidence Node;
there is intentionally no corresponding generic Edge command:

```sh
# New Evidence affirms a specification.
spec evidence add \
  '{"kind":"testimonial","locator":"docs/releases/2026-07.md"}' \
  --affirms spec-0123

# A correction denies an older Evidence Node.
spec evidence add docs/releases/correction.md \
  --denies evidence-0456
```

`spec evidence graph QUERY` executes a read-only
[openCypher](https://opencypher.org/) path query over the Evidence property-graph
scope and renders the exact union of the returned paths. It does not perform
text search and does not add incident neighbors that were not selected by the
query.

```sh
# Every manual relationship between two Evidence Nodes.
spec evidence graph \
  'MATCH p=(a:Evidence)-[:EVIDENCE_AFFIRMS|EVIDENCE_DENIES]->(b:Evidence) RETURN p'

# A correction that denies old Evidence which affirmed a Specification.
spec evidence graph \
  "MATCH p=(new:Evidence)-[:EVIDENCE_DENIES]->(old:Evidence)-[:EVIDENCE_AFFIRMS]->(s:Specification) WHERE new.kind = 'testimonial' RETURN p"

# Select one Evidence neighborhood by stable identity.
spec evidence graph \
  "MATCH p=(e:Evidence)-[r]-(target) WHERE e.id = 'evidence-0456' RETURN p" \
  --json
```

The Evidence scope exposes these property-graph names:

| Element | openCypher name | Queryable properties |
|---|---|---|
| Node | `Evidence` | `id`, `kind`, `locator`, `hash`, `bytes`, `captured_at`, `author` |
| Node | `Specification` | `id`, `statement`, `lang_version`, `created_at` |
| Relationship | `GROUNDED_BY` | `id`, `kind`, `recorded_at`, `source`, `target` |
| Relationship | `EVIDENCE_AFFIRMS` | `id`, `kind`, `recorded_at`, `source`, `target` |
| Relationship | `EVIDENCE_DENIES` | `id`, `kind`, `recorded_at`, `source`, `target` |

The shared graph-query layer supports one named path in `MATCH`, node labels,
relationship types (including `|` alternatives), incoming/outgoing/undirected
relationships, multiple explicit hops, inline literal property maps, `WHERE`
comparisons with `AND`/`OR`, `CONTAINS`, `STARTS WITH`, `ENDS WITH`, `RETURN`
of that path, and `LIMIT`. Mutation clauses, arbitrary expressions,
variable-length paths, multiple path patterns, and returning scalars are
rejected. This bounded read-only subset is deliberately storage-independent so
the same parser and evaluator can be reused by `spec graph` views without
exposing ArangoDB AQL.

`kind` records the *epistemic kind* of the grounding, one of: `constitutive`,
`demonstrative`, `testimonial`, `assertoric`, `circumstantial`, `counter`,
`unknown`.

```sh
cargo run --bin spec -- add "The pump shall stop." \
  --evidence '{"kind":"assertoric","locator":"so_lang/src/parse.rs:1"}'
```

## Configuration

Credentials are read from the **environment only**, never from the command line,
so they do not leak into shell history or the process table.

### Daemon (`specd`)

| Variable            | Flag            | Default                  | Purpose                                             |
| ------------------- | --------------- | ------------------------ | --------------------------------------------------- |
| `SPEC_ORACLE_LISTEN`| `--listen`      | `127.0.0.1:50051`        | gRPC listen address.                                |
| `SPEC_ORACLE_DIR`   | `--dir`         | *(current directory)*    | Base dir whose `.spec-oracle/blobs/` holds the bytes. |
| `SPEC_ORACLE_STORE` | `--store`       | `arango`                 | Node-store backend: `arango` (persistent) or `memory` (non-persistent, no DB required). |
| `ARANGODB_URL`      | `--arango-url`  | `http://localhost:8529`  | Where ArangoDB currently lives (ignored with `--store memory`). |
| `ARANGODB_DB`       | `--arango-db`   | `spec_oracle`            | Database name (auto-created).                        |
| `ARANGODB_USER`     | *(env only)*    | `root`                   | Authenticating user.                                 |
| `ARANGODB_PASSWORD` | *(env only)*    | *(empty)*                | Password. Must match the container's root password.  |
| `GITHUB_TOKEN`      | *(env only)*    | *(unset)*                | Optional bearer token for GitHub Evidence Consumers.  |

The store backend is **selectable**: `--store arango` (default) persists to
ArangoDB, while `--store memory` runs a first-class in-memory backend with no
database — handy for local development, demos, and driving the graph UI without
standing up ArangoDB (its data is lost on restart). Both implement the same
`GraphStore` seam, so the service behaves identically.

### CLI (`spec`)

| Variable             | Flag        | Default                   | Purpose                          |
| -------------------- | ----------- | ------------------------- | -------------------------------- |
| `SPEC_ORACLE_SERVER` | `--server`  | `http://127.0.0.1:50051`  | Address of the `specd` daemon. |

Exit codes (`spec`): `0` success; `2` bad input (grammar or evidence syntax the
user can fix by rewording, or a channel that could not be read); `1` runtime
failure (connection, evidence capture, or store).

### OpenTelemetry

Both binaries initialize OpenTelemetry tracing. `spec` and `specd` use
stable default service names in code, and export OTLP/HTTP traces to the shared
local stack when the `.env` defaults are loaded:

| Variable | Default in `.env.example` | Purpose |
| -------- | ------------------------- | ------- |
| `OTEL_EXPORTER_OTLP_ENDPOINT` | `http://192.168.10.4:4318` | Shared OTLP/HTTP ingest endpoint. |
| `OTEL_EXPORTER_OTLP_PROTOCOL` | `http/protobuf` | OTLP HTTP protobuf transport. |
| `OTEL_TRACES_EXPORTER` | `otlp` | Trace exporter selection. Set `none` to disable traces. |
| `OTEL_PROPAGATORS` | `tracecontext,baggage` | Context propagation across gRPC metadata. |
| `OTEL_RESOURCE_ATTRIBUTES` | `deployment.environment=dev,service.namespace=spec-oracle` | Stable resource labels. |
| `SPEC_ORACLE_TELEMETRY_CAPTURE` | `content` | spec-oracle domain attribute capture policy for local development. |

The binaries set `service.name=spec` and `service.name=specd` unless
`OTEL_SERVICE_NAME` or `service.name` in `OTEL_RESOURCE_ATTRIBUTES` overrides
them. Set `OTEL_SDK_DISABLED=true` to disable all OTel initialization.

`SPEC_ORACLE_TELEMETRY_CAPTURE` is intentionally a policy, not a list of every
attribute. Unset code defaults to `ops`; `.env.example` opts into `content` for
local development.

| Policy | Captures |
| ------ | -------- |
| `ops` | Operational shape: span names, durations, counts, stages, broad error category. |
| `diagnostic` | `ops` plus parse/error kinds and stable hashes for grouping failures. |
| `content` | `diagnostic` plus raw statements and content-bearing values needed to improve spec-oracle locally. |

For a `spec add` parse failure, `ops` records that specification parsing
failed; `diagnostic` also records fields such as `spec.parse.error.kind` and
`spec.specification.hash`; `content` additionally records `spec.specification.text`
and the detailed error message.

Local verification against the shared stack:

```sh
python3 ~/.agents/skills/otel-observe-api/scripts/grafana_query.py health
python3 ~/.agents/skills/otel-observe-api/scripts/grafana_query.py datasources

# After running one `spec add` request:
python3 ~/.agents/skills/otel-observe-api/scripts/grafana_query.py \
  tempo-search --tags 'service.name=specd' --limit 20
python3 ~/.agents/skills/otel-observe-api/scripts/grafana_query.py \
  tempo-search --tags 'service.name=spec' --limit 20
```

## Extending: origin enrichers

When evidence is ingested, the daemon enriches its **source provenance** (author
and first/last change dates) best-effort. This is an open extension seam: an
external crate contributes an enricher without editing this crate.

1. Implement the `OriginEnricher` trait (`handles(&Locator)` + `discover(…)`).
2. Register it at link time. Submit through the daemon crate's re-exported
   [`inventory`] (`so_daemon::inventory`), so your crate needs no
   `inventory` dependency of its own — and can't accidentally submit into a
   version-mismatched registry:

```rust
use so_daemon::origin::{EnricherRegistration, OriginEnricher};

struct IssueTrackerEnricher;
impl OriginEnricher for IssueTrackerEnricher { /* … */ }
fn make() -> Box<dyn OriginEnricher> { Box::new(IssueTrackerEnricher) }

so_daemon::inventory::submit! {
    EnricherRegistration::new("issue-tracker", 10, make)
}
```

`origin::registered_enrichers()` — which `spec add` calls — collects
the built-ins (`git`, `web`) plus every submitted registration. Order is
deterministic: **descending `priority`, then ascending `name`**, independent of
link order (as long as names are distinct, which they should be). Among enrichers
that `handles()` the same locator the highest-priority one wins (first-match, not
merge). The built-ins sit at `priority 0`: use a **positive** priority to override
them, a **negative** one to defer to them. At equal priority the name tie-break
decides, so a `priority 0` plugin whose name sorts before `git`/`web` would also
win — set the priority explicitly rather than relying on the name. For the linker
to keep a plugin crate's submissions, reference that crate at least once from the
binary (e.g. an `extern crate`/`use`).

[`inventory`]: https://docs.rs/inventory

## Extending: Event Consumers

An Event Consumer is an independently running receive loop, not a callback
owned by the Event Bus. It registers a stable Consumer ID and the Event kinds
it needs, receives leased Deliveries, and explicitly Acks only after its work
has completed. Domain work normally enters the Command Bus; the Command handler
owns persistence and publication of any fresh Event.

Plugins use this same interface as one possible kind of Consumer. There is no
Plugin-specific queue, retry loop, completion value, or Event publication
path. The daemon's built-in Evidence and graph processors are ordinary
Consumers wired by `consumer::built_in_consumers`.

```rust
use so_daemon::event_bus::{EventBus, EventBusError, EventKind, Subscription};

async fn consume(events: EventBus) -> Result<(), EventBusError> {
    events
        .register(Subscription::new(
            "tracker",
            [EventKind::NodeAdded],
            1,
        ))
        .await?;

    loop {
        let delivery = events.receive("tracker").await?;

        // Submit an idempotent Command derived from delivery.event.id and wait
        // for its handler to finish before acknowledging this attempt.
        process_with_a_command(&delivery.event).await;

        events.ack(&delivery).await?;
    }
}
```

Consumers can execute more than once, so their Commands and any external
effects must be idempotent. The built-in `github-evidence` Consumer handles
`https://github.com/OWNER/REPO/...` evidence: it resolves the commit through the
GitHub REST API and, for `/blob/REF/PATH`, captures the commit-fixed raw file in
the BlobStore before recording its hash and commit metadata on the Node.

## Operational notes

- **The root password is applied only on first init.** The ArangoDB entrypoint
  sets the root password from `ARANGO_ROOT_PASSWORD` (which compose maps from
  your `.env` `ARANGODB_PASSWORD`) *once*, when the data volume is first created.
  Changing it later has no effect until the volume is removed (`docker compose
  down -v`) or you rotate the password via `arangosh`/HTTP. This is why the two
  sides — container and daemon — share one value in `.env`.

- **Community Edition has a 100 GiB dataset cap** (enforced from ArangoDB 3.12.5:
  warnings for two days, then read-only, then shutdown). It is not a paywalled
  binary — the same server runs above that size once you relocate to a licensed
  tier — but it bounds the *local* leg. CE may not be used commercially.
