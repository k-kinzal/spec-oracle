# spec-oracle

An **assume-guarantee (AG) contract** specification graph, ingested from
constrained natural language.

Each specification statement is written in an EARS-derived controlled language
and projected — deterministically, with no inference and no human-in-the-loop
review — into an AG contract: a leading condition becomes the **assumption**,
the `<subject> <shall|must|should> <response>` clause becomes the **guarantee**. Every
node is also a *grounded* claim: it carries the evidence it was ingested from,
captured at ingest time.

> **Scope.** Today the tool does exactly one thing: `spec add` — recognize a
> statement, capture its evidence, and persist a contract node. Edges
> (refinement, composition, conjunction, quotient), strength, the authority/trust
> registry, and classify/review are deliberately out of scope for now.

## Architecture

spec-oracle is a Cargo workspace split into crates along a client/daemon seam.
The client and daemon talk **gRPC/protobuf** over a shared generated protocol;
they do not depend on each other.

| Crate        | Kind                 | Role                                                                                     |
| ------------ | -------------------- | ---------------------------------------------------------------------------------------- |
| `so-lang`    | lib                  | The EARS-derived grammar: a *total* recognizer projecting a statement into a contract.    |
| `so-protocol` | lib                 | Generated `spec_oracle.v1` protobuf messages and tonic gRPC stubs only.                  |
| `so-daemon`  | lib + `specd`        | Domain model, evidence capture, persistence, domain/protobuf conversion, and gRPC service. |
| `so-client`  | lib                  | A thin gRPC client; resolves the caller's `@file`/`-`(stdin) input channels.              |
| `so-cli`     | bin `spec`           | The command-line front end over the client.                                              |
| `so-tracing` | lib                  | Shared tracing/OpenTelemetry setup and gRPC trace propagation.                           |

**Capture happens in the daemon.** `specd` parses the
statement, snapshots what each locator points at, discovers source provenance,
and persists the node. The client only resolves input *channels* — reading the
descriptor from its own files/stdin — and forwards the statement plus the
resolved evidence values. One consequence to keep in mind: **a file locator is
resolved against the daemon's filesystem/git**, so the daemon must run where
the evidence lives (or where a checkout of it is reachable).

```text
spec (CLI) ──▶ so-client ──gRPC──▶ specd ──▶ ArangoDB + blob store
  resolves @file/-/inline                     captures, enriches, persists
```

## The grammar

`spec add` accepts an EARS statement in one of three forms and rejects anything
else with a precise syntax error (the recognizer is *total* — parseability is a
language requirement, not a score):

```text
Ubiquitous:   <subject> <shall|must|should> <response>.
Conditional:  <While|When|If|Where> <condition>, [then] <subject> <shall|must|should> <response>.
Complex:      <kw> <c1>, <kw> <c2>, ... <subject> <shall|must|should> <response>.
```

See [`docs/grammar/`](docs/grammar/) for the full reference; the single source
of truth is [`so_lang/src/grammar.rs`](so_lang/src/grammar.rs).

## Persistence: one product across the deployment spectrum

Contract nodes live in **ArangoDB** — chosen because a single graph-database
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

A node's identity is a random UUID: adding the *same* statement twice yields two
distinct nodes. Content-addressing applies to blobs only.

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

# 4. Start the ingest daemon. It captures evidence against its own working
#    directory, so run it from the repo root. Listens on 127.0.0.1:50051.
cargo run --bin specd

# 5. In another shell, add your first contract (evidence must point at something
#    the daemon can read — a file region here is captured and hashed at ingest).
cargo run --bin spec -- add \
  "When evidence is captured, the system shall record its content hash." \
  --evidence so_daemon/src/snapshot.rs:1
```

The `spec_oracle` database and the `contracts` collection are created
automatically by the daemon on first connect — there is no init step in compose.

Reset everything (drops the database volume) with `docker compose down -v`. The
daemon-side blob store under `./.spec-oracle/` is separate and is removed by
deleting that directory.

### Evidence

`--evidence` is repeatable. Each value is either:

- a **bare locator string** — recorded with kind `unknown` ("here is grounding,
  I am not classifying it now"); or
- a **JSON object** (or array) with `kind` and `locator`, plus optional `origin`.

A locator is an `http(s)://` URL (fetched and snapshotted) or a filesystem path
with an optional `:line[:col]` suffix (the cited region, with context, is
captured and hashed). The referenced file or URL must resolve **in the daemon** —
an unreadable locator fails the ingest.

Prefix a value with `@` to read the evidence *descriptor* from a file, or use `-`
to read it from stdin. These channels are resolved on the **client** (they name
the client's own streams); the resulting text is then interpreted and the locator
it names is captured by the daemon.

`kind` records the *epistemic kind* of the grounding, one of: `constitutive`,
`demonstrative`, `testimonial`, `assertoric`, `circumstantial`, `counter`,
`unknown`.

```sh
cargo run --bin spec -- add "The pump shall stop." \
  --evidence '{"kind":"assertoric","locator":"so_lang/src/grammar.rs:12"}'
```

## Configuration

Credentials are read from the **environment only**, never from the command line,
so they do not leak into shell history or the process table.

### Daemon (`specd`)

| Variable            | Flag            | Default                  | Purpose                                             |
| ------------------- | --------------- | ------------------------ | --------------------------------------------------- |
| `SPEC_ORACLE_LISTEN`| `--listen`      | `127.0.0.1:50051`        | gRPC listen address.                                |
| `SPEC_ORACLE_DIR`   | `--dir`         | *(current directory)*    | Base dir whose `.spec-oracle/blobs/` holds the bytes. |
| `ARANGODB_URL`      | `--arango-url`  | `http://localhost:8529`  | Where ArangoDB currently lives.                     |
| `ARANGODB_DB`       | `--arango-db`   | `spec_oracle`            | Database name (auto-created).                        |
| `ARANGODB_USER`     | *(env only)*    | `root`                   | Authenticating user.                                 |
| `ARANGODB_PASSWORD` | *(env only)*    | *(empty)*                | Password. Must match the container's root password.  |

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
| `diagnostic` | `ops` plus parse/error kinds, expected grammar form, and stable hashes for grouping failures. |
| `content` | `diagnostic` plus raw statements and content-bearing values needed to improve spec-oracle locally. |

For a `spec add` parse failure, `ops` records that statement parsing failed;
`diagnostic` also records fields such as `spec.parse.error.kind`,
`spec.parse.expected_form`, and `spec.statement.hash`; `content` additionally
records `spec.statement.text` and the detailed error message.

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

`origin::registered_enrichers()` — which the `spec add` pipeline calls — collects
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
