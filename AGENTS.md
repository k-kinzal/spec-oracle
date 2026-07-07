# AGENTS

## Engineering Rules

### Current crate layout

The workspace is split by ownership boundary:

- `so-lang`: the constrained specification language. It is pure and I/O-free;
  it parses a specification into its sentence structure — speech-act cores,
  circumstance frames, a phrase grammar — or returns a precise syntax error,
  and derives the semantic interpretations (speech acts, assertions, the
  assume-guarantee ingest projection) over that structure.
- `so-protocol`: generated `spec_oracle.v1` protobuf messages and tonic gRPC
  stubs only. Do not put domain types, storage models, business logic, or manual
  conversion logic here.
- `so-daemon`: the daemon-owned domain model, protobuf/domain conversion,
  evidence parsing, snapshot/origin capture, persistence, and the gRPC service.
  The daemon binary is `specd`.
- `so-client`: the thin gRPC client. It resolves client-side input channels such
  as `@file` and `-`, then talks to `so-protocol`; it must not depend on
  `so-daemon`.
- `so-cli`: the `spec` command-line frontend over `so-client`.
- `so-tracing`: shared tracing/OpenTelemetry initialization, propagation, and
  spec-oracle telemetry capture policy helpers.

The domain model belongs to `so-daemon`. The protocol crate is a wire boundary,
not a shared domain crate.

### Required health

Keep the repository in a state where all checks pass:

```sh
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo build --release --workspace
```

Run them before considering changes complete. The release build is required so
the `spec` and `specd` commands on `PATH` reflect the current workspace. If a
check cannot be run because of an environment issue, make that explicit and
leave the code in the best verified state possible.

### Running daemon

`specd` should always be the latest release-built code while working locally.
After any change that can affect daemon behavior, its dependencies, generated
protocol, or tracing, run the release build and restart the running daemon so
the active process matches the workspace.
If `specd` is not running and the task expects local verification through the
daemon, start it. If it cannot be restarted because required local services or
environment variables are unavailable, report that directly.

### OpenTelemetry

`spec` and `specd` work in this repository must be traceable through the shared
local OTel stack. Do not treat telemetry as optional during local verification.

Use these defaults unless the user explicitly asks for a different endpoint or
capture policy:

```sh
OTEL_EXPORTER_OTLP_ENDPOINT=http://192.168.10.4:4318
OTEL_EXPORTER_OTLP_PROTOCOL=http/protobuf
OTEL_TRACES_EXPORTER=otlp
OTEL_PROPAGATORS=tracecontext,baggage
OTEL_RESOURCE_ATTRIBUTES=deployment.environment=dev,service.namespace=spec-oracle
SPEC_ORACLE_TELEMETRY_CAPTURE=content
```

After a local `spec add` verification, confirm that traces are queryable via
Tempo for both `service.name=spec` and `service.name=specd`, and that the trace
connects CLI/client spans to daemon spans. If trace data is missing, treat that
as a verification failure to investigate, not as an acceptable blind spot.

## Vision

We are aiming at a world in which a system's specification can be trusted.

A specification you rely on the way you rely on its types or its tests — checked,
not merely read; live and load-bearing; always describing the system as it stands
right now, never a version of it that no longer exists. When you set out to build
something, you can ask whether it is consistent with everything the system has
already asserted about itself, and get an answer.

A specification set in which many statements coexist without contradiction and
without excess or gap — nothing in conflict, nothing missing, nothing redundant.

And a specification in which the root underneath the whole — the intent every
part of the system implicitly serves — is visible: not decreed from the top by
one person, but made legible from the bottom by the accumulated whole. We want to
see the shape of what we are really building.

## Thought

**Assume-guarantee contracts are the foundation.** Every behavioral
statement — one that obliges, forbids, recommends, permits, or describes —
denotes one assertion: a single property of system behavior; a definitional
statement contributes vocabulary rather than behavior. A statement's leading
conditions — scope, state, trigger — are the internal temporal structure of
its assertion, not a contract split. Assumption
and guarantee are the roles an assertion plays relative to a responsible
subject: a statement whose subject is the component itself is a guarantee of
that component's contract; a statement constraining the component's
environment becomes an assumption when paired with a guarantee that relies on
it. A contract is such a pairing — a guarantee read under its assumptions, and
relieved where they are violated — and a statement taken alone is a guarantee
under the trivial assumption, except a permission: a permission admits
behavior rather than constraining it, so it enters a contract only through
pairing, on the environment side. The specification set as a whole is the
conjunction of these contracts. This is the single lens through which every
statement is understood, and it is what gives words like *refine*, *compose*,
and *contradict* a precise meaning rather than a rhetorical one.

**A specification is formal, and it stays in the words it was written in.**
People state what a system must do in words, and those words carry context that
a symbolic formalization would strip away — context that is itself information.
So instead of translating the words into logic, we make the words themselves
formal: an EARS-derived grammar constrains the language until every statement
has exactly one unambiguous, machine-checkable meaning. The result is a formal
specification whose medium is constrained natural language — not a
natural-language document read loosely, and not a symbolic notation that has
discarded the words. The constraint removes ambiguity; it is not there to limit
what can be said. Expressiveness is what lets the specification carry the
system, so the language is meant to be as expressive as real specifications
demand and to grow as they do — keeping it small is not a goal, and a language
too thin to state the specification would defeat the Vision it serves. Because
its surface stays in words, the specification remains open to linguistic and
natural-language methods, and whatever structure we later derive is derived over
the words themselves.

**Meaning is relational, so it takes volume.** A statement's force is not
contained within it. Each statement is a node, and the relationships between
them — one refining another, two composing, two in contradiction — can carry
more than the statements do alone, turning a flat list of sentences into a
structure whose shape can be examined. The value is therefore not in any single
statement but in the mass of them: only from a collection large and dense enough
do the edges become drawable, showing which statements refine which, which stand
in tension, and where coverage is thin. What accumulates this way is a living
set — one that tracks the system as it changes instead of drifting behind the
moment it was written.

**The root is discovered from the many, not decreed from the top.** The usual
direction is top-down: a person writes the authoritative specification, and
code, tests, and types are derived beneath it. Here the direction runs the
other way. The specification that all the concrete statements implicitly
serve is written down nowhere; it is reconstructed by relating them, and that
living set is the progressively sharpening approximation of it. Mapping back
from the many to the one — reconstructing the root from below rather than
imposing it from above — is the point.

**This is possible now because the cost of volume has collapsed.** Leaning on
*constraint* and *volume* together has always been the obvious idea and always
been impractical. Collecting specifications at scale, grounding each one in
evidence, and normalizing them into a common form was human labor no one could
afford, so the payoff never arrived. Large language models change the
arithmetic: the collection, grounding, and normalization that used to be
prohibitive can now be defaulted on rather than paid for. Once volume is no
longer the binding constraint, an approach that depends on it becomes available
for the first time.

**The method is the open question — where we dig deepest, not where we leave
things thin.** How the graph gets its structure is genuinely not yet known, and
that is the point: there is a direction but not yet an answer, so this is the
part to be pressed on and sharpened — never the part left vague because it is
hard. The direction is to derive two things from the words: **node
meta-information** — clustering, labeling, part-of-speech decomposition of the
constrained language, whatever lets a node be understood in relation to its
neighbors — and **means of generating edges** — partial use of SMT and other
formal methods, language-level modeling aimed at detecting when two
specifications conflict. Managed through a graph view, these are what make a
collection of sentences into a specification that can be reasoned about. None of
this is settled; what is settled is only the direction — words at volume,
structure derived over them, and a specification that stays alive. And unlike
the others, this thought is provisional: it is scaffolding around a question
still open, and as the method is worked out and made precise it dissolves — once
the structure is understood, there is nothing left here to state.
