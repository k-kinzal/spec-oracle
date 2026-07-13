# AGENTS

## Vision

spec-oracle exists to build a specification set that approximates the complete specification set of a system.

A complete specification set would express the system explicitly and exactly: nothing would remain implicit, nothing would be missing, and nothing would be superfluous. Such a set is an ideal that exists only as a concept. It cannot be fully realized for a system in the real world.

It can nevertheless be approximated. By collecting specifications and bringing them together into a coherent set, spec-oracle constructs an increasingly close approximation of that unreachable whole. The purpose is not to claim completeness, but to make the best attainable specification set sufficiently complete and precise that it can serve as an oracle for the system.

## Thought

**A specification set is represented as a specification graph.** A collection of isolated specifications cannot reveal how closely it approximates the complete set; that becomes visible through the relationships between them. Nodes and Edges therefore accumulate in an append-only Ledger. The Ledger preserves the whole graph, while the current specification set is a view derived from it; later relationships can change that view without discarding information that may become relevant again.

**Quality emerges through accumulation and selection.** spec-oracle collects Nodes and Edges in volume without requiring them to be correct at admission. Selection needs this mixed population: only as relationships accumulate can well-supported specifications emerge from it. One possible selection mechanism is a support score derived from the Edges associated with a Node. As support changes, low-quality or outdated specifications and relationships recede from the current specification set while remaining in the Ledger.

**Specifications are expressed in constrained natural language.** Unlike models, program code, or formulas, words preserve the implicit context needed to derive the human conceptual model behind a system. Unrestricted natural language, however, makes the reliable derivation of Nodes and Edges difficult. Constraints retain that context and make meaning amenable to structured interpretation, providing the basis for deriving Nodes and Edges without narrowing what can be specified.

## Reasoning Foundations

This section presents a selective set of established and influential concepts and techniques in contemporary formal specification. Their inclusion records relevant foundations; it does not commit spec-oracle to a particular formal representation or implementation.

### Temporal Properties

Temporal properties describe how system behavior may evolve over time. In the standard trace-based view, a property is a set of execution traces, and a system satisfies it when all of its traces belong to that set. Safety properties rule out behaviors whose violation can be witnessed by a finite prefix; liveness properties require that every finite prefix can still be extended to a satisfying behavior. This distinction preserves the temporal meaning of behavioral specifications without requiring a particular temporal logic.

Temporal satisfaction need not be only Boolean. Quantitative semantics can assign a robustness value to a behavior, expressing how strongly it satisfies or violates a temporal property. This makes satisfaction margins available for comparison, diagnosis, falsification, and optimization without changing the property's temporal structure. A robustness value measures a behavior relative to a property; it is not a score of the specification's quality or credibility.

This foundation follows Amir Pnueli, [*The Temporal Logic of Programs*](https://doi.org/10.1109/SFCS.1977.32), 1977, and Bowen Alpern and Fred B. Schneider, [*Defining Liveness*](https://hdl.handle.net/1813/6495), 1985. Its quantitative extension follows Georgios E. Fainekos and George J. Pappas, [*Robustness of Temporal Logic Specifications for Continuous-Time Signals*](https://doi.org/10.1016/j.tcs.2009.06.021), 2009, and Alexandre Donzé and Oded Maler, [*Robust Satisfaction of Temporal Logic over Real-Valued Signals*](https://doi.org/10.1007/978-3-642-15297-9_12), 2010.

### Hyperproperties

A hyperproperty constrains a set of execution traces rather than each trace in isolation. It can therefore express relations between multiple executions, including information-flow and observational-equivalence requirements that no ordinary trace property can capture. Hyperproperties keep such relational behavior within the specification semantics without requiring a particular logic for representing it.

This foundation follows Michael R. Clarkson and Fred B. Schneider, [*Hyperproperties*](https://doi.org/10.3233/JCS-2009-0393), 2010, and Michael R. Clarkson et al., [*Temporal Logics for Hyperproperties*](https://arxiv.org/abs/1401.4492), 2014.

### Assume-Guarantee Contracts

Assume-guarantee contracts provide the semantic foundation for behavioral specifications. A contract reads a guarantee made by a responsible subject under assumptions about its environment; the guarantee is required only where those assumptions hold. This lens gives precise meaning to composition, refinement, and contradiction between specifications. It constrains reasoning over the specification graph without prescribing how Nodes and Edges are represented or derived.

This foundation follows Albert Benveniste et al., [*Contracts for System Design*](https://doi.org/10.1561/1000000053), 2018.

### Satisfiability Modulo Theories

Satisfiability Modulo Theories (SMT) is a reasoning instrument beneath the specification language. SMT asks whether a logical formula is satisfiable relative to background theories. Applied to structured interpretations derived from constrained natural language, it can test consistency and implication and provide evidence for relationships between Nodes. It does not replace words as the specification medium or prescribe a particular representation, encoding, solver, or Edge derivation process.

The concept and terminology follow Clark Barrett et al., [*Satisfiability Modulo Theories*](https://theory.stanford.edu/~barrett/pubs/BSST09-abstract.html), 2009, and Clark Barrett, Pascal Fontaine, and Cesare Tinelli, [*The SMT-LIB Standard: Version 2.7*](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf), 2025.

### Minimal Unsatisfiable Subsets and Minimal Correction Sets

For an unsatisfiable set of constraints, a minimal unsatisfiable subset (MUS) is an unsatisfiable subset all of whose proper subsets are satisfiable. A minimal correction set (MCS) is a subset whose removal makes the remaining constraints satisfiable, while removing any proper subset of it does not. MUSes expose irreducible conflicts and MCSes expose minimal repairs without deciding which constraint is at fault. Here, *minimal* means minimal by set inclusion, not necessarily smallest by cardinality.

This foundation follows Mark H. Liffiton and Karem A. Sakallah, [*Algorithms for Computing Minimal Unsatisfiable Subsets of Constraints*](https://doi.org/10.1007/s10817-007-9084-z), 2008, and Nina Narodytska et al., [*Core-Guided Minimal Correction Set and Core Enumeration*](https://doi.org/10.24963/ijcai.2018/188), 2018.

### Maximum Satisfiability Modulo Theories

Maximum Satisfiability Modulo Theories (MaxSMT) extends SMT by distinguishing hard constraints, which every model must satisfy, from optionally weighted soft constraints, whose satisfied weight is maximized. It supports optimization over theory-aware constraints while leaving the choice of what is hard, what is soft, and how each constraint is weighted outside the solver.

This foundation follows Roberto Sebastiani and Patrick Trentin, [*On Optimization Modulo Theories, MaxSMT and Sorting Networks*](https://arxiv.org/abs/1702.02385), 2017, and [*OptiMathSAT: A Tool for Optimization Modulo Theories*](https://doi.org/10.1007/s10817-018-09508-6), 2020.

# Crates

- `so-cli`: The `spec` command-line frontend. It owns argument parsing, exit behavior, JSON output, and terminal graph rendering, and delegates service access to `so-client`. It contains no domain, persistence, or evidence-capture logic.
- `so-client`: The reusable thin gRPC client. It resolves client-local input channels such as `@file` and stdin, propagates trace context, and forwards protobuf requests and responses. It does not own the domain model or resolve evidence locators.
- `so-daemon`: The `specd` runtime and owner of the domain model. It owns the gRPC service, ingestion, protobuf conversion, persistence, evidence capture and provenance, asynchronous Jobs and Plugins, and persisted graph generation. Its current graph derivation creates written term-form vertices and exact mention Edges, not semantic specification-to-specification Edges.
- `so-lang`: The pure, I/O-free constrained natural-language surface layer. It owns the grammar, lossless AST, language version, and total parser. It recognizes sentence structure but performs no semantic interpretation or cross-specification reasoning.
- `so-protocol`: The versioned protobuf schema and generated tonic message, client, and server types. It is the wire contract only and contains no domain model, persistence model, business logic, or manual conversion logic.
- `so-reason`: The pure, I/O-free semantic and reasoning layer over `so-lang` parse trees. It owns derived speech acts, semantic structures, assume-guarantee and formula projections, and conservative judgments such as implication, contradiction, and refinement. It performs no persistence or environmental I/O.
- `so-tracing`: Shared observability infrastructure. It owns tracing and OpenTelemetry initialization, telemetry capture policy, specification hashing and recording, and gRPC trace-context propagation. It contains no specification-domain behavior.

## Development Rules

Every change must leave the workspace passing both checks:

```sh
cargo check --workspace
cargo test --workspace
```

After the checks pass, build the complete workspace in release mode:

```sh
cargo build --release --workspace
```

After the release build, restart `specd` with the newly built `target/release/specd` binary. Do not leave an older build running.
