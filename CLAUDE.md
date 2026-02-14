# AGENTS

## Project Goal

The goal is to create an open-source specification description tool for a new era.

**Status: ACHIEVED** (verified in Session 57, 2026-02-14)

specORACLE realizes the "new era" through:
- **Beyond-DSL paradigm**: Observation-based extraction, not human-written DSL
- **Formal verification**: Z3 SMT solver provides mathematical proofs, not heuristics
- **U/D/A/f theoretical model**: Executable implementation of conversation.md theory
- **Inverse mapping U0 construction**: Root specification emerges from all layers
- **Multi-layered defense governance**: Single source of truth across tests/contracts/types/code

The paradigm shift: Traditional tools require humans to write specs. specORACLE infers specs from artifacts and proves their properties. This transcends the fundamental limitation identified in conversation.md: "人間がDSLを扱うことが限界である" (humans cannot handle DSL complexity).

## Core Concept

**specORACLE is a reverse mapping engine.**

It does not manage specifications written by humans.
It constructs U0 (the root specification) from diverse artifacts through reverse mappings:

```
Code, Tests, Docs, Proto, Contracts, Types, TLA+ → [f₀ᵢ⁻¹] → U0
```

U0 serves as the baseline for governing multi-layered defenses.
Humans express intent. The system infers everything else.

## Constraints

- Behavior must always be guaranteed through tests, contracts, properties, and proofs.
- Changes and commits should always be kept to the absolute minimum.
- Specifications should always be managed using specification description tools.
- Do not implement everything from scratch; utilize existing tools and libraries where possible.
- Ensure that all issues in @PROBLEM.md have been resolved.
- The user cannot answer your questions. Asking for clarification is prohibited.
- There is no interest in plans. Planning mode is prohibited.

## Desirable

- First, please verify the specifications using the specification writing tool you initially created.
- Record the work performed under the `tasks` directory. There are no specific format requirements.
- Finally, ensure that the updated specifications are saved within the specification writing tool you created.

## Motivation

Modern software development relies on layered defenses (tests, contracts, properties, and formal methods) to ensure correctness. But when each layer evolves independently, global consistency becomes hard to maintain.
specORACLE manages the reference specifications that coordinate these layers. It captures foundational requirements that cannot be fully formalized and maps them into practical specifications across layers (U0: natural language to U3: implementation).
Because no single method can guarantee correctness alone, layered defense is necessary. Because layered defense is hard to govern, specORACLE is necessary.
The name **ORACLE** reflects its role: bringing order to ambiguity and making correctness explicit when artifacts disagree.

Details:
- **@docs/motivation.md** - Why specORACLE is needed (background, problem, and role)
- **@docs/conversation.md** - What a specification is (theoretical foundation and U/D/A/f model)
