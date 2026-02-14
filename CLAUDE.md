# AGENTS

## Project Goal

The goal is to create an open-source specification description tool for a new era.

Note: The goal has not been reached. Have you realized the core concept? Have all constraints been met? Face the essence of specORACLE; the issues that should be resolved with specORACLE have not been addressed yet. Confront the problems you want to solve.

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

- All issues listed in @PROBLEM.md should be resolved.
- Behavior should always be guaranteed by means such as tests, contracts, properties, or proofs. Furthermore, it should be guaranteed not just by one, but by multiple layers.
- Specifications should always be managed using the writing tool currently being developed.
- Commits should always be made in the smallest possible units.
- Do not implement everything from scratch; utilize existing tools and libraries where possible.

## Prohibited

- The user cannot answer your questions. Asking for clarification is prohibited.
- There is no interest in plans. Planning mode is prohibited.

## Desirable

- First, please use the specification creation tool you initially developed to check the specifications of this tool. This is not an inspection of the specifications. Please understand the current specifications in terms of what features it possesses as a specification description tool.
- Record the work performed under the `tasks` directory. There are no specific format requirements.
- Finally, ensure that the updated specifications are saved within the specification writing tool you created.

## Motivation

Modern software development relies on layered defenses (tests, contracts, properties, and formal methods) to ensure correctness. But when each layer evolves independently, global consistency becomes hard to maintain.
specORACLE manages the reference specifications that coordinate these layers. It captures foundational requirements that cannot be fully formalized and maps them into practical specifications across layers (U0: natural language to U3: implementation).
Because no single method can guarantee correctness alone, layered defense is necessary. Because layered defense is hard to govern, specORACLE is necessary.
The name **ORACLE** reflects its role: bringing order to ambiguity and making correctness explicit when artifacts disagree.

Details:
- **@docs/motivation.md** - Why specORACLE is needed (background, problem, and role)
- **@docs/conversation.md** - What a specification is (theoretical foundation and UDA/f model)
