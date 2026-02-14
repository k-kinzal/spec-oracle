# AGENTS

## Project Goal

The goal is to create an open-source specification description tool for a new era.
This goal has not yet been met. Research it. Search for it. Surpass the failures of humanity's past.

## Constraints

- Behavior must always be guaranteed through tests, contracts, properties, and proofs.
- Changes and commits should always be kept to the absolute minimum.
- Specification management should be conducted using new specification tools to perform dogfooding.
- Do not implement everything from scratch; utilize existing tools and libraries where possible.
- The user cannot answer your questions. Asking for clarification is prohibited.
- There is no interest in plans. Planning mode is prohibited.

## Desirable

- Record the work performed under the `tasks` directory. There is no specific format required.

## Motivation

@docs/conversation.md

## Minimum Requirements to Meet User Expectations

- The architecture must separate the command and server, similar to "docker" and "dockerd."
- The server must strictly define specifications and be capable of detecting omissions or contradictions.
- The server must be able to manage graph data using either text files or an arbitrary database.
- The command must be able to process natural language.
    - It must be able to utilize any AI command, such as `claude -p ""` or `codex exec ""`.
- The command must be able to resolve and normalize variations in terminology.
- The command must be able to accurately retrieve specifications and handle Q&A.
- Communication between the server and command must be handled via gRPC.
- Both the server and command must be developed using Rust.
- The managed specifications must possess multi-layered concepts.

However, these requirements are not always absolute. They represent expectations and serve as a minimum starting point, not the final goal.