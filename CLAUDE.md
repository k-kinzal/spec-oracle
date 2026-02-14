# AGENTS

## Project Goal

The goal is to create an open-source specification description tool for a new era.
This goal has not yet been met. Research it. Search for it. Surpass the failures of humanity's past.

## Constraints

- Behavior must always be guaranteed through tests, contracts, properties, and proofs.
- Changes and commits should always be kept to the absolute minimum.
- Specifications should always be managed using specification description tools.
- Do not implement everything from scratch; utilize existing tools and libraries where possible.
- The user cannot answer your questions. Asking for clarification is prohibited.
- There is no interest in plans. Planning mode is prohibited.

## Desirable

- First, please verify the specifications using the specification writing tool you initially created.
- Record the work performed under the `tasks` directory. There are no specific format requirements.
- Finally, ensure that the updated specifications are saved within the specification writing tool you created.

## Motivation

現代のソフトウェア開発では、多層防御（テスト・契約・性質・形式手法など）によって実装の正しさを保証します。しかし、各層が独立して進化すると、**全体としての一貫性・整合性を保つことが極めて困難**になります。

specORACLEは、**多層防御の統制を保つための基準となる仕様**を管理するツールです。完全に形式化できない「根の部分の仕様」を、多少粗くても実用的な「写像の仕様群」として表現し、各層（U0: 自然言語 → U3: 実装）の整合性を検証します。

単一の手法では保証できないからこそ多層防御が必要であり、多層防御は統制が困難だからこそspecORACLEが必要なのです。

詳細：
- **@docs/motivation.md** - なぜspecORACLEが必要なのか（背景・問題・役割）
- **@docs/conversation.md** - 仕様とは何か（理論的基盤・U/D/A/fモデル）

## Minimum Requirements to Meet User Expectations

- The architecture must separate the command and server, similar to "docker" and "dockerd."
- The server must strictly define specifications and be capable of detecting omissions or contradictions.
- The server must be able to manage graph data using either text files or an arbitrary database.
- The command must be able to process natural language.
    - It must be able to utilize any AI command, such as `claude -p ""` or `codex exec ""`.
- The command must be user-friendly. It should be able to generate correct specifications simply by inputting specification-related terms without requiring deep thought. It must also prevent the creation of contradictory specifications.
- The command must be able to resolve and normalize variations in terminology.
- The command must be able to accurately retrieve specifications and handle Q&A.
- Communication between the server and command must be handled via gRPC.
- Both the server and command must be developed using Rust.
- The managed specifications must possess multi-layered concepts.

However, these requirements are not always absolute. They represent expectations and serve as a minimum starting point, not the final goal.
