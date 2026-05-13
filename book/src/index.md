# nix-effects

nix-effects provides effectful programs, typed validation, verified boundaries, and description-backed DSLs entirely in pure Nix.

Programs describe what they need. Handlers decide policy. Types, datatypes, and proofs describe the structure that generic tools can validate, interpret, extract, or document.

## Guide

The guide walks through nix-effects from first principles:

- **[Introduction](/nix-effects/guide/introduction)** — what nix-effects is and why it exists
- **[Getting Started](/nix-effects/guide/getting-started)** — installation, first program, REPL workflow
- **[Proof Guide](/nix-effects/guide/proof-guide)** — a first introduction to writing proofs for the nix-effects type checker
- **[Theory](/nix-effects/guide/theory)** — algebraic effects, handlers, MLTT, descriptions, and the mathematical foundations
- **[Trampoline](/nix-effects/guide/trampoline)** — stack-safe evaluation and the trampoline machine
- **[Systems Architecture](/nix-effects/guide/systems-architecture)** — how the components fit together
- **[Kernel Architecture](/nix-effects/guide/kernel-architecture)** — the MLTT type-checking kernel internals
- **[Kernel Specification](/nix-effects/guide/kernel-spec)** — formal specification with typing rules

## API Reference

Auto-generated reference documentation covering the core API, effect handlers, type constructors, stream combinators, and the type-checker internals.
