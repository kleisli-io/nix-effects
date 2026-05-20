# nix-effects

nix-effects provides effectful programs, typed validation, verified boundaries, and description-backed DSLs entirely in pure Nix.

Programs describe what they need. Handlers decide policy. Types, datatypes, and proofs describe the structure that generic tools can validate, interpret, extract, or document.

## Guide

The guide walks through nix-effects from first principles:

- **[Introduction](/nix-effects/guide/introduction)** — what nix-effects is and why it exists
- **[Getting Started](/nix-effects/guide/getting-started)** — installation, first type, first effect, first generated datatype
- **[Effects and Handlers](/nix-effects/guide/effects-and-handlers)** — computations describe operations; handlers choose policy
- **[Typed Validation](/nix-effects/guide/typed-validation)** — primitive, refined, structured, and dependent validation boundaries
- **[Generated Datatypes](/nix-effects/guide/generated-datatypes)** — descriptions, constructors, metadata, and generated families
- **[Generic Programming](/nix-effects/guide/generic-programming)** — derive schemas, dependency graphs, diagnostics, and structural views
- **[Sugar](/nix-effects/guide/sugar)** — opt-in syntax for effect pipelines and refined types
- **[Ornaments and Description-Backed Data](/nix-effects/guide/ornaments)** — enrich generated datatypes while preserving forgetful maps
- **[Proof Guide](/nix-effects/guide/proof-guide)** — a first introduction to writing proofs for the nix-effects type checker

## Concepts

Concept chapters explain the ideas behind the programming model:

- **[Theory](/nix-effects/concepts/theory)** — algebraic effects, handlers, MLTT, descriptions, and the mathematical foundations

## Internals

Implementation chapters are grouped for contributors:

- **[Trampoline](/nix-effects/internals/trampoline)** — stack-safe evaluation and the trampoline machine
- **[Systems Architecture](/nix-effects/internals/systems-architecture)** — how the components fit together
- **[Kernel Architecture](/nix-effects/internals/kernel-architecture)** — the MLTT type-checking kernel internals
- **[Kernel Specification](/nix-effects/internals/kernel-spec)** — formal specification with typing rules

## API Reference

Auto-generated reference documentation covering the core API, effect handlers, type constructors, stream combinators, and the type-checker internals.
