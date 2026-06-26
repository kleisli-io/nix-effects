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
- **[Ornaments and Description-Backed Data](/nix-effects/guide/ornaments)** — enrich generated datatypes while preserving forgetful maps
- **[Proof Guide](/nix-effects/guide/proof-guide)** — a first introduction to writing proofs for the nix-effects type checker
- **[Sugar](/nix-effects/guide/sugar)** — opt-in syntax for effect pipelines and refined types

## Concepts

Concept chapters explain the ideas behind the programming model:

- **[Theory](/nix-effects/concepts/theory)** — algebraic effects, handlers, MLTT, descriptions, and the mathematical foundations

## Internals

Implementation chapters are grouped for contributors:

- **[Trampoline](/nix-effects/internals/trampoline)** — stack-safe evaluation and the trampoline machine
- **[Kernel Architecture](/nix-effects/internals/kernel-architecture)** — the MLTT type-checking kernel internals
- **[Kernel Specification](/nix-effects/internals/kernel-spec)** — formal specification with typing rules

## Examples

Examples show complete uses of nix-effects in small programs. The source lives under `examples/` if you want to run or adapt it locally:

- **[Overview](/nix-effects/examples)** — where to start and where the source lives
- **[Proofs](/nix-effects/proof-examples)** — computational proofs, equality combinators, and verified functions
- **[Effects and Validation](/nix-effects/effect-examples)** — one validation computation under collecting, logging, and strict handlers
- **[Surface Languages](/nix-effects/surface-examples)** — STLC surface syntax, products, sums, recursive lists, refinements, and diagnostics

## API Reference

Auto-generated reference documentation covering the core API, effect handlers, type constructors, stream combinators, and the type-checker internals.
