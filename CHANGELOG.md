# Changelog

All notable changes to nix-effects are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2026-02-25

Initial release.

### Added

- Freer monad core with FTCQueue (O(1) bind) and `genericClosure` trampoline (O(1) stack depth)
- MLTT type-checking kernel (`src/tc/`) with bidirectional type checking and normalization by evaluation
- HOAS elaboration bridge between Nix values and kernel terms
- Verified computation layer: prove functions total, extract certified Nix functions from proof terms
- Proof-gated derivation builder: reject invalid configs at `nix eval` time via kernel proof obligations
- Primitive types: String, Int, Bool, Float, Attrs, Path, Function, Null, Unit, Any
- Compound type constructors: Record, ListOf, Maybe, Either, Variant
- Dependent types: Pi, Sigma, Certified, Vector, DepRecord
- Refinement types with predicate combinators: `refined`, `allOf`, `anyOf`, `negate`, `positive`, `nonNegative`, `inRange`, `nonEmpty`, `matching`
- Linear types: Linear, Affine, Graded
- Universe hierarchy: `typeAt n` for arbitrary levels, convenience aliases Type_0 through Type_4
- Algebraic effect handlers: state, error, reader, writer, acc, choice, conditions, typecheck, linear
- Handler `resume`/`abort` distinction for continuation control
- Effectful lazy streams: `fromList`, `iterate`, `range`, `replicate`, `map`, `filter`, `scanl`, `take`, `takeWhile`, `drop`, `fold`, `toList`, `length`, `sum`, `any`, `all`, `concat`, `interleave`, `zip`, `zipWith`
- `adapt` and `adaptHandlers` for handler state composition
- `mk { doc, value, tests }` structured module pattern with inline documentation and tests
- `extractDocs` for per-module API markdown generation
- Flake with lib, tests, packages, and checks outputs
- nix-unit integration for `nix flake check`
- Documentation: 8 book chapters (introduction, getting started, proof guide, theory, trampoline, systems architecture, kernel architecture, kernel formal specification)
- Examples: equality proofs, proof basics, typed derivation, verified functions
- MIT license
