# Changelog

All notable changes to nix-effects are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- **Kernel evaluator defunctionalized into a CEK-style abstract machine.** The evaluation hot path (`evalF` / `vAppF` / `instantiateF` / `vDescIndF` / `vEverywhereDF` and the desc-con trampoline) is now driven by a `builtins.genericClosure` + `builtins.foldl'` state machine (`src/tc/eval/machine.nix`) over an explicit frame/continuation algebra, replacing direct mutual recursion. User-level recursion depth N now produces O(1) libnix call frames and O(1) Nix call-depth per evaluator step, with O(N) work spread over O(N) driver iterations. Public signatures of `evalF` / `vAppF` / `instantiateF` / `vDescIndF` / `quote` / `nf` are preserved byte-for-byte; no consumer call site changes. `quote` and eval hand off end-to-end inside the same machine, and eliminator dispatch from machine handlers — including `lower` elimination (`vLiftElimF`) and the bootstrap eliminators — routes through machine frames instead of synchronous calls.
- **Conversion checking is defunctionalized and depth-flat in all value directions.** The recursive structural arms of `conv` are replaced by `runConvF`, a spine-peeling sub-machine that exposes structural children as direct pointers into the forced value and discharges flat goal lists, with a BFS frontier over sibling goals so neither spine-deep nor sibling-deep values recurse on the host stack. Binder descent (`VPi` / `VLam` / η / `VSigma`) and the level normalizer (`flattenLevel` / `dedupLevel`) are equally flat. The public `conv` signature is unchanged; all consumers untouched.
- **The bidirectional type checker is depth-flat.** Structural descent previously consumed host call-depth proportional to term depth (a nested error handler per descent plus host-stack recursion in the check/infer arms). Blame tracking now threads a flat frame stack in handler state, and recursive entries yield to the trampoline so deep terms check in O(1) host call frames — `checkType` on right-nested Pi and `checkTm` on deep lam/let pass at N=10000. Surfaced blame traces are identical; N retained blame frames cost O(N), not O(N²).
- **Every kernel hot path now runs depth-flat.** With conversion and checking joining the machine-driven evaluator, evaluation, quoting, conversion, and type checking all cost O(1) host call frames per step regardless of user-term depth. Residual host-stack recursion is confined to auxiliary helper walks (metavariable collection, extraction and reflection, generic-programming helpers) whose depth follows type/metadata structure rather than user-term depth.
- **`VDescCon` linear chains use a flat chain-form representation.** `vDescConChain` / `_layers` / `_shape = "linearChain"` replace the deep nested-attrset descriptor chain, unblocking 5000-deep constructor and evaluation workloads that previously overflowed. `quote` binder and VNe-spine read-back route through the machine's `runQuoteF`.
- **nixpkgs and `nix-unit` pins are unified in `pins.nix`.** `nixpkgs.nix` and `nix-unit-pinned.nix` are replaced by a single `pins.nix` consumed by the flake, shell, and test entry points. `nix-unit` is pinned to 2.34.0.

### Added

- **Verified `v.elimData` / `v.matchData` wrappers.** They are to a user `H.datatype` what `listElim` / `matchList` are to lists: branch binders are built from datatype metadata and each branch body is ann-wrapped against the motive image at its constructor, so branches are checked rather than synthesised. Handlers are keyed by constructor name, curried over fields then one induction hypothesis per recursive field. `elimData` takes a dependent motive; `matchData` is the constant-motive case analysis. Non-parametric datatypes only.
- **Depth-flatness regression tests.** Eliminators (lift-elim, boot-sum-elim, boot-J, squash-elim) nested N=1000 in scrutinee position over a neutral seed; checker `checkType` / `checkTm` at N=10000; conversion sibling- and balanced-depth shapes. A depth regression overflows max-call-depth well before these bounds.
- **Depth-scaling regression workload** `bench/workloads/tc/eval-depth-scaling.nix` exercises evaluator depth N across desc-ind, vAppF, and conv chains, guarding against future depth regressions.
- **dnzl joins the ecosystem section.** [dnzl](https://github.com/denful/dnzl) by @vic — an actor system for Nix using nix-effects streams for inbox and sidecar communication channels, with behaviours as plain Nix functions stream-folded over state.

### Fixed

- **WHNF-forcing boundaries in conversion, elaboration, and read-back.** Operands of `vStrEq`, meta-bearing annotations, and types are forced to weak-head normal form before tag dispatch; meta-bearing closures are opened via the overlay instantiator in `tc.elaborate` (kernel instantiation would crash reading `.tag` on a metavariable); `extract` and `quote` read-back honor WHNF boundaries; run-state results are forced to WHNF.
- **Datatype names survive nested extraction.** `extractInner` lost constructor/field names whenever a named datatype was nested inside another type, decoding it positionally as `con<i>` / `_field<j>`. Sum arms are now recovered from the app-spine (which retains datatype metadata) and record fields thread the constructor's declared field types, falling back to `reifyType` only for dependent or metadata-less fields. Opaque derivation payloads remain opaque by design.
- **`fieldTyOf` strips the `monoAt` ann artifact for declining-shape constructor args.** A parametric `monoAt` ascribes each substituted param against its kind, so an instantiated data field type read as `ann (listOf string) (u 0)`; consumers inspecting the field-type former saw the ann, dropped CHECK to INFER, and a bare cons/nil argument landed in the element-type slot. The strip is centralized in `fieldTyOf`, the sole field-type reader, so future consumers cannot reintroduce the gap.

### Performance

- **Known regression: the depth-flat machinery costs CPU and allocations.** Measured with the bench suite at the flake-pinned evaluator (no Nix-version confound), the full typechecker test suite costs ~4× CPU (29s → 119s) and 2.4–4.4× allocations versus 0.12.0; kernel workload medians regress across evaluator counters (attribute lookups +83%, function calls +50%, environments +46%, attrsets +40%, thunks +27%). The cost concentrates where blame brackets and trampoline churn are dense (worst workloads ~11×), not where terms are deep (pure deep chains ~+16% CPU); the `effects.*` layer is unaffected. This is the current price of O(1) host call-stack depth; attribution and optimization are in progress.
- **Equality-witness normal forms are shared across `checkHoas`'s type builds.** `checkHoas` builds the checked type three times (well-formedness, type evaluation, refl-conversion); for an equality telescope the last two each re-derived the same witness normal forms. The witnesses are now derived once from the already-checked type term and spliced into both subsequent builds — sound by eval-determinism, since the spliced witnesses are the checked type's own sub-terms and well-formedness is still checked genuinely on the unspliced term. A composed-handler law region drops from ~1.76 GiB to ~960 MiB live peak.
- **Kind-validated ann params skip description-body re-materialization.** `generatedParamTerm` gated its trusted-description fast path by re-checking whether each ann-wrapped param's body is itself generated, forcing expensive description-body materialization for composed-handler descriptions. Params whose ann body is already checked against its kind annotation are now trusted without re-materializing the generated description body.

## [0.12.0] - 2026-05-20

### Headline changes

#### Generic typed boundaries and datatype tooling

- **Datatype descriptions now drive generic metadata, views, round-trips, derivation, and checking.** The new `tc.generic` layer derives descriptor views, value/project/review helpers, dependency/schema-style artifacts, and stack-safe `checkD` validation from the same generated datatype descriptions used by the kernel.
- **Records, variants, and certified boundaries move onto description-backed data.** `Record` and `Variant` route through generated datatype evidence, `Certified` exposes its Σ shape in the kernel, and validation descends through a Contract detail layer with stable path and reason data instead of ad hoc walkers.
- **Decidable predicates become first-class library material.** `LeDT`, the decidable surface library, `Nat` equality/order witnesses, `IntZ`, and `intzLe` provide reusable proof objects for common value-level reasoning.

#### Surface elaboration and implicit arguments

- **The elaborator grows metavariable unification, check/infer overlays, and implicit insertion.** New `tc.elaborate` modules cover constraints, contexts, zonking, meta evaluation, checked/inferred overlays, value conversion, and `runElab`, with regression coverage for postponed constraints and wake-up chains.
- **A surface framework lands for description-backed DSLs.** The new `tc.surface` namespace includes registries, handler context, implicit support, parser/printer/elaborator derivation hooks, and a prelude used by the STLC examples.
- **STLC examples now exercise sums, products, recursive lists, and refinement diagnostics.** These examples validate the surface layer against realistic typed DSL shapes rather than isolated kernel snippets.

#### Description-interpreted effects

- **Experimental handler descriptions are represented as indexed descriptions.** `experimental.desc-interp` adds a FreeFx-style kernel, `IDesc (U × U)` handler result shapes, `UniRet`, state/error handler descriptions, extraction, trampoline support, and compatibility adapters.
- **Handler composition gets checked laws and shortcuts.** `composeHandlers`, `qAppKernel`, `qAppIdLaw`, state/error shortcut lemmas, residual-form emission, extension layering, and parity tests cover composed state/error handlers and deep bind chains.

#### Kernel `Derivation` primitive and generic `Thunk` carrier

- **`Derivation` joins the axiomatized primitive set as a new Nix native type.** Decided by `(v: builtins.isAttrs v && (v.type or null) == "derivation")` and sits parallel to `Path` (which uses `builtins.isPath`); the two primitives share no values — `Path` rejects attrsets, `Derivation` rejects strings and non-derivation attrsets.
- **Full pipeline coverage.** `Derivation` / `DerivationLit` ride through eval, quote, conv, infer, check, elaborate, extract, and the generic native predicate / expectation / onPrim wiring, mirroring the existing `Path` primitive's surface exactly. HOAS surface: `H.derivation` / `H.derivationLit`. Exported on both the sugar wrapper and the non-sugar `fx.types.Derivation` surface.
- **Motivates principled `package`-shaped fields.** Downstream typed builders can now require `package : H.derivation` instead of falling back to `H.any`, validating at the review boundary that a tool or dependency carries a real Nix derivation rather than a string.
- **Parametric `H.thunk : Hoas → Hoas` as a generic deepSeq-safe carrier.** `H.thunk a` is the kernel type former for `{ _tag = "Thunk"; _force = _: value : a }` — a closure-wrapped value of any inner type, opaque to `builtins.deepSeq`. The walker runs a *lazy structural check*: it verifies `is attrset ∧ has _force closure` and does NOT recurse into `_force`; inner-type validation runs at forget time, post-forced. Forcing in the validator would defeat the deepSeq-shielding the whole construct exists for. Handler-state-bound derivations are typed as `H.thunk H.derivation`.
- **Handler-state transport via Thunk.** A real Nix derivation cannot be threaded through trampoline-threaded handler state — its cyclic `passthru`/`all`/`outputs` graph hangs `builtins.deepSeq newState` (`src/trampoline.nix:124`), uncatchable by `tryEval`. `fx.state.mkThunk` wraps any value as `{ _tag = "Thunk"; _force = _: value; }` — closures are opaque to `deepSeq` — and `fx.state.forceThunk` recovers it after the trampoline returns. `H.thunk a` and the bare inner type `a` are disjoint at the validator — no implicit subtyping, explicit one-step coercions in both directions.

#### Ornament layer for generated datatypes

- **Ornaments are now a public datatype refinement layer.** Generated datatypes can be refined by checked ornaments with compiled descriptions and forgetful maps, including identity, composition, pullback, liftFold, law tests, structured diagnostics, and source-path reporting.
- **Algebraic ornaments connect folds to indices and inserted fields.** The public `algOrn` helper validates supported description/algebra shapes, covers the List-to-Vec pattern, and rejects unsupported fragments with stable diagnostics.
- **Functional ornaments add the forward direction.** A functional ornament is an ornament plus a checked section of its forgetful map, so base values can be canonically enriched, composed, lifted through producers/transforms, and diagnosed when inserted data or proof obligations are missing.

### Added

- **`tc.generic` namespace** — description, datatype, value, derive, check, `checkD`, ornament, and path modules for generic consumers over datatype descriptions.
- **`tc.surface` namespace** — surface registries, handler contexts, implicit elaboration, parser/printer/elaborator derivation hooks, ornament definitions, and surface tests.
- **Meta-aware elaboration APIs** — metavariables, constraints, zonking, check/infer overlays, literal `Val → Tm` splicing, and checked value extraction support the new surface layer.
- **`fx.state` namespace** — new state-carrier surface. Initial inhabitants: `mkThunk` / `forceThunk` / `isThunk` for deepSeq-safe transport of arbitrary values through handler state. Source: `src/state/thunk.nix`; rationale in `book/src/trampoline.md` § "State-shape contract".
- **`fx.types.Derivation`** — exported on the public `fx.types` surface and kernel-decided (`kernelType = H.derivation`, no guard). Accepts raw drv attrsets — for typed `package` fields and similar review-boundary checks.
- **`H.thunk : Hoas → Hoas`** — parametric deepSeq-safe carrier type former, walked lazily and structurally (verifies `_force` closure, never invokes it). Usable wherever a value must survive trampoline `deepSeq` while remaining recoverable post-forget.
- **Kernel `Empty` / `Absurd` primitives** — restored as explicit primitives for the implicit/surface migration path.
- **`H.product` sugar** — named single-constructor μ-datatypes can be introduced as product-shaped records without hand-writing the lower-level description form.
- **`defEq` exposure** — sugar compatibility tests and callers can anchor on definitional equality directly.
- **First-class ornaments for generated datatypes** — HOAS and generic surfaces expose ornament construction, checked metadata, `ornDesc`, `ornForget`, identity, composition, pullback transport, liftFold transport, and indexed/unit-indexed compatibility.
- **Ornament diagnostics and law harness** — validation APIs report datatype, constructor, field, indexed-branch, and algebra-node context while semantic maps stay pure after validation.
- **Functional ornaments for generated datatypes** — the HOAS surface exposes `functionalOrnament`, section/build accessors, law diagnostics, composition, and producer/transform lifting. The generic surface adds synthesis from `{ base; spec; synth; }`, proof and measure obligations, structured diagnostics, and canonical build/forget helpers.
- **MetaBuilder-style functional ornament pilot** — a synthetic `CoreBuilder -> CodeGenBuilder -> IdlBuilder` chain demonstrates public-API enrichment, composed sections, forget coherence, lifted producers, and missing-enrichment diagnostics.
- **Description labels and self-describing API wrappers** — generated descriptions carry erasable constructor/field labels, and public API leaves carry co-located descriptions, signatures, docs, tests, and source metadata.
- **New documentation and examples** — README rewrite, generated-datatypes, typed-validation, ornaments, effects-and-handlers, and generic-programming chapters; STLC examples; source mtime/SHA metadata for generated docs.
- **Bench workloads** — new generic, ornament, meta-unification, surface, decidable, `checkD`, paired state-chain, and experimental desc-interp workloads.
- **Docs-content CI gates** — the external docs corpus derivation now depends on deterministic docs checks, and `nix flake check` builds the corpus plus anchor/schema/routing gates.

### Changed

- **`Record` and `Variant` are description-backed datatypes.** Value walkers now recover constructors through datatype metadata and project fields through generated eliminators instead of the previous bespoke HOAS record/variant path.
- **Type-checking diagnostics use structured paths and Contract details.** `typeCheck` handlers receive richer reason/detail data, fail-only validation paths, wildcard hint keys, per-hint source positions, and parent backlinks for generated docs.
- **`Desc` and description operations lift the old `I : U(0)` restriction.** `descDesc`, `VDesc`, `canonRef`, `interpD`, `allD`, and `everywhereD` now carry the index universe level explicitly.
- **`fx.sugar.do` is replaced by a composable Kleisli pipeline; the old form is available as `steps`.** Documentation and compatibility tests now use the split naming.
- **Source internals are gated behind `exposeInternals`.** The public import keeps the curated API surface by default while internal consumers can opt into the raw source tree.
- **Bench history archives the recovery baseline.** The previous active baseline was renamed to `baseline.recovery-target.{json,md}`, and the failed `ci-1f13e07f` gate artifacts were removed from the active history.

### Fixed

- **API docs traversal is bounded.** Recursive documentation extraction avoids unbounded walks through generated API data.
- **Datatype fast paths are signature-aware.** Conversion and checking shortcuts no longer conflate generated datatype descriptors that share a shape but differ in signature.
- **Dependent datatype fields validate against their expected types.** Polymorphic field intros now thread expected types, and the latest homogeneous-chain optimization trusts prevalidated non-recursive field arguments only at the empty top-level context.
- **Implicit surface migration is green.** STLC implicits, `EffState` implicit parameters, and the broader implicit migration suite have regression fixes.
- **Inline tests call `api.mk` wrappers correctly.** `hasHandler`, plan, and benchmark tests no longer invoke wrapped namespaces as functions.
- **Generated anchor and docs tests are path-stable.** Schema tests scrub world-root paths, anchor golden files cover book chapters and hint docs, and docs-resolves tests cover deep-page routes.
- **Bench workloads track internal namespace moves.** Workloads were retargeted after `_internal` migration and split-module changes.

### Performance

- **Ornament benchmark workloads** — quick-tier workloads now cover `ornDesc`, `ornForget`, composition, algebraic ornaments, generic metadata/view/review/derive artifacts, functional synthesis, failed synthesis diagnostics, lifted producers, and the synthetic MetaBuilder-style chain. On the local quick sample, `tc.generic.functional-builder-chain` evaluated in about 221 ms wall / 0.171 s evaluator CPU while preserving `forget` and `liftedForget` checks.
- **Description-interpreter shortcuts** — `pureCon` memoization and removed kernel η-wrappers make `qApp` about 40% faster; state/error handlers cache per-op values and share shortcut paths across composed handlers.
- **Type-checker and evaluator fast paths** — certificate paths reuse `ty.D`, description eliminators share `ihVal`/`muFam`, closed deciders are pre-elaborated, test probes are hoisted, and `litVal` gives O(1) value reflection where possible.
- **Diagnostics allocate less on deep traces.** `multiLine` chain-position walking is fused and trace appends use literal records instead of `//`.
- **Homogeneous constructor chains avoid repeated field checks.** When a flattened constructor chain reuses the same simple data fields at every layer, elaboration prevalidates the shared field terms once and the kernel checker reuses that attestation only at the top-level empty context.

### Removed

- **Legacy bespoke `H.record` / `H.variant` implementation path** — the public constructors remain, but their behaviour now comes from generated datatype descriptions and `RecordOpen` metadata records.

## [0.11.0] - 2026-05-13

### Headline changes

#### Fully levitated public data layer

- **Public inductive data is now generated by the description/datatype layer.** `Nat`, `List`, `Sum`, `Bool`, `Eq`, `Fin`, `Vec`, and `W` route through the same levitated datatype machinery available to users. The old dedicated `Nat` / `List` kernel constructors and eliminators are gone from the public path
- **Bootstrap equality and coproducts are internal implementation details.** The kernel keeps small bootstrap pieces where they are needed to type the theory, but public `eq`, `refl`, `J`, `sum`, `inl`, and `inr` go through the generated datatype layer. This keeps the user-facing API decoupled from the bootstrap representation
- **Description constructors are themselves encoded through the description layer.** `Desc I k` round-trips through the canonical description-of-descriptions representation, with conversion and quoting fast paths for the canonical views

#### Strong levitation and kernel boundary

- **Strong levitation for descriptions.** `Desc I k` definitionally reifies through `μ ⊤ (descDesc I k) tt`, and canonical desc views let conversion compare encoded descriptions without expanding every layer
- **Kernel-owned generic description operations.** `interpD`, `allD`, and `everywhereD` replace the old HOAS-side `descElim` cascade, so interpretation and traversal are centralized at the trusted boundary instead of duplicated in the surface layer
- **Level-polymorphic datatype surface.** `Lift`, `natToLevel`, per-summand levels, and generated level-polymorphic `Sum` / `W` make datatype construction explicit about universe transport without restoring cumulative subtyping

#### Effects and streams

- **Scoped handler convenience APIs.** `scope.provide`, `scope.val`, and `bind.optionalArg` make reader-style scoped effects and optional handler-dependent arguments first-class. Credit: @sini (from #19)
- **Stream composition APIs.** `stream.flatMap`, `stream.signal`, `stream.signalOn`, and public `fx.isComp` are now exposed. Credit: @vic (from #22)

### Added

- **Fully levitated public inductive prelude** — generated `Nat`, `List`, `Sum`, `Bool`, `Eq`, `Fin`, `Vec`, and `W` definitions share the datatype macro path instead of special public kernel paths
- **Level-polymorphic `W` datatype** — generated by the datatype macro, including tests for universe-polymorphic construction and elimination
- **Canonical description references and certificates** — generated descriptions carry stable descriptor references so conversion can recognize shared generated data without expanding the full encoded description every time
- **`Lift` primitive** — explicit cross-level transport. `Lift l m eq A : U(m)` for `A : U(l)` with bound witness `eq : Eq Level (max l m) m`; introducer `liftAt`, eliminator `lowerAt`. Smart constructor collapses idempotently at `l ≡ m` (`Lift l l _ A ≡ A`, `liftAt l l _ A a ≡ a`, `lowerAt l l _ A x ≡ x`). HOAS surface: `LiftAt` / `liftAt` / `lowerAt`
- **`natToLevel : Nat → Level`** — structurally reduces on closed Nats (`natToLevel zero ≡ levelZero`, `natToLevel (succ n) ≡ levelSuc (natToLevel n)`); stuck on neutrals. Asymmetric — no `levelToNat` rule
- **`scope.provide` / `scope.val`** — stateless scoped handlers (reader/val pattern). `scope.provide handlers body` installs `handlers` for `body`'s dynamic extent without touching state; unhandled effects rotate outward and outer state mutations survive unaffected. `scope.val` is a convenience wrapper named after Koka's `val` handler: takes an attrset of constant values and builds handlers via `handlersFromAttrs`. Credit: @sini (from #19)
- **`bind.optionalArg` sentinel** — explicit marker for optional bindAttrs entries. `bindAttrs { x = optionalArg; ... }` probes via `has-handler` and omits `x` from the result when no handler is installed (Nix function defaults can then take over). `bind.comp` / `bind.fn` translate `lib.functionArgs`'s `true` (= has default) into this sentinel internally — the magic-coupling to `lib.functionArgs`'s output shape is now confined to the wrappers, and `bindAttrs`'s "non-comp value → `send name value`" contract is preserved literally for `true`
- **`stream.flatMap`, `stream.signal`, `stream.signalOn`, and `fx.isComp`** — stream composition and repeated-signal suppression helpers, plus a public computation predicate. Credit: @vic (from #22)

### Changed

- **Public datatype APIs route through generated descriptions.** Primitive kernel data is now bootstrap/internal; the public surface is the levitated datatype layer
- **Description quotation and conversion use canonical views.** Encoded descriptions retain their mathematical shape while avoiding repeated full expansion in common conversion paths
- **Per-summand level on `descArg` / `descPi`** with bound witness `eq : Eq Level (max l k) k`. The summand sort `S` may live at level `l` ≤ description level `k`; cross-level transport at every introducer / eliminator is via `Lift`
- **Benchmark history records two recalibrations.** The earlier queue-raw-resume calibration is preserved for attribution; the active quick-tier baseline was regenerated after the public data layer moved through the generated datatype path

### Fixed

- **Deep generated `Nat` / `List` chains remain stack-safe.** Regression tests cover 5000-deep generated values through the levitated datatype path
- **Description eliminator saturation and branch dispatch.** Over-applied encoded eliminators now saturate correctly, and `μ` branch selection uses datatype metadata instead of forcing failing semantic tests
- **Generated `Sum` proof paths.** Public `sum`, `inl`, `inr`, and `sumElim` now elaborate through the generated datatype representation without losing the expected proof shape
- **Deep handler routing through bind chains around scope rotation.** `queue.append` and `queue.snoc` now preserve the `__rawResume` flag set by `effectRotate` on rotation continuation queues. Without this, `bind` chains wrapping a rotating `scope.provide` / `scope.run` / `scope.runWith` lost the flag mid-chain — the outer interpreter fell back to `resumeCompOrValue` instead of `resumeWithQueue`, so effectful resumes from outer handlers no longer routed through inner-scope handlers. `append` fix credit: @sini (from #19); `snoc` fix closes the symmetric path on `kernel.bind`
- **`queue.append` fix preserved one-sided:** the flag is propagated from `q1` (the rotation continuation queue, which appears on the left at every current call site). `q2.__rawResume` is intentionally not propagated — no current call site produces it on the right

### Removed

- **Dedicated public `Nat` / `List` kernel paths** — public natural numbers and lists now use the generated datatype path
- **Primitive public description constructor surface** — description constructors are exposed through the encoded/canonical description layer instead of as a parallel HOAS cascade
- **Obsolete generated-desc tests tied to the retired representation** — tests now assert the canonical encoded shape rather than the removed primitive constructor path
- **`Sub-at-U` structural conv coercion** (CHECK trampoline's universe-cumulativity bridge). The kernel is non-cumulative: a term checked against `U(k)` must have inferred type exactly `U(k)` modulo `convLevel`. Cross-level transport is via explicit `Lift`

### Performance

- Canonical description peel views are cached and reused across evaluation, checking, and conversion
- Conversion fast paths skip redundant per-layer arm checks when generated datatype metadata proves both sides share the same description
- Homogeneous auto-witness `Lift` nodes erase in HOAS elaboration when source and target levels are equal
- `tt`, `refl`, empty-head, and certificate-target syntactic fast paths avoid expanding large generated descriptions on common proof paths
- L=0 fast-paths in `interpF` (eval-side) and `interpHoasAt` (HOAS-side): when the description level is statically zero, emit the post-collapse form directly without `Lift`-wrap or extra closure-env entries. HOAS↔eval conv preserved (same Val under instantiation; smart constructor collapses Lift at equal levels)
- `desc-arg` / `desc-pi` eq-slot fast-path: when `(l, k) = (0, 0)` and `tm.eq` is syntactically `refl`, emit `mkRefl` directly without recursing through CHECK
- Bench gate excludes `symbols` / `symbolsBytes` from the alloc max-fold — these track interned-string growth (new tag names, test names, binder names), not workload work. Reported in blame with `codeSize: true` for visibility
- `queue.append` / `queue.snoc` only allocate the `__rawResume` overlay attrset when the source queue actually carries the flag; common-case `bind` chains pay only an `or false` lookup. Credit: @sini (from #19)
- **Post-raw-resume baseline recalibrated.** `queue.snoc`'s `__rawResume` preservation (the snoc fix above) adds one attrset lookup per `kernel.bind` on the Impure path. Alternative encodings (`ImpureRaw` comp variant, `//` overlay) pay the same cost in different alloc fields — the discriminator is structurally additive, so the snoc fix's correctness gain (deep handler routing through `bind (provide _ _) k`) required a historical recalibration. @sini's `queue.append` fix from #19 is on the per-effect path and not gate-visible. Affected workloads at that point: `bindHeavy.s10k` +23‰, `nestedHandlers.d3_i1k` +11‰, `interp.{fib10,fib15,sum1000,countdown1000}` +6-14‰. Previous baseline preserved at `bench/history/baseline.pre-pr19.{json,md}`; the intermediate recalibration is preserved at `bench/history/baseline.post-raw-resume.{json,md}`
- **Post-levitation baseline is now active.** `bench/history/baseline.{json,md}` was regenerated after levitated data checks with 50 runs and 3 warmups, superseding the intermediate post-raw-resume baseline for current bench gating

### Contributors

- Thanks to @sini / Jason Bowman for the #19 contribution set: scoped `provide` / `val`, optional bind arguments, and the `queue.append` raw-resume preservation and allocation optimization work
- Thanks to @vic / Victor Hugo Borja for stream `flatMap`, stream signal helpers, and top-level `fx.isComp` exposure from #22, plus Den/ned documentation improvements from #23 and continued downstream feedback from Den and ned

## [0.10.0] - 2026-04-26

### Headline changes

#### Kernel

- **Universe-polymorphic descriptions and universes.** `Desc^k I`, `U(k)`, `descArg^k`, `descPi^k`, `descElim^k` carry an explicit universe level `k : Level`. The Tarski `Level` sort (`zero` / `suc` / `max`) inhabits `U(0)`; `convLevel` normalises level expressions modulo idempotence of `max`, distribution of `suc`, and zero absorption before comparing structurally
- **Conversion fast-paths.** Π-η reduction (`λx. f x ≡ f`) with `freshVar` sharing across both sides of `convVal`, plus a `convLevel a == b` syntactic-equality short-circuit **Description-of-descriptions.** `descDesc : Π(k:Level). Desc ⊤` describes descriptions themselves at any level. The `iso(D)` theorem is stateable in the kernel via the right-associated Σ shape `Π(k:Level). Σ(to). Σ(from). Σ(toFrom). fromTo`, and `from(to D) ≡ D` reduces structurally on prelude descriptions

#### Performance

- The representative cons-list construction workload is alloc-neutral against the 0.9.0 baseline (primOpCalls ±0‰; sets −26.6‰), and the full quick-tier alloc gate passes

#### Tooling and surface

- **Dual-metric bench harness** (`bench/`). `bench-run` samples each workload N times and records `NIX_SHOW_STATS` allocation counters plus cpu percentiles under `bench/history/<name>.{json,md}`. `bench-gate` classifies a run against the committed baseline, demotes hard-fails matched by `Perf-regression: <workload>, <reason>` commit trailers to "overridden", and runs **alloc-only in CI** (shared runners have too much cpu variance against a workstation-captured baseline). `bench-calibrate`, `bench-compare`, `bench-open-regressions`, and `bench-lint-workloads` round out the toolchain as flake packages. Per-workload cpu budgets, `noiseLimited` (cpu-axis) and `allocNoiseLimited` (alloc-axis) exclusion arrays, a Nix-version guard, and typo / missing-registry guards ship in `bench/budgets.toml` + `bench/runner/finalize-gate.nix`
- **Kernel diagnostic surface.** `H.checkHoas` / `H.inferHoas` now attach a `hint` string and a `surface` HOAS-node pointer to every type-error, lazily — only the failure branch materialises the walker. Powered by a position-stack effect in the `runCheck` handler (`src/tc/check/ctx.nix`), a `bindP pos m k` bracket combinator that tags sub-delegations with structural `Position`s, and a SourceMap mirror tree (`src/tc/hoas/source_map.nix`) keyed on the same `Position` alphabet
- **Bool / Void retired as primitives.** `H.bool = μ ⊤ (plus (retI tt) (retI tt)) tt`, `H.void = Fin 0`, `H.boolElim` via `descInd`, `H.absurd` via direct `J`-transport through `natCaseU`. Six `Tm` constructors, four `Val` constructors, two `Elim` frames, twelve dispatch cases, and ~60 lines of dead helpers leave the TCB. API surface unchanged **Indexed datatype macro.** `datatypeI` and `datatypePI` compile arbitrary-indexed inductive families atop the ⊤-indexed `datatype` / `datatypeP`. `FinDT`, `VecDT`, `EqDT` replace the hand-written description / constructor / eliminator triples; ~260 lines collapse to 25 lines of forwarders
- **Path-threaded `typeCheck` effect.** `Type.validateAt path v` recurses structural path segments through `Record`, `ListOf`, `Variant`, `Sigma`. Value-side and kernel-side Errors now share one `Position` ADT, so a single pretty-printer and hint-resolver cover both

### Added

#### Kernel — Level sort

- `Level` sort with `mkLevel`, `mkLevelZero`, `mkLevelSuc`, `mkLevelMax`, `mkLevelLit n` term constructors and `vLevel*` value mirrors. `convLevel` normaliser modulo idempotence, distribution of `suc`, zero absorption, and sorted-spine `max`, plus an `a == b` syntactic-equality fast-path
- `vLevelMaxOpt` — drop-zero-if-dominated optimisation for
  `vLevelMax`, applied in `descInd` `K_eff` reconstruction
- `reifyLevel` — closes the kernel↔HOAS round-trip for polymorphic levels

#### Kernel — Universe-polymorphic primitives

- `descDesc : Π(k:Level). Desc ⊤` — kernel-internal description of descriptions, threaded for the `iso(D)` weak-levitation theorem
- Universe-polymorphic `descElim` (leading `K : Level` slot matching the description's level) and heterogeneous `funext` (`Π(j:Level). Π(k:Level)` with decoupled domain/codomain levels)
- `checkDescAtAnyLevel` — bidirectional bridge that infers the description's universe level from a checked target type before delegating to the level-indexed description CHECK rules
- Π-η conversion with `freshVar` sharing across both sides of `convVal`

#### Tooling and surface

- `datatypeI name I consList` / `datatypePI name params indexFn mkCons` with `conI` / `recFieldAt` spec constructors; `FinDT` / `VecDT` / `EqDT` scope bindings
- `fx.effects.hasHandler : String → Computation Bool` (reserves the effect name `"has-handler"`) Deep handler semantics for effect rotation (Plotkin & Pretnar): raw resumes from an outer handler route back through the inner scope
- `.github/workflows/bench-gate.yml` — alloc-only CI gate per push / PR, with step-summary publication
- Short-alias `bench-*` commands alongside `nix-effects-bench-*` via a `bench-shims` derivation in `shell.nix`
- `bench/workloads/tc/{bindP,diag}.nix` canaries; `tc.e2e.let-chain-100`

### Changed

- **Breaking:** description and universe constructors take a leading `Level` slot. `vDesc`, `vDescArg`, `vDescPi`, `vU`, `mkDesc`, `mkDescArg`, `mkDescPi`, `mkDescElim`, `mkU` accept a `Level` Val/Tm; integer literals must be wrapped explicitly via `mkLevelZero` / `mkLevelLit n` (or `vLevelZero` / `vLevelSuc vLevelZero` for the common 0/1 cases)
- `StrEq` INFER rule returns the derived `H.bool`; `reifyType` recognises the plus-coproduct mu shape and maps back to `H.bool`
- Fin / Vec / Eq preludes in `hoas/combinators.nix` are η-expanded forwarders over macro outputs; `absurdFin0` discharges `Fin 0` via direct `J`-transport through `natCaseU`
- `readSrc` (`default.nix`) recurses into subdirectories uniformly in both split-module and plain-namespace modes; every output is `api.mk`-wrapped

### Removed

- Kernel `Tm` constructors `Bool` / `True` / `False` / `BoolElim` / `Void` / `Absurd`; kernel `Val` constructors `VBool` / `VTrue` / `VFalse` / `VVoid`; `Elim` frames `EBoolElim` / `EAbsurd`; HOAS aliases `boolPrim` / `truePrim_` / `falsePrim_` / `voidPrim` / `absurdPrim` / `boolElimPrim`; dead helpers `natDisc` / `noConfSuccZero` / `symNat`

## [0.9.0] - 2026-04-18

Descriptions become indexed. `Desc` and `μ` previously classified only `⊤`-indexed datatypes; they now take an arbitrary index type `I`, so `μ D : I → U` picks out a family of types rather than a single type. This is the machinery needed for length-indexed vectors, `Fin n`, propositional equality-as-a-description, and anything else that carries a value at the type level. The old unindexed combinators (`desc`, `mu`, `descRet`, `descRec`, `descPi`) remain as `⊤`-slice aliases, so the datatype macro and every downstream consumer — `Nat`, `List`, `Sum`, the category-theory library — keep working unchanged. A latent de Bruijn off-by-one in the value-level description eliminator is fixed en route.

### Added

- **Indexed descriptions** (`Desc I`) — `descI`, `muI`, `retI`, `recI`, `piI` at any index type. `descCon D i d` and `descInd D motive step i scrut` thread the target index; `VMu` / `vMu` / `mkMu` carry `I` alongside `D` and `i` so the kernel's `desc-con` CHECK rule recovers the index type from the surrounding `μ` without re-inferring the description
- **Acceptance coverage at non-`⊤` indices** — positive tests at `Desc Nat` and `Desc Bool` exercise `retI`, `recI`, and `piI` with a bool-dependent index function, plus an index-mismatch rejection at `Desc Bool` against a `Nat` literal and a `muI` at a matching target index
- **`J`-transport inside the `datatype` macro** — `dispatchStep` transports each constructor's step through the leaf `Eq ⊤ tt iArg` witness via the kernel's `J` primitive. Without Axiom K, MLTT cannot definitionally collapse `VRefl ≡ VNe(eq)`; routing through `J` is the principled transport
- **Pinned invariants for de Bruijn indices under `Π _:S. _` binders** — three tests assert that `interpOnArg` / `interpOnPi` / `allOnPi` quote their index-referencing Pi-domain codomain to the literal index value, not to the fresh-Var binding for `S`, when evaluated on a stuck `vDescElim` forced by `V.vNe 0 []`

### Changed

- **`desc-con` CHECK rule checks the description instead of inferring it** — `tm.D` is checked against `Desc ty.I`, using the index type recovered from the surrounding `μ`. Preserves strict bidirectional discipline: canonical intro forms at index positions (`tt`, `zero`, `refl`) remain checkable-only
- **`⊤`-slice aliases become thin wrappers** — `mu = D: i: muI unit D i`, `descRet = retI tt`, `descRec D = recI tt D`, `descPi S D = piI S (ann (λ_.tt) (S → ⊤)) D`, `desc = descI unit`. The datatype macro and the prelude descriptions `natDesc` / `listDesc` / `sumDesc` route through these aliases, so their behaviour is unchanged. `descCon` and `descInd` match kernel arities exactly (no alias): at `I = ⊤`, call sites write `tt` explicitly at the index position
- **Dead adapter branches deleted** — the `nat-elim` / `list-elim` / `sum-elim` branches in `hoas/elaborate.nix` were unreachable once `NatDT` / `ListDT` / `SumDT` migrated to the macro-generated elim path in 0.8.0. Removed

### Fixed

- **de Bruijn off-by-one in the value-level description eliminator.** Under a `Π _:S. _` binder inside `interpOnArg` / `interpOnPi` / `allOnPi` / `evOnPi`, the closure env is `[_, S, I]`, so references to the index type `I` must use `Var 2` — not `Var 1`, which resolves to `S`. Latent because `vDescElim` fully reduces on a concrete `VDesc*` and drops the intermediate Pi-domain annotations; observable only under `VNe + eDescElim` (e.g. `natDesc`'s inner `boolElim` stuck on a `Σ`-bound variable). Regression tests pin the invariant at three of the four sites

## [0.8.0] - 2026-04-17

A macro layer for user-defined datatypes lands on top of the kernel's description universe. Declaring an inductive type now means naming its fields; the macro compiles them to descriptions, flattens saturated and linear-recursive constructor chains to flat `desc-con` terms at elaboration time, and threads type parameters through a plain Π-binder so universe-typed components sit at the outside of the definition. `Nat`, `List`, and `Sum` are rebuilt through this surface. The category-theory example library is rewritten as a five-chapter guided tour that uses exactly the same macros users have.

### Added

- **Datatype macro layer** (`fx.types.hoas.datatype` / `fx.types.hoas.datatypeP` + `field`, `fieldD`, `piField`, `piFieldD`, `recField`) — declarative HOAS surface for single- or multi-constructor inductive types. Dependent fields receive a `prev` marker map so later fields reference earlier ones by name; `datatypeP` parameters thread through a `paramPi` (plain Π) binder, outside the description's `descArg`; duplicate constructor names and zero-constructor datatypes are rejected eagerly
- **Constructor-chain flattening at elaboration** — saturated (all-data) and linear-recursive (data-fields then one `rec`) shapes flatten to a single `desc-con` Tm (or a `genericClosure`-walked pyramid for the recursive shape). Deeply nested constructor applications (5000+ cons cells, 5000+ succs) type-check without blowing the C++ stack. Non-flattenable shapes fall through to the ann-wrapped λ-cascade path and behave identically to the pre-macro spelling
- **`W`-type datatype macro** — self-application inside `datatypeP` for M-like datatypes (`W A P` with `A : U₀`, `P : A → U₀`, `sup : Π a. (P a → W) → W`)
- **Dependent-field laws in the macro surface** — `fieldD`'s type function receives the full `prev` marker map, so associativity laws reference `prev.op`, category laws reference `prev.id` / `prev.comp`, etc. No projection chains
- **Category-theory library rewritten as a guided tour** — five chapters that build on each other:
  - `combinators.nix` — `sym`/`trans`/`cong` from J.
  - `arithmetic.nix` — `add` with seven verified properties.
  - `algebra.nix` — `Monoid` and `Category` as macro datatypes; instances `natAddMonoid`, `natCategory`; `compComm` stated categorically through `natCategory.comp`.
  - `functor.nix` — `MonoidHom` and `Functor` as macro datatypes; doubling packaged as both `doubleHom` (monoid homomorphism) and `doubleFunctor` (endofunctor on `natCategory`).
  - `yoneda.nix` — Yoneda's lemma as an equivalence of types.

### Changed

- **`Nat`, `List`, `Sum` use the macro surface for their µ/ctor/elim construction** — their HOAS forwarding stays unchanged from the user view; internally they flow through `datatype` / `datatypeP`, so every test-suite improvement on the macro improves the kernel primitives too
- **`examples/category-theory/algebra.nix`** — old nested-Σ `MonoidOf` / `CategoryTy` encoding replaced by macro datatypes. `natAddMonoid` and `natCategory` are exposed as HOAS records carrying both the component HOAS terms (`.op`, `.e`, `.comp`, …) and the bundled `(ty, impl)` pair that the kernel checks
- **Example-library invocations** — README and examples use `nix eval` rather than `nix-instantiate --eval --strict`

### Documented

- **`desc-arg` universe rule** — a principled note at check.nix's `desc-arg` rule explains why `S : U 0` is required, the parameter-lifting idiom that threads universe-typed components through `datatypeP` parameters, and that the category-theory library currently encodes `Obj` / `Hom` as parameters specifically because of this rule

## [0.7.0] - 2026-04-16

Six upstream PRs land alongside a kernel-level description universe. From @vic: Kyo-style handler rotation and a `scope` module for lexically scoped handlers (#8), `bind.*` operators for attrset/computation/function composition (#12), an `isComp` predicate on the computation ADT (#13), a first-class `state.update` (#15), and CI for pull requests (#16). From @sini (first contribution, landing via #14): effectful-resume handlers that can reply with a computation and have its effects spliced into the continuation. Thanks to both.

On the kernel side, `Desc` and `μ` join as primitives, and `Nat`, `List`, `Sum`, and `Unit` are rebuilt as HOAS descriptions on top — so further inductives can be added as ordinary data rather than new kernel nodes. Σ-η and ⊤-η conversion rules are added. A follow-up fix (`effectRotateSlow` now splices computation resumes correctly; see Fixed) closes a bug found during review of #14.

### Added

- **Kyo-style handler rotation** (`fx.rotate`) — handles matching effects and rotates unknown ones outward so an enclosing handler can resume them. Implements the law `handle(t1, suspend(t2, i, k), f) = suspend(t2, i, x → handle(t1, k(x), f))`. Credit: @vic (#8)
- **Scoped handlers** (`fx.effects.scope`) — `scope.run` installs handlers for a subcomputation and hides the scope's internal state, `scope.runWith` exposes it, and `scope.stateful` threads caller state across rotation. Credit: @vic (#8)
- **Effectful-resume handlers** — a handler may return a computation as its `resume` value; its effects are spliced before the pending continuation. Fast path uses `resumeCompOrValue` which dispatches on whether the resume is a computation. Credit: @sini (#14)
- **Description universe in the kernel** — `Desc` and `μ` as kernel primitives, with strict positivity guard, HOAS descriptor pieces (`descArg`, `descRec`, `descPi`, `descRet`), `descElim`/`descInd` elimination, and `interpHoas` for description interpretation
- **Nat/List/Sum/Unit rebound as HOAS descriptions** — kernel representations live entirely in the description universe; no dedicated kernel nodes for each type
- **Σ-η and ⊤-η conv rules** — `pair (fst p) (snd p) ≡ p` for Sigma and `tt ≡ _` for Unit, at the kernel conversion level
- **`bind.*` operators** — `bindAttrs`, `bindFx`, `bindFn` for monadic composition over attrset projections, computations, and Kleisli arrows. Credit: @vic (#12)
- **`state.update`** — effectful state transformer obeying `get >>= f >>= ({s, v}: put s >> pure v)`. Credit: @vic (#15)
- **`isComp`** — tag-based predicate on the computation ADT boundary. Credit: @vic (#13)
- **Pull-request CI** (`.github/workflows/flake-check.yml`) — runs `nix flake check -L` on PR events. Credit: @vic (#16)
- **CI and release badges** on the README

### Fixed

- **`effectRotateSlow` now splices computation resumes correctly.** When the depth ≥ 500 fast-to-slow threshold was crossed and a handler returned a computation as its `resume`, the slow path previously used `resumeWithQueue`, which treats the resume as a plain value. For the common case of an Identity continuation queue this wrapped the computation in `pure`, short-circuiting the loop with the inner effects unrun. Swap to `resumeCompOrValue` to match the fast path. Regression test: `effectRotationSlowPathEffectfulResume`.

### Changed

- **README** — rewritten intro, new `## Features` section covering effects-layer and MLTT kernel capabilities, old "No handler layering" limitation removed (superseded by `fx.effects.scope`), old "single source of truth" paragraph refocused on the real underlying limitation (`Certified` carries a Boolean witness, not an inhabitation proof)

## [0.6.0] - 2026-04-14

### Added

- **Opaque lambda** (`mkOpaqueLam`) — trust boundary for negative types (Pi). The kernel verifies domain match but cannot reduce the body. Follows the axiomatized literal pattern (`mkFnLit`/`mkAnyLit`). Conv uses `_fnBox` wrapper for thunk-identity comparison
- **Verified combinators** (`src/tc/verified.nix`) — `fn` combinator produces values carrying both a Nix callable (`__functor`) and an HOAS body (`_hoasImpl`). The kernel type-checks the full body, not just domain
- **Pi elaboration** — `elaborateValue` handles Pi types: verified values use `_hoasImpl` directly, raw Nix functions wrap in opaque lambda. `extractInner` returns Nix functions from `VOpaqueLam` and `VLam`
- **HOAS substitution for dependent Sigma** — `elaborateValue` Sigma case uses `body(â)` for correct dependent type computation, replacing the sentinel test heuristic
- **`_kernelPrecise` / `_kernelSufficient`** — orthogonal decomposition of the old `_kernelExact`. `_kernelPrecise` drives parent kernel building; `_kernelSufficient` drives guard decisions. Constructors compose both independently
- **`.diagnose` method** on all types — returns `{ kernel; guard; agreement; }` for independent kernel/guard reporting
- **Category theory library** (`examples/category-theory/`) — formally verified proofs running at Nix eval time. Proof combinators (sym, trans, cong) derived from J elimination; natural number arithmetic with 7 verified properties including commutativity; Monoid and Category as dependent sigma types with (Nat,+,0) instances; commutativity of composition in the endomorphism monoid; doubling endofunctor with functoriality proof via 5-step equational rewriting
- **Cross-cutting integration tests** — Record(Pi, Sigma(refined)), Maybe(DepRecord(dependent ListOf)), ListOf(Pi), Either(Sigma, Pi) verifying conjunction across compound types

### Changed

- **Universal conjunction** — every type with a guard uses `kernelDecide ∧ guard`. Replacement mode removed entirely from `effectiveCheck`
- **Polarity-aware elaboration** — positive types (Sigma, Sum, Nat) elaborate structurally; negative types (Pi) elaborate opaquely
- **Pair syntax** — `mkPair` is now 2-arg (Curry-style), removing the vestigial Church-style annotation that no computational layer maintained. Pair inference case removed from `check.nix`; use `Ann` for synthesis
- **Pi guard removed** — Pi with `kernelType` sets `guard = null`; opaque lambda domain check subsumes `isFunction`
- **Refined types** set `approximate = false`, enabling parent constructors to build precise kernels from refined children under conjunction
- **Constructor composition** — `Record`, `ListOf`, `Maybe`, `Either`, `Variant` split decisions into `allPrecise` (kernel building) and `allSufficient` (guard propagation)
- **DepRecord** `buildSigma` uses `_kernelPrecise` for precise nested Sigma kernels on non-dependent fields

### Removed

- `_kernelExact` — replaced by `_kernelPrecise` / `_kernelSufficient` with no backward-compatibility shim
- Replacement mode in `effectiveCheck` — all types use conjunction
- Pair inference case in `check.nix` — introduction forms check, not synthesize

## [0.5.2] - 2026-04-13

### Fixed

- **Soundness: refined type composition** — `refine`/`refined` exposed `_kernel` without marking themselves approximate, allowing `Maybe`/`Either` to bypass refinement predicates via the weaker kernel. `Maybe (refined "Nat" Int (x: x >= 0)).check (-1)` returned `true`. Fixed via Galois connection model: `_kernelExact` separates kernel availability from sufficiency, dual-mode conjunction/replacement semantics in `mkType`
- **`elaborate.decide` totality for records** — `elaborateValue` record case did raw `v.${field}` access without checking field presence. Missing-attribute errors are uncatchable by `builtins.tryEval`, making `decide` crash instead of returning `false`. Fixed with safe `fieldOf` helper

### Added

- `_kernelExact` field on all types — `true` when the kernel alone is sufficient for correct checking (no guard residual needed)
- `Record` per-field blame tracking via custom `verify` — delegates to each field type's `.validate` for recursive decomposition (context: `Record{age, name}.age`)
- `Variant` per-branch blame tracking via custom `verify` — delegates to active branch's `.validate`
- Composition soundness tests: deep composition, kernel-exact propagation, chained refinements, adequacy property

### Changed

- Type constructors (`Record`, `ListOf`, `Maybe`, `Either`, `Variant`) use `_kernelExact` instead of `? _kernel` for guard decisions and set explicit `approximate` flags
- `_kernel` is now always exposed on all types as the best kernel approximation; `kernelCheck` and `prove` remain gated on `!isApproximate`
- `Pi` without explicit `kernelType` omits redundant `isFunction` guard (conjunction with `kernelDecide` handles it)
- Locked nixpkgs via `nixpkgs.nix` for deterministic non-flake builds (@vic, kleisli-io/nix-effects#9)

## [0.5.1] - 2026-04-13

### Changed

- `Justfile`: `just test` now accepts an optional suite argument (`just test <suite>`) to selectively run a single test suite instead of all tests (kleisli-io/nix-effects#11, contributed by @vic)

## [0.5.0] - 2026-04-12

### Added

- `comp.nix`: Computation ADT module — single source of truth for `Pure`/`Impure` construction and elimination via `pure`, `impure`, `isPure`, and `match`. All modules now use these constructors instead of raw `_tag` attrset literals (closes #7)
- `kernel.pipe`: chain a computation through Kleisli arrows, threading results via bind (closes #6)
- `kernel.kleisli`: Kleisli composition `(a -> M b) -> (b -> M c) -> (a -> M c)`
- `queue.identity`: sentinel variant representing the identity continuation, letting the trampoline skip queue application for bare `send` effects
- Benchmark infrastructure: `nix run .#bench` / `nix run .#bench-compare` with named history, 3-run median, and comparison tables
- Benchmark examples: expression interpreter (`examples/interp`) and dependency graph evaluator (`examples/build-sim`) with scalable workload generators
- Benchmark stress tests: effectHeavy, bindHeavy, mixed, rawGC microbenchmarks for diagnosing bottlenecks
- Per-module test result reporting in `tests` output

### Changed

- Trampoline interpreter processes continuation queues inline via recursive `applyQueue` (depth-limited to 500, with genericClosure fallback for deep pure chains), keeping 1 genericClosure step per effect — 78% faster on effectHeavy 100k, 72% faster on mixed 100k vs 0.4.0
- `send` uses Identity queue instead of `singleton pure`, eliminating one wasted identity continuation application per effect
- `queue.viewlGo` fast-path: returns immediately when left child is already a Leaf, skipping genericClosure entry for the common case
- `queue.snoc` and `queue.append` handle Identity variant transparently
- All source modules migrated from raw `{ _tag = "Pure"; ... }` / `{ _tag = "Impure"; ... }` literals to `comp.pure` / `comp.impure` constructors, and from `._tag == "Pure"` checks to `comp.isPure`
- README and book reframed around the effect layer as the primary abstraction; removed Fire Triangle framing
- Book: trampoline guide updated to use `isPure`

### Fixed

- `build.materialize`: step-script env test matched exact quoting instead of presence

### Removed

- `examples/typed-derivation.nix` and the proof-gated derivation showcase wired through it. The example was contrived (the same policy is expressible with `assert`) and did not reflect how the library is actually used. The `api-server` package output and the book's "Proof-gated derivations" section in the Proof Guide are removed along with it. The `v.verify` verified-extraction pipeline it demonstrated is still available and documented in the remaining `examples/` and in the Proof Guide.

## [0.4.0] - 2026-04-06

### Changed

- **Breaking:** `mk`-wrapped functions are now directly callable, removing the need for `.value` (@vic, #1)
- Test extraction produces nested attrsets instead of flat dotted keys, enabling targeted `nix-unit` runs (@vic, #5)

### Added

- `CONTRIBUTING.md` explaining the josh mirror workflow
- `shell.nix`, `Justfile`, `tests.nix` for non-flake dev workflow (@vic, #4)

### Removed

- Unused flake inputs (@vic, #3)

## [0.3.0] - 2026-02-27

### Added

- Effects-powered build module (`fx.build`): typed build steps, eval-time validation, and derivation materialization
- `fx.build.BuildStep` and `fx.build.BuildPlan` Record types for describing build pipelines
- `fx.build.plan`: eval-time validation pipeline that type-checks steps and filters conditional steps via `when` predicates, collecting all errors without throwing
- `fx.build.materialize`: converts a validated BuildPlan + pkgs into a `pkgs.runCommand` derivation with per-step env isolation, source copying, and shell generation

## [0.2.0] - 2026-02-27

### Added

- Typed pipeline framework (`fx.pipeline`): composable stages with `mkStage`, `compose`, and `run`, wiring reader, error, acc, and typecheck effects with typed boundaries between stages
- Pipeline convenience re-exports: `ask`, `asks`, `raise`, `raiseWith`, `warn`, `pure`, `bind`, `map` for use inside stage transforms
- 14 inline tests and 2 integration tests for the pipeline module

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
