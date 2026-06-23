# Changelog

All notable changes to nix-effects are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- **`Certified` carries a genuine inhabitation proof, not a `Bool`.** `fx.types.Certified` was the subset type `Σ(x:A).{p:Bool | p ∧ P(v)}` — its second component stored the *result* of evaluating the predicate as a bare `Bool`, so a certified value held no transportable evidence and could not serve as propositional content downstream (no transport, no rewriting). It is now the subset type `Σ(x:A).P(x)` with `P` forced to a mere proposition, over two formers: a **decidable** predicate (a `fx.tc.kernel` `KernelPred` over the base carrier) reflects to `_kernel = El t`, with the witness the membership proof transported from the kernel decision `decide t x = true` through `Id` / `J` (the witness is the `Unit` inhabitant `tt`, `_kernelSufficient = true`); a **general** propositional family (`{ family; bridge; }`) carries a `Squash`-truncated inhabitant via `certifyProof`. The witness is always a real proof term.
- **`certify` is pure on a valid value; `certifyE` emits a typecheck effect only on rejection.** The old `certifyE` emitted a `typeCheck` effect even on success; it is now pure on a valid value (`{ fst = v; snd = <proof>; }`) and effectful only when the predicate rejects.

### Removed

- **The `Bool`-witness escape is gone — an uncertifiable predicate is rejected at construction.** A raw host-lambda predicate (no kernel decision procedure, no propositional `family` + `bridge`) can no longer be wrapped in a `Certified` that forges a `Bool` witness; construction throws, pointing to `fx.types.refinement.refined` — the honest, proof-free guard subtype for predicates the kernel cannot express. A consequence of the decidable arm: the base carrier must match the predicate's `KernelPred` carrier (a scalar `int` / `string`), so a guard over a compound value (e.g. a list-length predicate) is not a `Certified` — it belongs on `refined` or the compound type's own `validate`. The corresponding "Bool witness" entry under the README's *Known limitations* is removed accordingly.

## [0.14.0] - 2026-06-23

### Headline changes

#### Refinement and compound checks become kernel decisions

- **Every type carries an authoritative `ktype`.** `mkType` reflects a flat predicate-stack `KType` / `El` family — a base carrier paired with a stack of Boolean predicates — into a new `ktype` field on every type: the bare carrier reflection when the kernel alone decides the type, the refined code when the guard is a kernel-expressible witness, and `null` when it is not (lazy, `tryEval`-wrapped). The new `fx.tc.kernel` layer owns the family — the conjunction decider, the `validate` report stream, the failure encoding, the fold handlers, and a `reflect` layer whose `KernelPred` witness derives its host guard *from* its kernel predicate term, so the kernel decision and the value-side guard cannot diverge. Raw (non-kernel) guards stay opaque host lambdas with `ktype = null`.
- **Refined compounds decide in the kernel.** `Record` (closed and open), `ListOf`, `Variant`, `Either`, and `Maybe` now emit a non-null `ktype` and a kernel-decided `.check` whenever every child refinement is kernel-expressible, replacing the raw-lambda host guard. `Record` / `ListOf` fold their carrier description with `descCataBool`, a constant-`Bool`-motive `descInd` catamorphism (a derived theorem over the existing large eliminator — **zero new trusted primitives**); `Variant` / `Either` / `Maybe` fold the native nested-sum carrier directly with the pre-existing `sumElim`, each branch deciding its own child. Open records pass an openExtras-tagged carrier so the elaboration bridge drops undeclared fields before the fold runs, deciding exactly the declared fields. Any non-kernel-expressible child reverts the whole compound to the host guard; per-field / per-branch blame (`verify`) is unchanged.
- **The price of purity is a bounded constant.** The internalized `.check` is linear in workload and in structure size, with flat memory (`maxRSS` independent of workload; a ~480 MB working set GC'd between checks). Routing each decision through the kernel (`elaborate → check → eval → conv`) costs a ~300–400× constant over a pure-host guard at the same linear asymptotics — suited to build-time configuration validation, not a hot-loop runtime check.

#### Every structural walk is now depth-flat

- **The depth-flatness work reaches the auxiliary walks.** 0.13.0 made the kernel hot paths (eval / quote / conv / check) cost O(1) host call frames per step; 0.14.0 completes the job for the remaining structural walks that still recursed on the host C-stack. The HOAS force-analysis walk (`mentionsOf`), value rendering (`renderValue`), the typing-context depth / `eb` counters and cons-list readers, `hoasWhnf`, the `conv` neutral-spine and `Mu` / `Desc` / `Eq` arms, the desc catamorphisms, the ornament shape-diagnostic walk, `deriveGo`, `Sigma.verify`, and the dependent-sigma extractor (`extractInner`) are each now driven by a `genericClosure` worklist or a fuel-gated trampoline bounce. Every rewrite is byte-identical to its recursive predecessor (pre-order child order and accumulator semantics preserved), so deep terms (N ≥ 5000, some walks to 30000) type-check, render, and extract without overflowing the host stack.
- **Conversion routes by depth, not shape.** `conv` runs the native structural arms under a C-stack depth budget and bounces to the heap-bounded worklist machine only on budget exhaustion, instead of routing every goal through the machine unconditionally. The native arms and the machine share the `cPeel` / `elimGoals` decomposition (no drift), so the bounce handles any shape, while shallow goals — the dominant class — dispatch natively with no machine materialization. `conv` stays byte-identical and deep-conv stress stays total at `max-call-depth=10000`.

### Added

- **`fx.tc.kernel` namespace** — the flat predicate-stack `KType` / `El` family, the conjunction decider, the kernel-internal `validate` report-stream producer, failure encoding, the fold handlers, and a `reflect` layer (carrier reflection plus the `KernelPred` witness whose guard is derived from its kernel predicate term). `validateK` is the kernel-internal decision; `validateEl` is its membership-witness dual — given `x : β t` it produces the dependent witness `El t` when the decider accepts (transporting `decide t x = true` through `Id` / `J`) and otherwise aborts over `EffError`'s strict `Void` response, the continuation discharged by `absurd`, so no witness is ever forged on rejection.
- **`ktype` on every type** — the authoritative kernel type, exposed lazily on the `mkType` surface.
- **Kernel-internalizing refinement predicates** — `positiveInt`, `nonNegativeInt`, `inRangeInt`, `eqInt`, and `oneOfStr` carry a non-null `ktype` and a kernel-decided `.check`; all are exposed on `fx.types`. `nonEmpty` / `matching` stay raw lambdas (they need string introspection the kernel lacks).
- **`intLe` / `intEq` kernel primitives** — host-backed `int_ → int_ → Bool` opaque-carrier comparators parallel to `strEq`. `intEq` is symmetric (one `EIntEq` frame); `intLe` carries the neutral operand's side via distinct `EIntLeL` / `EIntLeR` frames so `intLe a b` and `intLe b a` stay non-convertible. The Int refinement vocabulary is re-expressed over the `int_` carrier through these plus the O(1) `intLit` bridge.
- **`descCataBool`** — a constant-`Bool`-motive `descInd` catamorphism in `hoas/combinators.nix`, exported via the module surface; the fold engine behind the internalized compound predicates.
- **`EffTypeCheck` effect and kernel-term handlers** (`experimental.desc-interp`) — one `report(reason, path, carrier, passed)` op with a `Unit` response, plus six handlers over the FreeFx trampoline: five resume strategies (collecting / logging / firstN / summarize / pretty) as bare Σ-State-Unit terms and `strict` as a `UniRet` `Sum` with conditional-throw dispatch. Each ships an `atType_*` bridge record; per-handler `H.refl` shortcut-law lemmas certify that each handler reduces to the residual its fast-path emitter targets. A `byReason` assoc-list `summarize` variant keys on the reason token via `strEq`.
- **`Position` / `Path` datatypes** — a `Position` over the value-side descent alphabet (`Field` / `Elem` / `Tag` / `Tuple`) and `Path = List Position`, threaded through the typecheck `report` op as an internalized, eliminable coordinate (field-name as a `strEq`-comparable carrier, index as a `Nat`; rendered segment text stays host-side). Surfaced on the public API.
- **Stack-safety stress gates** — depth-axis bench probes for the structural walks that recurse on the host stack (conv neutral-spine, `renderValue`, the μ extractor, `lower` on an inferred app spine, `elaborateForCheck`, the desc catamorphisms, the ornament shape-diagnostic walk, `deriveGo`, `Sigma.verify`). Each forces a `control` depth (green) and a `witness` depth (red until heap-driven), classified at the process boundary in its own capped subprocess under the pinned Nix and an explicit `max-call-depth`, kept out of `meta.nix` so the alloc / cpu runner never enumerates the intentionally-overflowing leaves. Plus latent stack-safety guards for quote read-back spines.
- **Soundness suite for the internalized refinement check** — pins signed-int literal-bridge order / equality faithfulness, predicate-stack composition as conjunction, the check law (host carrier gate conjoined with the kernel decision at the bridged value), decision / structural-check agreement over record / list / option / sum / variant, the fail-closed degradation arms, and agreement among the kernel decision and the collecting / strict `validate` runs.

### Changed

- **Compound `verify` delegates to each child's `validateAtF`.** The four compound constructors (`Record` / `RecordOpen`, `ListOf`, `Either`, `Variant`) previously set `verify = deriveCheck self._kernel`, which walked the predicate-erased forgetful kernel carrier and so silently accepted guard-violating children that `.check` rejects — a `validate` / `check` disagreement and soundness gap. Each `verify` is now a child-delegating fold that descends each child through its own `validateAtF` (fuel threaded for the trampoline bounce), making the child's guard authoritative and mirroring the already-sound `Sigma` verify. Blame paths (`Elem` / `Field` / `Tag` / missing-field) are preserved.
- **Int refinement comparators are O(1), not O(value).** The Int vocabulary (`positiveInt` / `nonNegativeInt` / `inRangeInt` / `eqInt`) is re-expressed over the `int_` carrier via `intLe` / `intEq`, replacing the unary `Nat` / `IntZ` comparator path whose succ-tower bridge was O(value) and OOM'd on large Int fields. The now-unused `leb` / `eqb` / `intzLeb` / `intzEqb` / `*Nat` / `*IntZ` refinement comparators are retired.
- **The guard dispatch is hoisted out of the per-value check**, `diagnose` no longer applies a witness directly, and contract diagnostics render a labelled predicate for derived guards.
- **The bench baseline is regenerated to 0.14.0 — to capture improvement, not to absorb a regression.** `bench/history/baseline.{json,md}` is refreshed to a quick-tier capture of this release (5 runs, 1 warmup, Nix 2.31.4, name `release-0.14.0`); the 0.13.0 baseline is archived at `bench/history/baseline.release-0.13.0.{json,md}`. 0.14.0 does **not** regress against the 0.13.0 baseline — the `--alloc-only` gate passes with **zero hard fails** and zero step-axis fails, and the conv depth-gate fix lands the conv-heavy workloads (`alg-list-to-vec-check`, `ornCompose-check`) net-below the 0.13.0 figures. The refresh promotes those improved numbers to the new gating floor, so subsequent work is measured against the shipped allocation profile rather than retaining the pre-improvement headroom. The recorded Nix version is unchanged (2.31.4), so the counters remain directly comparable across the bump.

### Fixed

- **`verifyAndExtract` evaluates the checked term.** It type-checked the impl, discarded the checked term, then re-elaborated the original with no expected type — leaving checking-only metavariables (a polymorphic list's element type) unsolved, so it threw `unsolved-meta` on bare `cons` / `nil` and duplicated elaboration superlinearly. It now evaluates the checked term, whose metas are already pinned by checking.
- **Universe-level datatype parameters stay bare.** `annotateParamArgs` ascribed every substituted parameter uniformly as `ann a (resolveKind …)`, turning a level param into `ann <level> level` — a vacuous ascription that made the level opaque to `sameLevelSyntax` / `levelAsInt` and defeated `LiftAt` / `liftAt` idempotence, so an indexed / parametric family used as a `Sum` summand had its payload spuriously `lift`-wrapped, leaked to a terminal `lower` with unsolved implicits, and conv-failed (expected μ, got Π). Only genuine type / term params are now ascribed; level-sort params stay bare. Restores checking of `Sum` / `Dec` over indexed (`Le`) or parametric (`List`) family summands.
- **`extractInner` forces the dependent-sigma `snd` type to WHNF** before descending, so the per-level `instantiate` chain stays O(1) on a head-normal input instead of accumulating an O(depth) chain that overflowed on force. Byte-identical (the `seq` only forces existing work earlier); the sole observable change is termination at depth.
- **`boolDesc` is exported from the HOAS surface.** `vStrEq` deep-forces `boolDescV` when `conv` reduces a concrete `strEq`; `boolDesc` was the lone prelude `*Desc` former missing from the public export, so the force threw `attribute boolDesc missing`.
- **`VThunkTm` read-site force discipline.** The eager eval overlay's `vAppF` and the direct evaluator's `vFst` / `vSnd` read a machine-minted `VThunkTm`'s `.tag` (or projected it) without forcing; they now force first, mirroring the kernel paths. `VThunkTm` is minted only by the kernel machine and is meta-blind, so forcing it at any read-site that opens a machine-built closure env is always safe.
- **The bench entry point resolves `pkgs` / `lib` from `pins.nix`**, not the ambient `<nixpkgs>` channel, so a standalone `import ./bench {}` is reproducible and matches the canonical paths.

### Performance

- **The depth-flat rewrites are byte-identical and add no complexity class.** Each stack-safety change (force analysis, `renderValue`, typing-context counters, `hoasWhnf`, conv arms, desc catamorphisms, ornament diagnostic, `deriveGo`, `Sigma.verify`, `extractInner`) preserves its predecessor's output byte-for-byte; the only observable change is termination at depth under a bounded host stack. The `deriveGo` / `Sigma.verify` / conv bounces stay native for shallow walks (the dominant case) and defer only past their budget, so common-case cost is unchanged.
- **Conversion improves on conv-heavy workloads.** Routing `conv` by depth rather than unconditionally through the machine removes the per-goal routing peel that recomputed the machine's first `cPeel` and lets shallow goals dispatch with no machine materialization. On the quick-tier conv-heavy workloads this lands net-below the 0.13.0 baseline on the deterministic Σ-bytes axis (the list-to-vec and ornament-compose checks drop; the surface-elaborate workload holds flat), with the step axis unchanged.
- **The internalized compound `.check` is linear with flat memory.** Measured linear in workload `M` and structure size `N` (per-leaf marginal ≈ 1.0–1.2 ms; per-check kernel fixed overhead ≈ 5–8 ms), with `maxRSS` independent of workload. The kernel route is a bounded ~300–400× constant over a pure-host guard — the deliberate, opt-in price of a kernel-decided check, paid only where a refinement is kernel-expressible.

## [0.13.0] - 2026-06-14

### Headline changes

#### Every kernel hot path is depth-flat

- **The evaluator is a CEK-style abstract machine.** `evalF` / `vAppF` / `instantiateF` / `vDescIndF` / `vEverywhereDF` and the desc-con trampoline are driven by a `builtins.genericClosure` + `builtins.foldl'` state machine (`src/tc/eval/machine.nix`) over an explicit frame/continuation algebra, replacing direct mutual recursion — user-level recursion depth N produces O(1) libnix call frames per evaluator step, with O(N) work spread over O(N) driver iterations. `quote` and eval hand off end-to-end inside the same machine, and eliminator dispatch (including `lower` elimination and the bootstrap eliminators) routes through machine frames.
- **Evaluation enters through a depth-budgeted hybrid front end.** `evalF` routes through `src/tc/eval/direct.nix`: shallow structural terms run direct `mkValueF` recursion under a budget threaded through sub-evaluations, bottoming out in the machine at exhaustion, so libnix stack depth stays O(budget) at any term depth. The description-eliminator family (`desc-ind`, `interp-d`, `all-d`, `everywhere-d`) and desc-con chains always run through the machine, preserving the machine-internal value invariants and the single cert-construction path.
- **Conversion and the bidirectional checker are equally flat.** `conv`'s recursive arms are replaced by `runConvF`, a spine-peeling sub-machine exposing structural children as direct pointers into the forced value, with a BFS frontier over sibling goals; binder descent (`VPi` / `VLam` / η / `VSigma`) and the level normalizer (`flattenLevel` / `dedupLevel`) are flat. The checker threads blame as a flat frame stack in handler state and yields recursive entries to the trampoline, so `checkType` on right-nested Pi and `checkTm` on deep lam/let pass at N=10000; surfaced blame traces are byte-identical and N retained frames cost O(N), not O(N²). `VDescCon` linear chains use a flat chain-form (`vDescConChain` / `_layers` / `_shape = "linearChain"`) in place of the deep nested-attrset chain, unblocking 5000-deep constructor and evaluation workloads that previously overflowed.
- **Net effect.** Evaluation, quoting, conversion, and type checking all cost O(1) host call frames per step regardless of user-term depth; residual host-stack recursion is confined to auxiliary walks (metavariable collection, extraction/reflection, generic-programming helpers) whose depth follows type/metadata structure, not user-term depth. Public signatures of `evalF` / `vAppF` / `instantiateF` / `vDescIndF` / `quote` / `nf` / `conv` are preserved byte-for-byte; no consumer call site changes.

#### Representation-invariant bench gate

- **The gate verdict is the Σ-bytes aggregate** (values+envs+sets+list `.bytes`, code-size excluded; tolerance 50‰) plus a deterministic step axis, replacing the old max-‰-across-per-counter rule — which a faithful representation change could trip by relocating allocation between counters at near-flat total heap. The per-counter max survives as a safety net behind an absolute floor (`allocAbsoluteFloor`): a counter fails only when it moves both >5‰ and ≥ floor. Failing workloads render a signed blame section (risers/drops by |‰|). Parallel counted CEK and conversion drivers (production paths untouched) gate exact transition counts against generated slope contracts — deterministic, so any slope move is a real work regression. 30 nix-unit fixtures pin classify, the floor, both axes, and the markdown serialiser.

### Added

- **Verified `v.elimData` / `v.matchData` wrappers.** To a user `H.datatype` what `listElim` / `matchList` are to lists: branch binders built from datatype metadata, each branch body ann-wrapped against the motive image at its constructor (branches checked, not synthesised), handlers keyed by constructor name and curried over fields then one induction hypothesis per recursive field. `elimData` takes a dependent motive; `matchData` is the constant-motive case. Non-parametric datatypes only.
- **Depth-flatness and depth-scaling regression coverage.** Eliminators nested N=1000, checker `checkType` / `checkTm` at N=10000, conversion sibling/balanced-depth shapes — a depth regression overflows max-call-depth well before these bounds; `bench/workloads/tc/eval-depth-scaling.nix` exercises evaluator depth across desc-ind, vAppF, and conv chains.
- **CEK step-count and counted-conversion work axes.** `runMachineCountedF` reports exact CEK transition counts at two depths and `runConvCountedF` counts dispatched conversion goals per BFS round (both sibling drivers; production paths untouched, zero per-step cost), each checked against generated slope contracts (`budgets.toml` `[stepSlopes]`, tol 5‰; values spliced from `bench/runner/step-budgets.nix`, never hand-typed). Probes share term builders with the alloc workloads so both axes gate identical terms; the `VDescCon`-not-a-peel-arm coverage boundary is documented in `bench/step-probes.nix`.
- **Peak-heap soft-warn axis.** `gc.heapSize` (≈ peak committed heap) is threaded through the run summary; a rise above `peakHeapWarnPct` (25%) is an advisory warning, never a hard fail (peak live heap is GC-timing-nondeterministic). The runner pins `GC_INITIAL_HEAP_SIZE=8M` so the axis compares peaks, not the GC's starting-heap floor (an ambient ~403 MB default clamped every workload under it); the pin is alloc- and step-neutral, recorded as `gcInitialHeapSize` for provenance.
- **dnzl joins the ecosystem section.** [dnzl](https://github.com/denful/dnzl) by @vic — an actor system for Nix using nix-effects streams for inbox and sidecar channels, behaviours as plain Nix functions stream-folded over state.

### Changed

- **nixpkgs and `nix-unit` pins are unified in `pins.nix`.** `nixpkgs.nix` and `nix-unit-pinned.nix` are replaced by a single `pins.nix` consumed by the flake, shell, and test entry points; `nix-unit` is pinned to 2.34.0.
- **Post-CEK-recovery baseline is now active.** `bench/history/baseline.{json,md}` was regenerated (quick tier, 5 runs, 1 warmup) after the recovery work below, superseding the 0.12.0 baseline for current gating; the 0.12.0 gold baseline is preserved at `bench/history/baseline.gold-0.12.0.{json,md}`.

### Fixed

- **WHNF-forcing boundaries in conversion, elaboration, and read-back.** Operands of `vStrEq`, meta-bearing annotations, and types force to weak-head normal form before tag dispatch; meta-bearing closures open via the overlay instantiator in `tc.elaborate` (kernel instantiation would crash reading `.tag` on a metavariable); `extract` and `quote` read-back honor WHNF boundaries; run-state results force to WHNF.
- **Deferred desc-ind motives force before their domain is read.** A computed motive arrived as a deferred term record; consumers demanding the elimination's index type — quoting a stuck `everywhere-d` spine, conversion touching an IH binder domain — threw a spurious `requires VLam motive (got VThunkTm)` on legal programs. The motive now forces at the point of demand inside the lazy index-type binding (memoized, one shared machine run).
- **Datatype names survive nested extraction.** `extractInner` no longer decodes a named datatype nested inside another type positionally as `con<i>` / `_field<j>`: sum arms recover from the app-spine and record fields thread the constructor's declared field types, falling back to `reifyType` only for dependent or metadata-less fields.
- **`fieldTyOf` strips the `monoAt` ann artifact for declining-shape constructor args**, so an instantiated data field type no longer reads as `ann (listOf string) (u 0)` and drops CHECK→INFER. Centralized in the sole field-type reader so consumers cannot reintroduce the gap.
- **Corrected the 0.12.0 "Handler-state transport via Thunk" note** that misattributed the `deepSeq` hazard. `forceValueDeep` does carry an identity seen-set (a self-referential attrset terminates — verified across Nix 2.3.18, 2.18.8, 2.24.8, Lix 2.91.1, 2.35pre); the Thunk carrier is still required for lazy graphs that regenerate a fresh object on each force (uncatchable overflow), real-derivation full-closure force cost, and the guard-less `api.extractValue` walk on raw cyclic values. The "uncatchable by `tryEval`" point stands. Rationale corrected in `book/src/trampoline.md`; pinned by cycle/throw tests in `src/state/thunk.nix`.

### Performance

Allocation figures are evaluator-deterministic Σ-heap-bytes excess (the gate's verdict axis) relative to the 0.12.0 baseline; the step axis holds at Δ0 across every entry. CPU and wall-clock timings are single-host samples — indicative only.

- **The depth-flat machinery has an allocation cost.** At first landing the full typechecker suite cost ~4× CPU and 2.4–4.4× allocations versus 0.12.0 (worst blame/trampoline-dense workloads ~11×; pure deep chains only ~+16% CPU); the `effects.*` layer is unaffected. This is the price of O(1) host call-stack depth.
- **Recovery brought the bulk of that back.** Across the round: `bindP` chain positions force only on the error path; desc-con chain layers are attested individually; the machine's per-transition/per-entry ceremony is cut (state passed directly, the step chain fused, states/konts built literally, deferred-term forces memoized, `envNth` unrolled to i≤7 and the env spine inlined past helper frames); shallow and eliminator evaluation ride the direct path; conversion sheds per-goal/per-level setup and compares closed levels by nat denotation; success-path transits fuse across `bindP` and the effects queue while error-free chain layers bypass it; checker entries stay Pure under a fanout-divided entry budget; the machine's sub-evaluator builds 20 bounded-position tags directly; certified desc-con chain-prepends, nocert `descDesc` builds, and `VDescCon` interpretation run off-machine; conversion dispatch sheds its binder classifier and a redundant re-force; and scan-provably meta-free `checkHoas` / `inferHoas` runs route straight to the kernel. Each lever was audited byte-identical (dual-run instruments over the suite and all 91 quick-tier workloads). Most quick-tier workloads recovered below the 0.12.0 baseline or within the 50‰ tolerance — including the first green flips on the elaboration-heavy cluster (`stateChain.s1k` / `s1kShort`, both builder chains, `deep-app`, `functional-synthesis`, `ornForget-check`).
- **Lower live-peak on equality-heavy and composed-handler laws.** `checkHoas` shares equality-witness normal forms across its three type builds (a composed-handler law region drops ~1.76 GiB → ~960 MiB live peak); kind-validated ann params skip description-body re-materialization.
- **Remaining gap — the architectural floor.** Three kernel-heavy quick-tier workloads still exceed the 50‰ Σ-bytes tolerance versus the 0.12.0 gold baseline: `alg-list-to-vec-check` +382‰, `tc.decidable.leDiag50` +236‰, `ornCompose` +186‰. Measured ceilings — a bracket-free checker, the full gold checker discipline swapped onto the current evaluator, and the depth-budget knob — prove this is the floor of the stack-safe CEK design rather than a missed optimization: gold's lower allocation came from machine-free native recursion that consumes O(term-depth) host stack (overflowing on deep terms), and even reverting the entire checker to gold's discipline leaves both workloads above tolerance, the residual being eval-during-check CEK state-record overhead shared with `leDiag50`. The excess is the bounded, deliberate cost of O(1) host call-stack depth.
- **Net effect on the common case.** Despite the higher allocation on those three workloads, the round is a net win on real-world cost: the typechecker test suite runs ~24 s faster than 0.12.0 while covering 255 more tests — the recovery levers, especially routing meta-free elaboration straight to the kernel, more than pay for the depth-flat overhead on the common case.

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
