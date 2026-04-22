# Changelog

All notable changes to nix-effects are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

The benchmark harness is rebuilt around dual-metric measurement. Allocation counters from `NIX_SHOW_STATS` (deterministic for a fixed Nix evaluator + nixpkgs) are the primary, structural axis; cpu.p50 / cpu.p95 percentiles are the secondary, environmental axis. `bench/workloads/` collects the existing effects-kernel workloads (`effects.interp.*`, `effects.buildSim.*`, `effects.stress.*`) alongside new type-checking-kernel workloads (`tc.conv.*`, `tc.check.*`, `tc.infer.*`, `tc.quote.*`, `tc.elaborate.*`, `tc.e2e.*`). `bench/lib/{measure,gate,format}.nix` produces pure sampling, classification, and markdown; `bench/runner/` exposes `bench-run`, `bench-compare`, `bench-gate`, `bench-calibrate`, and `bench-open-regressions` as flake packages under `packages.<system>.bench-*`. The committed `bench/history/baseline.{json,md}` is the rolling reference and `bench/budgets.toml` carries per-workload cpu budgets plus a `noiseLimited` array for workloads whose cpu.p95 spread is structurally too wide for cpu gating. Commit trailers `Perf-regression: <workload>, <reason ≥20 chars>` acknowledge intentional regressions; the gate demotes matching hard-fails into an "overridden" bucket.

A `bench-gate` CI workflow runs on every push to main and every pull request touching `src/**`, `bench/**`, `flake.{nix,lock}`. It gates **alloc-only**: shared runners and the developer workstation that captured the baseline have different hardware profiles, so cpu percentage deltas aren't meaningful across them, but allocation counters — as evaluator-deterministic byte counts — are a valid universal gate. A shell-level and Nix-level pair of guards refuses to compare a baseline captured on one Nix version against a current run on another, since allocation counts can shift under evaluator changes unrelated to the contributor's code. Workloads in `noiseLimited` retain alloc gating but are exempt from cpu gating even on the workstation path.

Bench runners pin `NIX_PATH=nixpkgs=${pkgs.path}` to the flake-locked nixpkgs store path instead of resolving `<nixpkgs>` from the ambient channel. The host's channel version of `lib` previously entered workload evaluation and produced hardware- and developer-specific allocation counts even for identical code; the pin closes that hole so alloc determinism actually holds across machines with the same `flake.lock`.

Type validation threads a structural `path` through the `typeCheck` effect, so the collecting handler now reports deep blame as a list of descent segments rather than a single opaque type name. `Record`, `ListOf`, `Variant`, and `Sigma` recurse via a new `validateAt path v` alongside the existing `validate v`; the 1-arg API is unchanged, and `ListOf` now delegates to `elemType.validateAt` so record elements decompose into per-field effects instead of blaming as a whole.

The kernel retires `Bool`, `Void`, and `absurd` as primitives. The plus-coproduct and `Fin 0` from the indexed-description layer now carry them: `H.bool = μ ⊤ (plus (retI tt) (retI tt)) tt`, `H.void = Fin 0`, `H.boolElim` derived via `descInd` on `boolDesc`, and `H.absurd` routed through `absurdFin0` — a direct `J`-transport at motive `λx _. app (natCaseU P unitPrim) x`, eliminating the `natDisc → noConfSuccZero → absurdPrim` chain. Twelve kernel dispatch cases, six `Tm` constructors, four `Val` constructors, and two `Elim` frames disappear from the TCB. User-facing API (`H.bool`, `H.true_`, `H.false_`, `H.void`, `H.boolElim`, `H.absurd`, `v.if_`, `v.true_`, `v.false_`) is unchanged — they are the same combinators, now derived. `VUnit`/`VTt` remain as the irreducible bootstrap singleton.

The datatype macro gains an indexed variant. `datatypeI name I consList` and `datatypePI name params indexFn mkCons` compile indexed families alongside the existing ⊤-indexed `datatype` / `datatypeP`, with `conI name fields targetIdx` and `recFieldAt name idxFn` as the spec constructors for non-trivial target indices and recursive calls at non-default indices. `Fin : Nat → U`, `Vec A : Nat → U`, and the propositional-equality family `Eq A a : A → U` are reimplemented as macro invocations (`FinDT`, `VecDT`, `EqDT`) and the hand-written `finDesc` / `fin` / `fzero` / `fsuc` / `finElim`, `vecDesc` / `vec` / `vnil` / `vcons` / `vecElim`, `eqDesc` / `eqDT` / `reflDT` bodies in `combinators.nix` collapse into forwarders over the macro outputs. Single source of truth for indexed families: the description, type family, constructors, and eliminator all flow through `datatypeI` / `datatypePI`, and every internal consumer (`absurdFin0`, `natPredCase`, `vhead`, `vtail`, `eqToEqDT`, `eqDTToEq`, `eqIsoFwd`, `eqIsoBwd`) continues to resolve through the macro-bound names.

### Added

- **Dual-metric bench harness** (`bench/{lib,runner,workloads}/`) — `bench-run` samples each workload N times, aggregates via `measure.summarize` into alloc counters and cpu percentiles, writes `bench/history/<name>.{json,md}`. `bench-compare` / `bench-gate` classify baseline-vs-current via `bench.gate.gate`; `bench-gate` additionally scans `git log --since <range>` for `Perf-regression:` trailers and validates them (rejects wildcards, unknown workloads, reasons <20 chars). `bench-calibrate` drives runs at elevated sample counts, computes per-workload cpu budgets as `ceil((p95 - p50) / p50 × 1.5 × 100)` (floored at 3%), and preserves a `noiseLimited` array across re-calibration via `--existing-budgets`. `bench-open-regressions` audits `Perf-regression:` trailers against current metrics, classifying each as RECOVERED / OPEN / UNMEASURED. All five runners exposed as flake packages (`.#bench-run`, `.#bench-compare`, `.#bench-gate`, `.#bench-calibrate`, `.#bench-open-regressions`)
- **Type-checking-kernel bench workloads** (`bench/workloads/tc/`) — microbenchmarks on `conv` (identical-shallow/deep, α-equivalent, β-distinct, μ-heavy, plus-heavy), `quote` (closed, open, stuck on `VNe`), `check` (nat-chain-5000, list-chain-5000, macro-field), `infer` (100-deep app spine), `elaborate` (saturated-flatten, linear-recursive), plus end-to-end workloads covering the full 1014-test tc suite, per-module breakdowns, the category-theory library, and a 20-constructor `datatypeP` macro stress
- **`bench-gate --alloc-only`** flag — ignores the `[cpu]` table of `--budgets` and gates only on allocation counters. Used by CI where the baseline was captured on different hardware than the PR runner. Local developers keep the full dual-metric gate
- **Nix-version guard in `bench-gate`** — refuses to compare a baseline captured on one Nix version against a current run on another. The shell driver fast-fails with a clean CLI message; `finalize-gate.nix` re-asserts the invariant for non-CLI callers
- **`.github/workflows/bench-gate.yml`** — alloc-only CI gate on every push to main and every PR touching `src/**`, `bench/**`, `flake.{nix,lock}`. Captures a `pr-<sha>` run, gates against the committed baseline, publishes the verdict to the job step summary, and uploads `pr-*.{json,md,gate.md}` as artifacts. `Perf-regression:` commit trailers demote matching hard-fails to "overridden"
- **`datatypeI` / `datatypePI` indexed-datatype macros** — compile indexed inductive families `I : U` into a record exposing `.D : Desc I`, `.T : Π(i:I). U`, per-constructor fields `.<name> : Π(params). Π(fields). μ I D (targetIdx prev)`, and `.elim` on top of `descInd`. Spec constructors `conI name fields targetIdx` and `recFieldAt name idxFn` land alongside the existing `con` / `recField`. `datatypeI` is monomorphic over a user-supplied `I`; `datatypePI name params indexFn mkCons` threads an outer Π-over-params and a parameter-dependent index type (needed for `Eq A a : A → U` where the index type is the parameter `A`). The ⊤-indexed `datatype` / `datatypeP` continue to work verbatim — internally they lift `con` specs to `conI` with default `targetIdx = (_: ttPrim)` and delegate to the indexed path
- **`FinDT` / `VecDT` / `EqDT` scope bindings** in `hoas/datatype.nix` — macro-derived instances of the three canonical indexed families, mirroring the existing `NatDT` / `ListDT` / `SumDT` pattern
- **`fx.effects.hasHandler : String → Computation Bool`** — runtime query for whether a handler with the given name exists in the current scope. Dispatched by the trampoline via a scope-aware `localHandler` shim: returns `true` when the name is bound in the nearest enclosing `handle`/`scope.run`, rotates outward through unhandled scopes, and defaults to `false` at the root. **Reserves the effect name `"has-handler"`** — user handlers bound to that name are shadowed by the internal dispatch and should be renamed
- **Deep handler semantics for effect rotation** (Plotkin & Pretnar 2013) — when an effect rotates past an inner `scope.run` to an outer handler, and the outer handler's `resume` is itself a computation, that computation's effects now route back through the inner scope's handlers first. Previously the shallow path had the sub-effects bypass the inner scope, producing unhandled-effect errors for patterns like `scope.run { A = … } (send "B")` where the outer `B` handler resumes with `send "A"`. The fix tags the rotation continuation's queue with `__rawResume` and routes raw resumes through `effectRotate` against the inner handler stack
- **Path-threaded `typeCheck` effect** — the effect param grows a `path : [String]` field. Collecting-handler state grows `{ path }`; logging-handler state grows `{ path }`. Strict handler's throw message renders `path` when non-empty, falls back to `context` otherwise
- **`Type.validateAt path v`** — public method on every type for effectful validation with an explicit path prefix. `validate v` is the 1-arg convenience that delegates to `validateAt []`. Constructors (`Record`, `ListOf`, `Variant`, `Sigma`) thread path by appending one segment per recursion (field name, `"[i]"` for list elements, variant tag, `"fst"`/`"snd"` for `Sigma`)
- **`verify` callback contract** — custom verifiers now take `self: path: v: Computation`. Previously `self: v: Computation`

### Changed

- **Bench runners pin nixpkgs to `${pkgs.path}`** (the flake-locked store path) instead of resolving `<nixpkgs>` from the ambient channel. Workload evaluation now uses the same `lib` that built the runner derivation, so allocation counts are reproducible across machines that share a `flake.lock`. Affects `bench-run`, `bench-compare`, `bench-gate`, `bench-calibrate`, and `bench-open-regressions`
- **`open-regressions` audit is data-driven, not trailer-pair-based.** Previously a single `Perf-recovers-in:` trailer in the log range coarsely marked every outstanding regression as recovered. The runner now invokes the gate against supplied baseline/current pairs and classifies each `Perf-regression:` trailer by the workload's current gate status: `pass` → RECOVERED, `fail_*` → OPEN, missing → UNMEASURED. No external task-tracker references
- **`finalize-gate.nix` asserts `[cpu]` and `noiseLimited` disjointness.** A workload present in both would silently prefer the cpu budget and mask the noise-limited declaration; the finalizer now throws with the offending workload names
- **Fin / Vec / Eq-as-description preludes rebound through the datatype macro.** `finDesc` / `fin` / `fzero` / `fsuc` / `finElim`, `vecDesc` / `vec` / `vnil` / `vcons` / `vecElim`, and `eqDesc` / `eqDT` / `reflDT` in `hoas/combinators.nix` are now η-expanded forwarders over `FinDT` / `VecDT` / `EqDT` fields. Single source of truth for the indexed-family machinery; `absurdFin0`, `natPredCase`, `vhead`, `vtail`, `eqToEqDT`, `eqDTToEq`, `eqIsoFwd`, and `eqIsoBwd` keep their references unchanged. ~260 lines of hand-written description / constructor / eliminator bodies collapse into 25 lines of forwarders
- **Chain-flatten path in `hoas/elaborate.nix` generalised to `I ≠ ⊤`.** `buildTagInterpTms`'s signature widens to carry the index type `I` and per-summand `targetIdxVal`; `flattenCtor` derives a `prev` attrset from the ctor's HOAS field args, computes each layer's `targetIdxHoas = mono.targetIdx prev`, and emits `mkDescCon dTm targetIdxTm payload` with the correct i-slot and per-summand `interp` types. The ⊤-sugar invariant is preserved: under `mono.I._htag == "unit"` the tags are computed once per chain (`sharedTags`), preserving the O(1) cost for 5000-deep list / nat chains; only genuinely indexed families recompute per layer. The six scalar callers (`zero` / `succ` / `nil` / `cons` / `inl` / `inr`) pass `unitPrim` / `ttPrim` explicitly
- **`absurdFin0` discharges `Fin 0` via direct `J`-transport.** At motive `λx _. app (natCaseU P unitPrim) x`, base `ttPrim` — `natCaseU P unitPrim` maps `zero → P` and `succ → Unit`, the `J`-base `tt : Unit = natCaseU P Unit (succ m)`, and the result `natCaseU P Unit zero = P`. No `Void` intermediate; the `natDisc → noConfSuccZero → absurdPrim` chain is gone
- **StrEq's INFER rule returns the derived bool.** Return type is `μ ⊤ (plus (retI tt) (retI tt)) tt` instead of the retired `VBool`; `vStrEq` on two concrete string literals produces the plus-encoded `VDescCon boolDescV VTt (VInl/VInr eqTtV eqTtV VRefl)` instead of `VTrue`/`VFalse`
- **`reifyType` VMu-plus recognizer.** The retired `VBool → H.bool` and `VVoid → H.void` cases are replaced by a VMu handler that checks the plus-coproduct-of-two-`retI tt` shape and maps to `H.bool`; `extractInner`'s `t == "bool"` branch is dropped (the mu branch handles the derived form)
- **Elaborate's empty-variant case** routes to `self.void` (the derived `Fin 0`) instead of the deleted `T.mkVoid`

### Removed

- **Kernel `Tm` constructors** — `Bool`, `True`, `False`, `BoolElim(P,t,f,b)`, `Void`, `Absurd(A,t)`. No Tm builders (`mkBool`, `mkTrue`, `mkFalse`, `mkBoolElim`, `mkVoid`, `mkAbsurd`), no `inherit`s of them, no docs
- **Kernel `Val` constructors** — `VBool`, `VTrue`, `VFalse`, `VVoid`. `Elim` frames `EBoolElim(P,t,f)`, `EAbsurd(A)` also gone. Their `eval` / `check` / `infer` / `conv` / `quote` / `elaborate` dispatch cases removed across `src/tc/`
- **HOAS primitive aliases** — `boolPrim`, `truePrim_`, `falsePrim_`, `voidPrim`, `absurdPrim`, `boolElimPrim` in `src/tc/hoas/combinators.nix`. Along with dead helpers `natDisc` (43 lines), `noConfSuccZero` (9 lines), `symNat` (5 lines) — all unreachable after the `absurdFin0` rewrite

### Documented

- **`CONTRIBUTING.md` CI-requirements and bench sections.** The `## CI requirements` section explains the dual-axis gate, the CI alloc-only vs. local dual-metric split, the Nix-version constraint, and the `Perf-regression:` trailer contract. A new `## Baseline refresh` section documents when to regenerate `bench/history/baseline.{json,md}` (intentional alloc improvement, Nix evaluator upgrade, new workload), the exact procedure, the sample-size caveat for local cpu gating, and how to recalibrate `bench/budgets.toml` while preserving `noiseLimited`
- **`kernel-architecture.md` reframed** — replaced the vacuously-true "one system" prose with a factual "two kernels" description: effects kernel (`src/kernel.nix`, freer monad + FTCQueue) and type-checking kernel (`src/tc/`, MLTT), plus the route by which the TC kernel's higher layers send `typeError` effect requests that handlers in `src/effects/typecheck.nix` interpret with pluggable strategies. Structural-types list moves `Bool`/`Void` into a derived bullet pointing at `combinators.nix`
- **`kernel-spec.md` synced with Bool/Void retirement** — §4.5 Booleans and §4.8 Void deleted; §4 renumbered (§4.5–§4.11); retired `Tm`/`Val`/`Elim` constructors and dispatch cases removed across §§2–9; §4.11 and §7.3 StrEq rules updated to return the derived `H.bool`; §11 positive/negative fixtures migrated from `Bool`/`True`/`False`/`Void`/`Absurd`/`BoolElim` to `Unit`/`Tt`/`Sum(Nat,Unit)` where the point wasn't testing bool/void behavior; §12 notation index rows `𝔹` and `⊥` annotated "(derived: …)"
- **`proof-guide.md` updated** — §Booleans and §Boolean-and-cross-type-elimination describe `H.boolElim k motive trueCase falseCase scrutinee` as a derived combinator on the plus-coproduct `boolDesc`; §"What the kernel can and cannot prove" opening and the user-defined-recursive-types bullet distinguish primitive inductives (Nat, List, Sum, Unit, Eq, indexed descriptions) from derived (Bool, Void); quick-reference table rows updated accordingly
- **`systems-architecture.md` reframed** — drop the "one system / no adequacy bridge / no separate contract system" framing at the opener, §"The kernel-first architecture", and §"What exists"; describe the two-kernel layering and `typeError`-effect route factually instead. Kernel `Tm` enumeration in §"The term language" drops the retired `bool`/`true`/`false`/`void`/`absurd` tags and adds the indexed-description constructors (`desc`, `desc-ret`, `desc-arg`, `desc-rec`, `desc-pi`, `desc-plus`, `mu`, `desc-con`, `desc-ind`); "What exists" §1 kernel inventory corrected (Bool/Void now listed as derived)
- **`README.md` gains a table of contents** aligned to the existing section headings

### Fixed

- **`ListOf` element decomposition.** `ListOf.verify` previously sent a flat `typeCheck` effect with the element type and a synthetic `"List[T][i]"` context string, bypassing per-element decomposition. For record elements this flattened per-field blame to a single "whole element invalid" effect. Fixed by delegating to `elemType.validateAt (path ++ ["[${i}]"]) elem`, so a list of records now emits one effect per (element, field) pair
- **Deep blame path loss in `Record`.** `Record.verify`'s present-field branch called `field.validate v.field` without threading context, so a three-level nested record with a bad leaf reported only the leaf type name — no structural descent. Fixed by threading `path ++ [field]` through `validateAt`

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
- **`apps/category-theory/algebra.nix`** — old nested-Σ `MonoidOf` / `CategoryTy` encoding replaced by macro datatypes. `natAddMonoid` and `natCategory` are exposed as HOAS records carrying both the component HOAS terms (`.op`, `.e`, `.comp`, …) and the bundled `(ty, impl)` pair that the kernel checks
- **Example-library invocations** — README and apps use `nix eval` rather than `nix-instantiate --eval --strict`

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
- **Category theory library** (`apps/category-theory/`) — formally verified proofs running at Nix eval time. Proof combinators (sym, trans, cong) derived from J elimination; natural number arithmetic with 7 verified properties including commutativity; Monoid and Category as dependent sigma types with (Nat,+,0) instances; commutativity of composition in the endomorphism monoid; doubling endofunctor with functoriality proof via 5-step equational rewriting
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
- Benchmark apps: expression interpreter (`apps/interp`) and dependency graph evaluator (`apps/build-sim`) with scalable workload generators
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
