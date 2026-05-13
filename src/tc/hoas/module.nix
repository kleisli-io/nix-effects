# fx.tc.hoas — HOAS surface combinators module head.
#
# Public export assembly. `self` is the disjoint-union fixpoint of
# `combinators.nix` (core HOAS nodes + binding forms +
# descriptions + eliminator wrappers), `desc.nix` (prelude descriptions and
# descDesc encoders), `datatype.nix` (datatype macro +
# prelude instances + surface forwarders), and `elaborate.nix` (HOAS → Tm
# elaborator + kernel-checker convenience wrappers); `partTests` is the
# aggregated test map.
{ self, partTests, api, ... }:

api.mk {
  doc = ''
    # fx.types.hoas — HOAS Surface Combinators

    Higher-Order Abstract Syntax layer that lets you write kernel terms
    using Nix lambdas for variable binding. The `elaborate` function
    compiles HOAS trees to de Bruijn indexed Tm terms.

    Spec reference: kernel-spec.md §2.

    ## Example

    ```nix
    # Π(A:U₀). A → A
    H.forall "A" (H.u 0) (A: H.forall "x" A (_: A))
    ```

    ## Type Combinators

    - `nat`, `bool`, `unit`, `void` — base types
    - `string`, `int_`, `float_`, `attrs`, `path`, `function_`, `any` — primitive types
    - `listOf : Hoas → Hoas` — List(elem)
    - `sum : Hoas → Hoas → Hoas` — Sum(left, right)
    - `eq : Hoas → Hoas → Hoas → Hoas` — generated EqDT(type, lhs, rhs)
    - `u : Int → Hoas` — Universe at level
    - `forall : String → Hoas → (Hoas → Hoas) → Hoas` — Π-type (Nix lambda for body)
    - `sigma : String → Hoas → (Hoas → Hoas) → Hoas` — Σ-type

    ## Compound Types (Sugar)

    - `record : [{ name; type; }] → Hoas` — nested Sigma (sorted fields)
    - `maybe : Hoas → Hoas` — Sum(inner, Unit)
    - `variant : [{ tag; type; }] → Hoas` — nested Sum (sorted tags)

    ## Term Combinators

    - `lam : String → Hoas → (Hoas → Hoas) → Hoas` — λ-abstraction
    - `let_ : String → Hoas → Hoas → (Hoas → Hoas) → Hoas` — let binding
    - `zero`, `succ`, `true_`, `false_`, `tt`, `refl` — intro forms; `refl` is check-mode only
    - `nil`, `cons`, `pair`, `inl`, `inr` — data constructors
    - `stringLit`, `intLit`, `floatLit`, `attrsLit`, `pathLit`, `fnLit`, `anyLit` — primitive literals
    - `absurd`, `ann`, `app`, `fst_`, `snd_` — elimination/annotation

    ## Eliminators

    - `ind` — generated natural eliminator adapter
    - `boolElim` — (k : Level) → (Q : bool → U(k)) → Q true_ → Q false_ → (b : bool) → Q b
    - `listElim` — generated list eliminator adapter
    - `sumElim` — generated sum eliminator adapter
    - `j` — EqDT eliminator adapter with J-shaped arguments

    ## Elaboration

    - `elaborate : Int → Hoas → Tm` — compile at given depth
    - `elab : Hoas → Tm` — compile from depth 0

    ## Convenience

    - `checkHoas : Hoas → Hoas → Tm|Error` — elaborate type+term, type-check
    - `inferHoas : Hoas → { term; type; }|Error` — elaborate and infer
    - `natLit : Int → Hoas` — build S^n(zero)

    ## Stack Safety

    Binding chains (pi/lam/sigma/let), succ chains, and cons chains
    are elaborated iteratively via `genericClosure` — safe to 8000+ depth.
  '';
  value = {
    # Types
    inherit (self)
      nat bool unit void w string int_ float_ attrs path function_ any listOf sum sumAt eq u
      record maybe variant;
    # Level sort and its constructors. `level` is the universe-level
    # type former (inhabits U(0)); `levelZero`/`levelSuc`/`levelMax`
    # build Level expressions that flow into `u`/`descArg`/`descPi`'s
    # level slots. Bound Level variables come from
    # `forall "k" level (k_var: …)`.
    inherit (self) level levelZero levelSuc levelMax natToLevel;
    # Binding
    inherit (self) forall sigma lam let_;
    # Terms
    inherit (self)
      zero succ true_ false_ tt nil cons pair inl inr inlAt inrAt sup refl
      stringLit intLit floatLit attrsLit pathLit fnLit anyLit
      opaqueLam strEq absurd ann app fst_ snd_;
    # Eliminators
    inherit (self) ind boolElim listElim sumElim sumElimAt j;
    # Propositional truncation (Squash). `squash A` formation,
    # `squashIntro a` introduction, `squashElim A B f x` eliminator
    # restricted to `Squash`-typed motives.
    inherit (self) squash squashIntro squashElim;
    # Descriptions — types, constructors, eliminators.
    # `descI`/`retI`/`recI`/`piI`/`muI` build `Desc I` / `μ I D i` at an
    # arbitrary index type; `desc`/`descRet`/`descRec`/`descPi`/`mu` are
    # ⊤-slice aliases that specialise I to `Unit`.
    inherit (self) descI desc descIAt descAt muI mu retI recI piI piIAt
                   piIWithEq
                   descRet descArg descArgAt descArgWithEq descRec
                   descPi descPiAt descPiWithEq
                   plusI plus
                   descCon descInd descElim
                   interpD allD everywhereD
                   congSuc maxSucDom;
    # Lift primitive — Tarski + non-cumulative cross-level transport.
    # `LiftAt l m A : U(m)` with `l ≤ m`; `liftAt l m A a` /
    # `lowerAt l m A x` introduce / eliminate. The `eq` witness is
    # auto-emitted as `mkBootRefl` by the elaborator. The `*WithEq` variants
    # take an explicit `eq` term — used when `l`/`m` are level-polymorphic
    # binders and `convLevel` cannot decide `refl`.
    inherit (self) LiftAt liftAt lowerAt
                   LiftAtWithEq liftAtWithEq lowerAtWithEq;
    # Prelude descriptions
    inherit (self) natDesc listDesc sumDesc natDescTm descDesc descDescTm descDescVal __descDesc descDescApp;
    # descDesc-encoded constructor Tms — closed kernel terms that
    # produce `μ ⊤ (descDesc I k) tt` values structurally encoding
    # source descriptions. Each is the pre-elaborated form of the
    # corresponding `encodeDesc*` HOAS combinator; the shared encoding
    # context lives in `descEncodingCtx` (a Nix-level helper internal
    # to `hoas/`).
    inherit (self) encodeDescRet encodeDescRetTm
                   encodeDescArg encodeDescArgTm
                   encodeDescArgAt encodeDescArgAtTm
                   encodeDescRec encodeDescRecTm
                   encodeDescPi  encodeDescPiTm
                   encodeDescPiAt encodeDescPiAtTm
                   encodeDescPlus encodeDescPlusTm
                   encodeDescElim encodeDescElimTm encodeDescElimVal;
    # Fin prelude — indexed family `Fin : Nat → U` with vacuous base at
    # `Fin 0` (discharged via `absurdFin0`).
    inherit (self) finDesc fin fzero fsuc finElim absurdFin0;
    # Vec prelude — indexed family `Vec A : Nat → U`. `vhead` / `vtail`
    # extract head / tail of a non-empty vector via `natCaseU`- /
    # `natPredCase`-motives over `vecElim`. `natPredCase` dispatches the
    # succ-case result type through the private plus-summand eliminator.
    inherit (self) natCaseU natPredCase vecDesc vec vnil vcons vecElim vhead vtail;
    # Eq-as-description — public equality as an indexed datatype over a
    # single retI-only description. The iso helpers bridge to the private
    # bootstrap identity used by descRet.
    inherit (self) eqDesc eqDT reflDT eqToEqDT eqDTToEq eqIsoFwd eqIsoBwd;
    # Datatype macro
    inherit (self)
      field fieldD fieldAt fieldDAt fieldAtWithEq fieldDAtWithEq
      recField recFieldAt
      piField piFieldD piFieldAt piFieldDAt piFieldAtWithEq piFieldDAtWithEq
      con conI
      datatype datatypeAt datatypeI datatypeP datatypePAt datatypePI;
    inherit (self) WDT wDesc wElim;
    # Elaboration
    inherit (self) elaborate elab reifyLevel;
    # HOAS surface → SourceMap walker, and the pair-producing `elab2`
    # that the diagnostic shell consumes.
    inherit (self) sourceMapOf elab2;
    # Convenience
    inherit (self) checkHoas inferHoas natLit;
  };
  tests = partTests;
}
