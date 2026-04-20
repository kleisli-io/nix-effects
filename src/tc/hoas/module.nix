# fx.tc.hoas — HOAS surface combinators module head.
#
# Public export assembly. `self` is the disjoint-union fixpoint of
# `combinators.nix` (kernel-primitive HOAS nodes + binding forms +
# descriptions + eliminator wrappers), `desc.nix` (interpHoas / allHoas
# helpers + prelude descriptions), `datatype.nix` (datatype macro +
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
    - `eq : Hoas → Hoas → Hoas → Hoas` — Eq(type, lhs, rhs)
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
    - `zero`, `succ`, `true_`, `false_`, `tt`, `refl` — intro forms
    - `nil`, `cons`, `pair`, `inl`, `inr` — data constructors
    - `stringLit`, `intLit`, `floatLit`, `attrsLit`, `pathLit`, `fnLit`, `anyLit` — primitive literals
    - `absurd`, `ann`, `app`, `fst_`, `snd_` — elimination/annotation

    ## Eliminators

    - `ind` — NatElim(motive, base, step, scrut)
    - `boolElim` — (k : Level) → (Q : bool → U(k)) → Q true_ → Q false_ → (b : bool) → Q b
    - `listElim` — ListElim(elem, motive, onNil, onCons, scrut)
    - `sumElim` — SumElim(left, right, motive, onLeft, onRight, scrut)
    - `j` — J(type, lhs, motive, base, rhs, eq)

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
      nat bool unit void string int_ float_ attrs path function_ any listOf sum eq u
      record maybe variant;
    # Binding
    inherit (self) forall sigma lam let_;
    # Terms
    inherit (self)
      zero succ true_ false_ tt nil cons pair inl inr refl
      stringLit intLit floatLit attrsLit pathLit fnLit anyLit
      opaqueLam strEq absurd ann app fst_ snd_;
    # Eliminators
    inherit (self) ind boolElim listElim sumElim j;
    # Descriptions — types, constructors, eliminators.
    # `descI`/`retI`/`recI`/`piI`/`muI` build `Desc I` / `μ I D i` at an
    # arbitrary index type; `desc`/`descRet`/`descRec`/`descPi`/`mu` are
    # ⊤-slice aliases that specialise I to `Unit`.
    inherit (self) descI desc muI mu retI recI piI
                   descRet descArg descRec descPi descCon descInd descElim;
    # Description-level helpers and prelude descriptions
    inherit (self) interpHoas allHoas natDesc listDesc sumDesc natDescTm;
    # Fin prelude — indexed family `Fin : Nat → U` with vacuous base at
    # `Fin 0` (discharged via `absurdFin0`).
    inherit (self) finDesc fin fzero fsuc finElim absurdFin0;
    # Vec prelude — indexed family `Vec A : Nat → U`. `vhead` / `vtail`
    # extract head / tail of a non-empty vector via `natCaseU`- /
    # `natPredCase`-motives over `vecElim`. `natPredCase` dispatches the
    # succ-case result type on the payload's predecessor field via
    # `sumElimPrim` on the plus-summand.
    inherit (self) natCaseU natPredCase vecDesc vec vnil vcons vecElim vhead vtail;
    # Eq-as-description — the kernel-primitive `Eq` derived as an
    # inductive family over a single retI-only description.
    # `eqIsoFwd` / `eqIsoBwd` prove the iso with the primitive.
    inherit (self) eqDesc eqDT reflDT eqToEqDT eqDTToEq eqIsoFwd eqIsoBwd;
    # Datatype macro
    inherit (self) field fieldD recField piField piFieldD con datatype datatypeP;
    # Elaboration
    inherit (self) elaborate elab;
    # Convenience
    inherit (self) checkHoas inferHoas natLit;
  };
  tests = partTests;
}
