# Overlay value algebra for the meta-aware elaborator.
#
# `ElabVal = Val ⊎ VMeta` informally — kernel `Val`s pass through
# unchanged; `VMeta` is a sentinel-tagged constructor distinct from
# the kernel's value algebra.
#
# Refs: Abel-Pientka (2011) §2 grammar `R ::= E[H] | E[u[σ]]` — `VMeta`
# encodes the `u[σ]` half (a metavariable applied to its captured
# spine). `type = { ctx; ty }` carries the meta's allocation-site
# typing context (`Ctx`) plus its expected type as a kernel `Val`,
# matching the paper's `u : A[Φ]` annotation.
#
# Kernel-purity: `VMeta` is NOT promoted into `src/tc/value.nix`'s
# `Val` algebra. Putting it there would force kernel reductions to
# consult the meta-context Δ (per Abel-Pientka §5), which violates
# the kernel-purity principle. The overlay sits strictly above the
# kernel; `force` (in `effects.nix`) is the only bridge.
{ fx, api, ... }:

let
  E = fx.tc.eval;
  V = fx.tc.value;
  defaultFuel = 10000000;

  mkVMeta = id: spine: type:
    { _vTag = "VMeta"; inherit id spine type; };

  isVMeta = v:
    builtins.isAttrs v && (v ? _vTag) && v._vTag == "VMeta";

  coerce = v: v;

  extendVMeta = v: frame:
    v // { spine = v.spine ++ [ frame ]; };

  elabAppF = fuel: fn: arg:
    if isVMeta fn then extendVMeta fn (V.eApp arg)
    else E.vApp fn arg;

  elabFst = p:
    if isVMeta p then extendVMeta p V.eFst
    else E.vFst p;

  elabSnd = p:
    if isVMeta p then extendVMeta p V.eSnd
    else E.vSnd p;

  elabBootSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
    if isVMeta scrut
    then extendVMeta scrut (V.eBootSumElim left right motive onLeft onRight)
    else E.vBootSumElim left right motive onLeft onRight scrut;

  elabBootJ = type: lhs: motive: base: rhs: eq:
    if isVMeta eq then extendVMeta eq (V.eBootJ type lhs motive base rhs)
    else E.vBootJ type lhs motive base rhs eq;

  elabSquashElimF = fuel: A: B: f: x:
    if isVMeta x then extendVMeta x (V.eSquashElim A B f)
    else E.vSquashElim A B f x;

  elabLiftElimF = l: m: eq: A: x:
    if isVMeta x then extendVMeta x (V.eLiftElim l m eq A)
    else E.vLiftElimF l m eq A x;

  elabDescIndF = fuel: D: motive: step: i: scrut:
    if isVMeta scrut then extendVMeta scrut (V.eDescInd D motive step i)
    else E.vDescInd D motive step i scrut;

  elabInterpDF = fuel: level: I: D: X: i:
    if isVMeta D then extendVMeta D (V.eInterpD level I X i)
    else E.vInterpD level I D X i;

  elabAllDF = fuel: level: I: D: K: X: M: i: d:
    if isVMeta D then extendVMeta D (V.eAllD level I K X M i d)
    else E.vAllD level I D K X M i d;

  elabEverywhereDF = fuel: level: I: D: K: X: M: ih: i: d:
    if isVMeta D then extendVMeta D (V.eEverywhereD level I K X M ih i d)
    else E.vEverywhereD level I D K X M ih i d;

  elabApp = elabAppF defaultFuel;
  elabBootSumElim = elabBootSumElimF defaultFuel;
  elabSquashElim = elabSquashElimF defaultFuel;
  elabDescInd = elabDescIndF defaultFuel;
  elabInterpD = elabInterpDF defaultFuel;
  elabAllD = elabAllDF defaultFuel;
  elabEverywhereD = elabEverywhereDF defaultFuel;

  # Tests fixtures
  spine0 = [ ];
  type0 = {
    ctx = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
    ty = V.vUnit;
  };
  meta0 = mkVMeta 0 spine0 type0;
  lamId = V.vLam "x" V.vUnit (V.mkClosure [ ] (fx.tc.term.mkVar 0));
in
{
  scope = {
    mkVMeta = api.leaf {
      value = mkVMeta;
      description = "mkVMeta: construct an overlay metavariable value — `{ _vTag = \"VMeta\"; id; spine; type = { ctx; ty } }`. `id` is the globally-unique meta identifier allocated by `runElab`; `spine` is the local-variable spine captured at construction (Abel-Pientka, section 2 σ); `type` carries the meta's allocation-site typing context plus its expected type (paper's `A[Φ]` annotation).";
      signature = "mkVMeta : Int -> [Val] -> { ctx : Ctx; ty : Val } -> ElabVal";
      tests = {
        "mkVMeta-tag" = {
          expr = (mkVMeta 0 spine0 type0)._vTag;
          expected = "VMeta";
        };
        "mkVMeta-id" = {
          expr = (mkVMeta 7 spine0 type0).id;
          expected = 7;
        };
        "mkVMeta-spine" = {
          expr = (mkVMeta 0 [ V.vTt V.vUnit ] type0).spine;
          expected = [ V.vTt V.vUnit ];
        };
        "mkVMeta-type-fields" = {
          expr =
            let m = mkVMeta 0 spine0 type0;
            in { hasCtx = m.type ? ctx; hasTy = m.type ? ty; };
          expected = { hasCtx = true; hasTy = true; };
        };
      };
    };
    isVMeta = api.leaf {
      value = isVMeta;
      description = "isVMeta: predicate distinguishing the overlay `VMeta` from kernel `Val`s — true iff `v._vTag == \"VMeta\"`. Kernel `Val`s use `tag` (not `_vTag`) for ADT discrimination, so the predicate is decidable on the disjoint union.";
      signature = "isVMeta : ElabVal -> Bool";
      tests = {
        "isVMeta-on-VMeta-true" = {
          expr = isVMeta (mkVMeta 0 spine0 type0);
          expected = true;
        };
        "isVMeta-on-vTt-false" = {
          expr = isVMeta V.vTt;
          expected = false;
        };
        "isVMeta-on-vUnit-false" = {
          expr = isVMeta V.vUnit;
          expected = false;
        };
        "isVMeta-on-non-attrset-false" = {
          expr = isVMeta 42;
          expected = false;
        };
      };
    };
    coerce = api.leaf {
      value = coerce;
      description = "coerce: embed a kernel `Val` into `ElabVal`. Identity at the Nix level — the coproduct `ElabVal = Val ⊎ VMeta` is structural (kernel `Val`s are already valid `ElabVal` inhabitants because `VMeta` has a disjoint tag).";
      signature = "coerce : Val -> ElabVal";
      tests = {
        "coerce-identity" = {
          expr = coerce V.vUnit == V.vUnit;
          expected = true;
        };
      };
    };
    elabAppF = api.leaf {
      value = elabAppF;
      description = "elabAppF fuel fn arg: meta-aware application helper. Rigid `fn` delegates to the kernel evaluator; `VMeta` appends `EApp arg` to its spine.";
      signature = "elabAppF : Fuel -> ElabVal -> ElabVal -> ElabVal";
      tests = {
        "elabAppF-rigid-lambda-reduces" = {
          expr = (elabAppF 10 lamId V.vTt).tag;
          expected = "VTt";
        };
        "elabAppF-meta-extends-spine" = {
          expr = (elabAppF 10 meta0 V.vTt).spine;
          expected = [ (V.eApp V.vTt) ];
        };
      };
    };
    elabApp = elabApp;

    elabFst = api.leaf {
      value = elabFst;
      description = "elabFst p: meta-aware first projection. Rigid pairs/neutrals delegate to the kernel evaluator; `VMeta` appends `EFst`.";
      signature = "elabFst : ElabVal -> ElabVal";
      tests = {
        "elabFst-rigid-pair-reduces" = {
          expr = (elabFst (V.vPair V.vTt V.vUnit)).tag;
          expected = "VTt";
        };
        "elabFst-meta-extends-spine" = {
          expr = (elabFst meta0).spine;
          expected = [ V.eFst ];
        };
      };
    };
    elabSnd = api.leaf {
      value = elabSnd;
      description = "elabSnd p: meta-aware second projection. Rigid pairs/neutrals delegate to the kernel evaluator; `VMeta` appends `ESnd`.";
      signature = "elabSnd : ElabVal -> ElabVal";
      tests = {
        "elabSnd-rigid-pair-reduces" = {
          expr = (elabSnd (V.vPair V.vUnit V.vTt)).tag;
          expected = "VTt";
        };
        "elabSnd-meta-extends-spine" = {
          expr = (elabSnd meta0).spine;
          expected = [ V.eSnd ];
        };
      };
    };
    elabBootSumElimF = api.leaf {
      value = elabBootSumElimF;
      description = "elabBootSumElimF fuel left right motive onLeft onRight scrut: meta-aware bootstrap sum eliminator. `VMeta` appends `EBootSumElim`.";
      signature = "elabBootSumElimF : Fuel -> Val -> Val -> Val -> Val -> Val -> ElabVal -> ElabVal";
      tests = {
        "elabBootSumElimF-meta-extends-spine" = {
          expr = (elabBootSumElimF 10 V.vUnit V.vUnit V.vUnit V.vTt V.vTt meta0).spine;
          expected = [ (V.eBootSumElim V.vUnit V.vUnit V.vUnit V.vTt V.vTt) ];
        };
      };
    };
    elabBootSumElim = elabBootSumElim;

    elabBootJ = api.leaf {
      value = elabBootJ;
      description = "elabBootJ type lhs motive base rhs eq: meta-aware J eliminator. `VBootRefl` reduces to `base`; `VMeta` appends `EBootJ`.";
      signature = "elabBootJ : Val -> Val -> Val -> Val -> Val -> ElabVal -> ElabVal";
      tests = {
        "elabBootJ-refl-reduces" = {
          expr = (elabBootJ V.vUnit V.vTt V.vUnit V.vTt V.vTt V.vBootRefl).tag;
          expected = "VTt";
        };
        "elabBootJ-meta-extends-spine" = {
          expr = (elabBootJ V.vUnit V.vTt V.vUnit V.vTt V.vTt meta0).spine;
          expected = [ (V.eBootJ V.vUnit V.vTt V.vUnit V.vTt V.vTt) ];
        };
      };
    };
    elabSquashElimF = api.leaf {
      value = elabSquashElimF;
      description = "elabSquashElimF fuel A B f x: meta-aware propositional-truncation eliminator. `VMeta` appends `ESquashElim`.";
      signature = "elabSquashElimF : Fuel -> Val -> Val -> Val -> ElabVal -> ElabVal";
      tests = {
        "elabSquashElimF-meta-extends-spine" = {
          expr = (elabSquashElimF 10 V.vUnit V.vUnit lamId meta0).spine;
          expected = [ (V.eSquashElim V.vUnit V.vUnit lamId) ];
        };
      };
    };
    elabSquashElim = elabSquashElim;

    elabLiftElimF = api.leaf {
      value = elabLiftElimF;
      description = "elabLiftElimF l m eq A x: meta-aware Lift eliminator. `VMeta` appends `ELiftElim`.";
      signature = "elabLiftElimF : Val -> Val -> Val -> Val -> ElabVal -> ElabVal";
      tests = {
        "elabLiftElimF-meta-extends-spine" = {
          expr = (elabLiftElimF V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl V.vUnit meta0).spine;
          expected = [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl V.vUnit) ];
        };
      };
    };
    elabDescIndF = api.leaf {
      value = elabDescIndF;
      description = "elabDescIndF fuel D motive step i scrut: meta-aware descInd eliminator. `VMeta` appends `EDescInd`.";
      signature = "elabDescIndF : Fuel -> Val -> Val -> Val -> Val -> ElabVal -> ElabVal";
      tests = {
        "elabDescIndF-meta-extends-spine" = {
          expr = (elabDescIndF 10 V.vUnit V.vUnit V.vTt V.vTt meta0).spine;
          expected = [ (V.eDescInd V.vUnit V.vUnit V.vTt V.vTt) ];
        };
      };
    };
    elabDescInd = elabDescInd;

    elabInterpDF = api.leaf {
      value = elabInterpDF;
      description = "elabInterpDF fuel level I D X i: meta-aware interpD. `VMeta` in the description position appends `EInterpD`.";
      signature = "elabInterpDF : Fuel -> Val -> Val -> ElabVal -> Val -> Val -> ElabVal";
      tests = {
        "elabInterpDF-meta-extends-spine" = {
          expr = (elabInterpDF 10 V.vLevelZero V.vUnit meta0 V.vUnit V.vTt).spine;
          expected = [ (V.eInterpD V.vLevelZero V.vUnit V.vUnit V.vTt) ];
        };
      };
    };
    elabInterpD = elabInterpD;

    elabAllDF = api.leaf {
      value = elabAllDF;
      description = "elabAllDF fuel level I D K X M i d: meta-aware allD. `VMeta` in the description position appends `EAllD`.";
      signature = "elabAllDF : Fuel -> Val -> Val -> ElabVal -> Val -> Val -> Val -> Val -> Val -> ElabVal";
      tests = {
        "elabAllDF-meta-extends-spine" = {
          expr = (elabAllDF 10 V.vLevelZero V.vUnit meta0 V.vLevelZero V.vUnit V.vUnit V.vTt V.vBootRefl).spine;
          expected = [ (V.eAllD V.vLevelZero V.vUnit V.vLevelZero V.vUnit V.vUnit V.vTt V.vBootRefl) ];
        };
      };
    };
    elabAllD = elabAllD;

    elabEverywhereDF = api.leaf {
      value = elabEverywhereDF;
      description = "elabEverywhereDF fuel level I D K X M ih i d: meta-aware everywhereD. `VMeta` in the description position appends `EEverywhereD`.";
      signature = "elabEverywhereDF : Fuel -> Val -> Val -> ElabVal -> Val -> Val -> Val -> Val -> Val -> Val -> ElabVal";
      tests = {
        "elabEverywhereDF-meta-extends-spine" = {
          expr = (elabEverywhereDF 10 V.vLevelZero V.vUnit meta0 V.vLevelZero V.vUnit V.vUnit V.vUnit V.vTt V.vBootRefl).spine;
          expected = [ (V.eEverywhereD V.vLevelZero V.vUnit V.vLevelZero V.vUnit V.vUnit V.vUnit V.vTt V.vBootRefl) ];
        };
      };
    };
    elabEverywhereD = elabEverywhereD;
  };
}
