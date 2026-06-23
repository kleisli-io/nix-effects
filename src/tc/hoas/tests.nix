# Inline tests for the HOAS surface: combinator-level elaboration shape
# checks, kernel-integration checks through `checkHoas`/`inferHoas`,
# theorem proofs, description-level semantic equivalence, datatype macro
# coverage (UnitDT / BoolDT / NatDT / ListDT / SumDT / TreeDT / W-type),
# and deep-stack / neutral-scrutinee stress tests.
{ self, fx, ... }:

let
  E = fx.tc.eval;
  Q = fx.tc.quote;
  V = fx.tc.value;
  C = fx.tc.conv;
  T = fx.tc.term;
  CH = fx.tc.check;
  HI = {
    inherit (self) nilAtExplicit consAtExplicit inlAtExplicit inrAtExplicit;
  };
  fzeroAt = m: self.app self.FinDT.fzero m;
  fsucAt = m: k: self.app (self.app self.FinDT.fsuc m) k;
  leZAt = n: self.app self.LeDT.leZ n;
  leSSAt = m: n: lemn: self.app (self.app (self.app self.LeDT.leSS m) n) lemn;
  vnilAt = A: self.implicitApp self.VecDT.vnil A;
  vconsAt = A: m: x: xs:
    self.app (self.app (self.app (self.implicitApp self.VecDT.vcons A) m) x) xs;

  inherit (self)
    nat bool unit void w string int_ float_ attrs path function_ any
    listOf sum eq u
    bootEq bootRefl
    level levelZero levelSuc levelMax natToLevel
    LiftAt liftAt lowerAt LiftAtWithEq liftAtWithEq lowerAtWithEq
    forall sigma lam let_
    zero succ true_ false_ tt nil cons pair inl inr sup refl
    stringLit intLit floatLit attrsLit pathLit fnLit anyLit
    opaqueLam absurd ann app fst_ snd_
    ind boolElim listElim sumElim
    desc descAt mu descRet descArg descArgAt descRec descPi descPiAt descCon descInd descElim
    interpD allD
    descI descIAt muI retI recI piI plusI plus
    natDesc listDesc sumDesc descDesc __descDesc canonApp
    encodeDescElim
    retIAtI recIAtI piIAtI plusIAtI muIAtI descIAtI
    ttPrim
    fin fzero fsuc finElim absurdFin0
    le leZ leSS leElim leDesc
    True False and or_ not iff dec yes no decElim
    decAnd decOr decNot
    predNat eqCongSucc eqInjSucc eqRefutSuccZero eqRefutZeroSucc
    leRefutSuccZero leInjSS
    decideEqNat decideLeNat
    intz intzDesc intzPos intzNegSucc intzElim
    intzLit signsDiffer intzLe
    signsDifferRev intzPosCong intzNegSuccCong intzDecode
    intzPosInjective intzNegSuccInjective
    decideEqIntZ decideLeIntZ refinementPred
    natCaseU natPredCase vec vnil vcons vecElim vhead vtail
    eqDesc eqDT reflDT eqToEqDT eqDTToEq eqIsoFwd eqIsoBwd
    wDesc wElim
    field fieldAt recField piFieldD piFieldDAt con datatype datatypeAt datatypeP datatypePAt unitPrim
    elab checkHoas inferHoas natLit;

  # Use conversion for semantic HOAS equality. Raw `Q.nf lhs == Q.nf rhs`
  # can force recursive datatype metadata in quoted bootstrap sum types.
  semEq = lhs: rhs:
    C.conv 0 (E.eval [ ] (elab lhs)) (E.eval [ ] (elab rhs));

  # Constant-Nat decision probe: `decElim` over `dec P` with a
  # constant `nat` motive maps the yes / no branches to `zero` /
  # `succ zero`. Forcing `Q.nf` then comparing against the
  # pre-computed sentinels tests the decision-procedure semantics
  # end-to-end through elaboration + kernel reduction.
  yesSentinel = Q.nf [ ] (elab zero);
  noSentinel = Q.nf [ ] (elab (succ zero));
  decProbeNat = P: d:
    decElim P
      (lam "_" (dec P) (_: nat))
      (lam "_" P (_: zero))
      (lam "_" (not P) (_: succ zero))
      d;

  shallowMeta = meta: {
    inherit (meta) name indexed indexTy;
    params = meta.params or [ ];
    paramArgs = meta.paramArgs or [ ];
    constructors = map
      (c: {
        name = c.name;
        fields = map (f: { name = f.name; kind = f.kind; }) c.fields;
      })
      meta.constructors;
  };

  isoTy = forall "iLev" level (iLev:
    forall "I" (u iLev) (I:
      forall "k" level (k:
        let
          dDescAt = app (app (app descDesc iLev) I) k;
          muTtAt = mu dDescAt ttPrim;
          descK = descIAt k I;
        in
        sigma "to_" (forall "_" descK (_: muTtAt)) (toV:
          sigma "from_" (forall "_" muTtAt (_: descK)) (fromV:
            sigma "toFrom_"
              (forall "D" descK (D: bootEq descK (app fromV (app toV D)) D))
              (_:
                forall "x" muTtAt (x:
                  bootEq muTtAt (app toV (app fromV x)) x)))))));

  # Identity iso bridge between the surface name `Desc^k I` and the
  # descDesc-encoded `μ⊤(descDesc I k) tt`. The two presentations name
  # the same type via the kernel's Desc/μ unfolding conv rule, so the
  # iso witnesses are identity and the round-trip equalities are refl.
  # That this term typechecks against `isoTy` is the load-bearing
  # regression on `descDesc`'s faithfulness as an encoding of `Desc`:
  # if `descDesc`'s body ever drifts from a faithful 5-summand mirror
  # of `Desc`'s ret/arg/rec/pi/plus grammar, the conv rule stops
  # firing for the Σ-component checks and this term fails to elaborate.
  isoIdentity = ann
    (lam "iLev" level (iLev:
      lam "I" (u iLev) (I:
        lam "k" level (k:
          let
            dDesc = app (app (app descDesc iLev) I) k;
            muTt = mu dDesc ttPrim;
            descK = descIAt k I;
            toTerm = lam "D" descK (D: D);
            fromTerm = lam "x" muTt (x: x);
          in
          pair toTerm
            (pair fromTerm
              (pair (lam "D" descK (_: bootRefl))
                (lam "x" muTt (_: bootRefl))))))))
    isoTy;
in
{
  scope = { };
  tests = {
    # ===== Combinator tests (elaborate produces correct Tm) =====

    # -- Type combinators --
    "elab-nat" = { expr = (elab nat).tag; expected = "mu"; };
    "elab-bool" = { expr = (elab bool).tag; expected = "mu"; };
    "elab-unit" = { expr = (elab unit).tag; expected = "unit"; };
    "elab-void" = { expr = (elab void).tag; expected = "empty"; };
    "elab-U0" = { expr = (elab (u 0)).tag; expected = "U"; };
    "elab-U0-level" = { expr = (elab (u 0)).level.tag; expected = "level-zero"; };
    "liftAt-auto-homogeneous-type-erases" = {
      expr = (elab (LiftAt 0 0 nat)).tag;
      expected = "mu";
    };
    "liftAt-auto-homogeneous-int-level-erases" = {
      expr = (elab (LiftAt 0 levelZero nat)).tag;
      expected = "mu";
    };
    "liftAt-auto-homogeneous-bound-level-erases" = {
      expr = (elab (forall "k" level (k: LiftAt k k nat))).codomain.tag;
      expected = "mu";
    };
    "liftAt-auto-heterogeneous-type-keeps-node" = {
      expr = (elab (LiftAt 0 1 nat)).tag;
      expected = "lift";
    };
    "liftAt-auto-homogeneous-term-erases" = {
      expr = (elab (liftAt 0 0 nat zero)).tag;
      expected = "desc-con";
    };
    "lowerAt-auto-homogeneous-term-erases" = {
      expr = (elab (lowerAt 0 0 nat zero)).tag;
      expected = "desc-con";
    };
    "liftAt-auto-heterogeneous-term-keeps-node" = {
      expr = (elab (liftAt 0 1 nat zero)).tag;
      expected = "lift-intro";
    };
    "LiftAtWithEq-homogeneous-keeps-proof-node" = {
      expr = (LiftAtWithEq 0 0 (throw "eq witness should remain lazy") nat)._htag;
      expected = "lift";
    };
    "liftAtWithEq-homogeneous-keeps-proof-node" = {
      expr = (liftAtWithEq 0 0 (throw "eq witness should remain lazy") nat zero)._htag;
      expected = "lift-intro";
    };
    "lowerAtWithEq-homogeneous-keeps-proof-node" = {
      expr = (lowerAtWithEq 0 0 (throw "eq witness should remain lazy") nat zero)._htag;
      expected = "lift-elim";
    };
    "elab-list" = { expr = (elab (listOf nat)).tag; expected = "app"; };
    "elab-sum" = { expr = (elab (sum nat bool)).tag; expected = "app"; };
    "elab-eq" = { expr = (elab (eq nat zero zero)).tag; expected = "app"; };

    # -- Binding type: forall --
    "elab-forall-tag" = {
      expr = (elab (forall "x" nat (_: nat))).tag;
      expected = "pi";
    };
    "elab-forall-domain" = {
      expr = (elab (forall "x" nat (_: nat))).domain.tag;
      expected = "mu";
    };
    "elab-forall-body-var" = {
      # forall "x" Nat (x: x) — body is Var(0)
      expr = (elab (forall "x" nat (x: x))).codomain.tag;
      expected = "var";
    };
    "elab-forall-body-idx" = {
      expr = (elab (forall "x" nat (x: x))).codomain.idx;
      expected = 0;
    };

    # -- Binding type: sigma --
    "elab-sigma-tag" = {
      expr = (elab (sigma "x" nat (_: bool))).tag;
      expected = "sigma";
    };

    # -- Binding terms: lam --
    "elab-lam-tag" = {
      expr = (elab (lam "x" nat (x: x))).tag;
      expected = "lam";
    };
    "elab-lam-body-idx" = {
      expr = (elab (lam "x" nat (x: x))).body.idx;
      expected = 0;
    };

    # -- let_ --
    "elab-let-tag" = {
      expr = (elab (let_ "x" nat zero (x: x))).tag;
      expected = "let";
    };

    # -- Non-binding terms --
    "elab-zero" = { expr = (elab zero).tag; expected = "desc-con"; };
    "elab-succ" = { expr = (elab (succ zero)).tag; expected = "desc-con"; };
    "elab-true" = { expr = (elab true_).tag; expected = "desc-con"; };
    "elab-false" = { expr = (elab false_).tag; expected = "desc-con"; };
    "elab-tt" = { expr = (elab tt).tag; expected = "tt"; };
    # nil/cons elaborate to desc-con whose payload is `boot-inl …`/`boot-inr …`,
    # selecting the nil vs cons summand of the generated listDesc.
    "elab-nil" = {
      expr = let t = elab (HI.nilAtExplicit nat); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };
    "elab-cons" = {
      expr = let t = elab (HI.consAtExplicit nat zero (HI.nilAtExplicit nat)); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };
    "elab-pair" = { expr = (elab (pair zero true_)).tag; expected = "pair"; };
    # inl/inr elaborate to desc-con whose payload is `boot-inl …`/`boot-inr …`,
    # selecting the left vs right summand of the generated sumDesc.
    "elab-inl" = {
      expr = let t = elab (HI.inlAtExplicit 0 nat bool zero); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };
    "elab-inr" = {
      expr = let t = elab (HI.inrAtExplicit 0 nat bool true_); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };
    "elab-just" = {
      expr = let t = elab (self.just nat zero); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };
    "elab-nothing" = {
      expr = let t = elab (self.nothing nat); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };
    "elab-variantInject-first" = {
      expr =
        let
          v = self.variant [
            { tag = "A"; type = nat; }
            { tag = "B"; type = bool; }
          ];
          t = elab (self.variantInject v "A" zero);
        in
        "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };
    "elab-variantInject-second" = {
      expr =
        let
          v = self.variant [
            { tag = "A"; type = nat; }
            { tag = "B"; type = bool; }
          ];
          t = elab (self.variantInject v "B" true_);
        in
        "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };
    "check-public-refl" = {
      expr = (checkHoas (eq nat zero zero) refl).tag;
      expected = "desc-con";
    };
    "elab-ann" = { expr = (elab (ann zero nat)).tag; expected = "ann"; };
    "elab-app" = { expr = (elab (app (lam "x" nat (x: x)) zero)).tag; expected = "app"; };
    "elab-absurd" = { expr = (elab (absurd nat (lam "x" void (x: x)))).tag; expected = "absurd"; };
    "elab-fst" = { expr = (elab (fst_ (pair zero true_))).tag; expected = "fst"; };
    "elab-snd" = { expr = (elab (snd_ (pair zero true_))).tag; expected = "snd"; };

    # -- Error path: non-serializable value doesn't crash toJSON --
    "elab-error-non-serializable" = {
      expr = (builtins.tryEval (elab (x: x))).success;
      expected = false;
    };

    # -- Sentinel hardening: {_hoas=true} is NOT a marker --
    "elab-reject-fake-marker" = {
      expr = (builtins.tryEval (elab { _hoas = true; level = 0; })).success;
      expected = false;
    };

    # -- Eliminators --
    # nat-elim surface combinator elaborates to nested let-bindings around
    # a desc-ind: `let P = motive in let B = base in let S = step in
    # desc-ind …`. The let-wrapping makes motive/step/base inferable (VAR
    # via lookupType) so the descInd check rule can type the body.
    "elab-nat-elim" = {
      expr = (elab (ind 0 (lam "n" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
        zero)).tag;
      expected = "let";
    };
    "elab-bool-elim" = {
      expr = (elab (boolElim 0 (lam "b" bool (_: nat)) zero (succ zero) true_)).tag;
      expected = "app";
    };

    # -- Nested binding: de Bruijn indices correct --
    "elab-nested-var-outer" = {
      # forall "A" U0 (A: forall "x" A (_: A))
      # Inner body uses A which is at depth 0 when bound, now at depth 2
      # So idx = 2 - 0 - 1 = 1
      expr = (elab (forall "A" (u 0) (a:
        forall "x" a (_: a)))).codomain.codomain.idx;
      expected = 1;
    };
    "elab-nested-var-inner" = {
      # forall "A" U0 (A: forall "x" A (x: x))
      # x is at depth 1, used at depth 2 → idx = 2 - 1 - 1 = 0
      expr = (elab (forall "A" (u 0) (_:
        forall "x" nat (x: x)))).codomain.codomain.idx;
      expected = 0;
    };

    # -- natLit helper --
    "natLit-0" = { expr = (elab (natLit 0)).tag; expected = "desc-con"; };
    "natLit-3" = { expr = (elab (natLit 3)).tag; expected = "desc-con"; };

    # -- Stack safety: deep succ chain elaboration --
    "elab-succ-5000" = {
      expr = let tm = elab (natLit 5000); in tm.tag;
      expected = "desc-con";
    };

    # -- Stack safety: deep nested Pi chain elaboration --
    "elab-pi-8000" = {
      expr =
        let
          deepPi = builtins.foldl'
            (acc: _:
              forall "_" nat (_: acc)
            )
            nat
            (builtins.genList (x: x) 8000);
          tm = elab deepPi;
        in
        tm.tag;
      expected = "pi";
    };

    # -- Stack safety: deep nested Lam chain elaboration --
    "elab-lam-8000" = {
      expr =
        let
          deepLam = builtins.foldl'
            (acc: _:
              lam "_" nat (_: acc)
            )
            zero
            (builtins.genList (x: x) 8000);
          tm = elab deepLam;
        in
        tm.tag;
      expected = "lam";
    };

    # -- Stack safety: deep Pi-telescope ending in Eq (EqDT-witness path) --
    # A telescope ending in a 3-arg Eq spine drives checkHoas's shared-Eq
    # witness derivation (checkedEqWitnesses -> peelTmTelescope), which
    # descends the kernel-built Pi Tm spine. A native descent grows the
    # host stack one frame per binder; the heap worklist keeps it bounded.
    # Depth exceeds the native walk budget, so the worklist fallback runs.
    "check-deep-pi-eq-2000" = {
      expr =
        let
          deepPi = builtins.foldl'
            (acc: _: forall "_" nat (_: acc))
            (eq nat zero zero)
            (builtins.genList (x: x) 2000);
          deepLam = builtins.foldl'
            (acc: _: lam "_" nat (_: acc))
            refl
            (builtins.genList (x: x) 2000);
        in
        (checkHoas deepPi deepLam).tag;
      expected = "lam";
    };

    # -- Stack safety: deep cons chain elaboration --
    "elab-cons-5000" = {
      expr =
        let
          bigList = builtins.foldl'
            (acc: _:
              HI.consAtExplicit nat zero acc
            )
            (HI.nilAtExplicit nat)
            (builtins.genList (x: x) 5000);
          tm = elab bigList;
        in
        tm.tag;
      expected = "desc-con";
    };

    "check-generated-nat-5000" = {
      expr = (checkHoas nat (natLit 5000)).tag;
      expected = "desc-con";
    };

    "check-generated-list-5000" = {
      expr =
        let
          bigList = builtins.foldl'
            (acc: _:
              cons zero acc
            )
            nil
            (builtins.genList (x: x) 5000);
        in
        (checkHoas (listOf nat) bigList).tag;
      expected = "desc-con";
    };

    # ===== Kernel integration: type-check elaborated terms =====

    # Zero : Nat — descCon natDesc (boot-inl …)
    "check-zero" = {
      expr = let t = checkHoas nat zero; in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # S(S(0)) : Nat — outer desc-con has payload `boot-inr …`; inner is s(0).
    "check-succ2" = {
      expr = let t = checkHoas nat (succ (succ zero)); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };

    # True : Bool
    "check-true" = {
      expr = (checkHoas bool true_).tag;
      expected = "desc-con";
    };

    # () : Unit
    "check-tt" = {
      expr = (checkHoas unit tt).tag;
      expected = "tt";
    };

    # nil : List Nat — descCon (listDesc nat) (boot-inl …)
    "check-nil" = {
      expr = let t = checkHoas (listOf nat) nil; in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # cons 0 nil : List Nat — descCon (listDesc nat) (boot-inr …)
    "check-cons" = {
      expr = let t = checkHoas (listOf nat) (cons zero nil); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };

    # inl 0 : Sum Nat Bool — descCon (sumDesc nat bool) (boot-inl …)
    "check-inl" = {
      expr = let t = checkHoas (sum nat bool) (inl zero); in
        "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # inl leZ : Sum (le 0 2) Nat — the Left summand is an INDEXED inductive
    # family (`Le`), so the inner ctor must flatten and recover its implicit
    # index from the field type. Regression guard: a level-sort param must
    # not be `ann`-ascribed (else `fieldLiftType` lift-wraps the field type,
    # `dtypeView` declines, and the payload leaks with its index unsolved).
    "check-inl-indexed-family" = {
      expr = let
        le02 = le (natLit 0) (natLit 2);
        t = checkHoas (sum le02 nat) (inl leZ);
      in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # inl nil : Sum (List Nat) Nat — Left summand is a PARAMETRIC family.
    "check-inl-parametric-family" = {
      expr = let t = checkHoas (sum (listOf nat) nat) (inl nil); in
        "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # yes le02 leZ : Dec (le 0 2) — `Dec` over an indexed family; exercises
    # the decision vocabulary (`decideLeNat`/`decideEqNat`) in CHECKING
    # position, previously only validated via `Q.nf` normalization.
    "check-dec-yes-indexed-family" = {
      expr = let
        le02 = le (natLit 0) (natLit 2);
        t = checkHoas (dec le02) (yes le02 leZ);
      in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inl";
    };

    # pair(0, true) : Σ(x:Nat).Bool
    "check-pair" = {
      expr = (checkHoas (sigma "x" nat (_: bool)) (pair zero true_)).tag;
      expected = "pair";
    };

    # H.refl : H.eq H.nat 0 0
    "check-refl" = {
      expr = (checkHoas (eq nat zero zero) refl).tag;
      expected = "desc-con";
    };

    # ===== Theorem tests =====

    # Polymorphic identity: λ(A:U₀). λ(x:A). x  :  Π(A:U₀). A → A
    "theorem-poly-id" = {
      expr =
        let
          ty = forall "A" (u 0) (a: forall "x" a (_: a));
          tm = lam "A" (u 0) (a: lam "x" a (x: x));
        in
        (checkHoas ty tm).tag;
      expected = "lam";
    };

    # 0 + 0 = 0 by computation: generated natural induction reduces to 0.
    "theorem-0-plus-0" = {
      expr =
        let
          addZero = ind 0 (lam "n" nat (_: nat)) zero
            (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
            zero;
          eqTy = eq nat addZero zero;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # n + 0 = n by induction:
    #   motive: λn. H.eq H.nat (add(n,0)) n
    #   base: H.refl  (add(0,0) = 0 by computation)
    #   step: λk. λih. cong succ ih  (where add(S(k),0) = S(add(k,0)))
    # cong f p = H.j(A, a, λb.λ_. H.eq(B, f(a), f(b)), refl, b, p)
    # For our purposes, since add(S(k), 0) computes to S(add(k, 0)) by the
    # generated natural step, and ih : add(k,0) = k, we need:
    #   S(add(k,0)) = S(k), which follows from congruence on ih.
    #
    # Since add is defined by generated natural induction, its S(k) case
    # computes the step, we get: add(S(k), 0) = S(add(k, 0)). Combined
    # with ih : add(k,0) = k we need S(add(k,0)) = S(k). The J eliminator
    # can produce this.
    #
    # This local HOAS smoke test uses a concrete case, where normalization
    # makes H.refl sufficient. The library-level universal proof lives in
    # examples/category-theory/arithmetic.nix as addRightZero.
    "theorem-3-plus-0-eq-3" = {
      expr =
        let
          three = succ (succ (succ zero));
          add_n_0 = ind 0 (lam "n" nat (_: nat)) zero
            (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
            three;
          eqTy = eq nat add_n_0 three;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # Dependent pair: (0, H.refl) : Σ(x:Nat). H.eq H.nat x 0
    "theorem-dep-pair" = {
      expr =
        let
          ty = sigma "x" nat (x: eq nat x zero);
          tm = pair zero refl;
        in
        (checkHoas ty tm).tag;
      expected = "pair";
    };

    # BoolElim type-checks: if true then 0 else 1 : Nat
    # `nat` is `mu natDesc`, so the inferred value tag is "VMu".
    "theorem-bool-elim" = {
      expr =
        let
          tm = boolElim 0 (lam "b" bool (_: nat)) zero (succ zero) true_;
        in
        (inferHoas (ann tm nat)).type.tag;
      expected = "VMu";
    };

    # ===== Description-based prelude integration =====
    # End-to-end semantic checks that the μ-description rebind of
    # Nat/List/Sum computes the same values as the primitive
    # representations under conv.

    # add(2, 3) = 5 on description-based Nat — exercises the rebound
    # `ind` adapter (let-bound P/B/S around descInd) plus Σ-η + ⊤-η in
    # the step.
    "integration-desc-nat-add-2-3" = {
      expr =
        let
          two = succ (succ zero);
          three = succ (succ (succ zero));
          five = succ (succ (succ (succ (succ zero))));
          # Bidirectional discipline: bare lambdas are not inferable, so a
          # function value used as an `app` head needs an explicit Π
          # annotation. Without it, INFER on `app addTm two` would have
          # to INFER on the lambda head — which is structurally rejected.
          addTm = ann
            (lam "m" nat (m: lam "n" nat (n:
              ind 0 (lam "_" nat (_: nat))
                n
                (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                m)))
            (forall "m" nat (_: forall "n" nat (_: nat)));
          eqTy = eq nat (app (app addTm two) three) five;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # length [0, 0, 0] = 3 on description-based List — exercises the
    # rebound `listElim` adapter (let-bound P/N/C around descInd) on the
    # cons chain.
    "integration-desc-list-length-3" = {
      expr =
        let
          zeros = HI.consAtExplicit nat zero (HI.consAtExplicit nat zero (HI.consAtExplicit nat zero (HI.nilAtExplicit nat)));
          three = succ (succ (succ zero));
          lenTm = listElim 0 nat (lam "_" (listOf nat) (_: nat))
            zero
            (lam "h" nat (_:
              lam "t" (listOf nat) (_:
                lam "ih" nat (ih: succ ih))))
            zeros;
          eqTy = eq nat lenTm three;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # sumElim id id (inl Nat Nat 7) = 7 on description-based Sum —
    # exercises the rebound `sumElim` adapter (let-bound P/L/R around
    # descInd) with a constant motive Nat, where the trivial rih : ⊤ is
    # discharged in both arms.
    "integration-desc-sum-elim-inl" = {
      expr =
        let
          seven = succ (succ (succ (succ (succ (succ (succ zero))))));
          scrut = HI.inlAtExplicit 0 nat nat seven;
          motiveNat = lam "_" (sum nat nat) (_: nat);
          idNat = lam "n" nat (n: n);
          result = sumElim 0 nat nat motiveNat idNat idNat scrut;
          eqTy = eq nat result seven;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # sumElim id id (inr Nat Nat 4) = 4 — mirror test exercises the
    # right arm.
    "integration-desc-sum-elim-inr" = {
      expr =
        let
          four = succ (succ (succ (succ zero)));
          scrut = HI.inrAtExplicit 0 nat nat four;
          motiveNat = lam "_" (sum nat nat) (_: nat);
          idNat = lam "n" nat (n: n);
          result = sumElim 0 nat nat motiveNat idNat idNat scrut;
          eqTy = eq nat result four;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    # W-type wellformedness: μ(wDesc Bool (b: if b then Unit else Void)) : U(0).
    # `wDesc A B = descArg 0 A (a: descPi 0 (B a) descRet)` — B is a
    # Nix meta-level function (A → U at the HOAS surface), applied at
    # elaboration time. Exercises the descPi case in the kernel's Desc
    # check rule; `k = 0` pins both domains to `U(0)`.
    "integration-desc-wtype-wellformed" = {
      expr =
        let
          wDesc = A: B: descArg unit 0 A (a: descPi 0 (B a) descRet);
          wBool = wDesc bool (a:
            boolElim 1 (lam "_" bool (_: u 0)) unit void a);
        in
        (checkHoas (u 0) (mu wBool tt)).tag;
      expected = "mu";
    };

    # ===== Roundtrip: elaborate → eval → quote → eval → quote =====

    "roundtrip-lam-id" = {
      expr =
        let
          tm = elab (lam "x" nat (x: x));
        in
        Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };

    "roundtrip-forall" = {
      expr =
        let
          tm = elab (forall "A" (u 0) (a: forall "x" a (_: a)));
        in
        Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };

    "roundtrip-sigma" = {
      expr =
        let
          tm = elab (sigma "x" nat (_: bool));
        in
        Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };

    "roundtrip-nat-elim" = {
      expr =
        let
          tm = elab (ind 0 (lam "n" nat (_: nat)) zero
            (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
            (succ (succ zero)));
        in
        Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };

    "roundtrip-natLit-5" = {
      expr =
        let tm = elab (natLit 5);
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };

    # Stress test — stack safety (B4)
    "natLit-5000" = {
      expr = (elab (natLit 5000)).tag;
      expected = "desc-con";
    };

    # ===== Primitive type elaboration =====

    "elab-string" = { expr = (elab string).tag; expected = "string"; };
    "elab-int" = { expr = (elab int_).tag; expected = "int"; };
    "elab-float" = { expr = (elab float_).tag; expected = "float"; };
    "elab-attrs" = { expr = (elab attrs).tag; expected = "attrs"; };
    "elab-path" = { expr = (elab path).tag; expected = "path"; };
    "elab-function" = { expr = (elab function_).tag; expected = "function"; };
    "elab-any" = { expr = (elab any).tag; expected = "any"; };

    # ===== Primitive literal elaboration =====

    "elab-string-lit" = { expr = (elab (stringLit "hi")).tag; expected = "string-lit"; };
    "elab-string-lit-value" = { expr = (elab (stringLit "hi")).value; expected = "hi"; };
    "elab-int-lit" = { expr = (elab (intLit 42)).tag; expected = "int-lit"; };
    "elab-int-lit-value" = { expr = (elab (intLit 42)).value; expected = 42; };
    "elab-float-lit" = { expr = (elab (floatLit 3.14)).tag; expected = "float-lit"; };
    "elab-float-lit-value" = { expr = (elab (floatLit 3.14)).value; expected = 3.14; };
    "elab-attrs-lit" = { expr = (elab attrsLit).tag; expected = "attrs-lit"; };
    "elab-path-lit" = { expr = (elab pathLit).tag; expected = "path-lit"; };
    "elab-fn-lit" = { expr = (elab fnLit).tag; expected = "fn-lit"; };
    "elab-any-lit" = { expr = (elab anyLit).tag; expected = "any-lit"; };

    # ===== Primitive kernel integration =====

    "check-string-lit" = {
      expr = (checkHoas string (stringLit "hello")).tag;
      expected = "string-lit";
    };
    "check-int-lit" = {
      expr = (checkHoas int_ (intLit 7)).tag;
      expected = "int-lit";
    };
    "check-float-lit" = {
      expr = (checkHoas float_ (floatLit 2.5)).tag;
      expected = "float-lit";
    };
    "check-attrs-lit" = {
      expr = (checkHoas attrs attrsLit).tag;
      expected = "attrs-lit";
    };
    "check-path-lit" = {
      expr = (checkHoas path pathLit).tag;
      expected = "path-lit";
    };
    "check-fn-lit" = {
      expr = (checkHoas function_ fnLit).tag;
      expected = "fn-lit";
    };
    "check-any-lit" = {
      expr = (checkHoas any anyLit).tag;
      expected = "any-lit";
    };

    # ===== Opaque lambda: trust boundary for Pi =====

    "elab-opaque-lam" = {
      expr = (elab (opaqueLam (x: x) (forall "x" nat (_: nat)))).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda checks at matching Pi type
    "opaque-lam-checks-at-pi" = {
      expr =
        let
          piTy = forall "x" nat (_: nat);
        in
        (checkHoas piTy (opaqueLam (x: x) piTy)).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda rejects domain mismatch
    "opaque-lam-rejects-domain-mismatch" = {
      expr =
        let
          targetPi = forall "x" nat (_: nat);
          annotPi = forall "x" bool (_: nat);
        in
        (checkHoas targetPi (opaqueLam (x: x) annotPi)) ? error;
      expected = true;
    };

    # Opaque lambda rejects non-Pi target type
    "opaque-lam-rejects-non-pi" = {
      expr = (checkHoas nat (opaqueLam (x: x) (forall "x" nat (_: nat)))) ? error;
      expected = true;
    };

    # Opaque lambda infers Pi type from annotation
    "opaque-lam-infers-pi-type" = {
      expr =
        let
          piTy = forall "x" nat (_: nat);
          result = inferHoas (ann (opaqueLam (x: x) piTy) piTy);
        in
        result.type.tag;
      expected = "VPi";
    };

    # Opaque lambda quote roundtrip: eval → quote → eval = same structure
    "opaque-lam-quote-roundtrip" = {
      expr =
        let
          H = { inherit nat forall opaqueLam elab; };
          piTy = H.forall "x" H.nat (_: H.nat);
          tm = H.elab (H.opaqueLam (x: x) piTy);
          Q' = fx.tc.quote;
        in
        Q'.nf [ ] (Q'.nf [ ] tm) == Q'.nf [ ] tm;
      expected = true;
    };

    # Conv: same Nix function → conv-equal
    "opaque-lam-conv-reflexive" = {
      expr =
        let
          f = x: x;
          piTy = forall "x" nat (_: nat);
          tm1 = elab (opaqueLam f piTy);
          tm2 = elab (opaqueLam f piTy);
          E' = fx.tc.eval;
          C' = fx.tc.conv;
          v1 = E'.eval [ ] tm1;
          v2 = E'.eval [ ] tm2;
        in
        C'.conv 0 v1 v2;
      expected = true;
    };

    # Conv: different Nix functions → not conv-equal
    "opaque-lam-conv-distinct" = {
      expr =
        let
          f = x: x;
          g = x: succ x;
          piTy = forall "x" nat (_: nat);
          tm1 = elab (opaqueLam f piTy);
          tm2 = elab (opaqueLam g piTy);
          E' = fx.tc.eval;
          C' = fx.tc.conv;
          v1 = E'.eval [ ] tm1;
          v2 = E'.eval [ ] tm2;
        in
        C'.conv 0 v1 v2;
      expected = false;
    };

    # ----- Description-level acceptance tests -----

    # descArg at level k=0 with body at level 0 yields a desc-shape
    # whose post-encoding type is `μ ⊤ (descDesc nat 0) tt`, conv-equal
    # to `descIAt levelZero nat`. The encoded form makes a direct
    # `r.type.level` assertion structurally unavailable; conv against
    # the canonical `descIAt levelZero nat` shape captures the same
    # invariant. The body's `retI nat 0 zero` threads `zero : nat` so
    # `j : I = nat` is well-typed.
    "descArg-level-zero-infers-desc-zero" = {
      expr =
        let
          r = inferHoas (descArg nat 0 nat (s: retI nat 0 zero));
          target = E.eval [ ] (elab (descIAt levelZero nat));
        in
        C.conv 0 r.type target;
      expected = true;
    };
    # descArg at level k=1 with body at level 1 yields a desc-shape
    # conv-equal to `descIAt (suc 0) unit`.
    "descArg-level-one-infers-desc-one" = {
      expr =
        let
          r = inferHoas (descArg unit 1 (u 0) (S: retI unit 1 (ann tt unit)));
          target = E.eval [ ] (elab (descIAt (levelSuc levelZero) unit));
        in
        C.conv 0 r.type target;
      expected = true;
    };
    # Polymorphic descArg: `Π(k:Level). desc^(suc k) ⊤`. Witnesses that
    # the kVar at the descArg's level slot threads through to the
    # inferred result type's level — closing the universe-polymorphism
    # loop end-to-end. The body's `retI unit (suc k) tt` matches the
    # outer level so the homogeneous-l descArg form type-checks.
    "descArg-level-polymorphic-checks" = {
      expr = (checkHoas
        (forall "k" level (k: descIAt (levelSuc k) unit))
        (lam "k" level (k: descArg unit (levelSuc k) (u k) (S: retI unit (levelSuc k) (ann tt unit))))) ? error;
      expected = false;
    };

    # ----- Universe-polymorphism of I in `Desc^k I` (CDMM 2010 formation
    # rule: `Desc^k I : U(suc (max k iLev))` for `I : U(iLev)`) -----

    # Small-I sanity: `Desc^0 nat : U(1)`. iLev = 0; max(0,0) = 0;
    # universe = U(suc 0).
    "descIAt-zero-nat-infers-at-U1" = {
      expr =
        let
          r = inferHoas (descIAt 0 nat);
          target = E.eval [ ] (elab (u 1));
        in
        C.conv 0 r.type target;
      expected = true;
    };

    # Higher-universe I: `Desc^0 (U(0) × U(0))` admits I at U(1).
    # The sigma `Σ(X:U(0)). U(0)` lives at U(1); pre-lift this faulted
    # at the I:U(0) clamp.
    "descIAt-zero-U-cross-U-admits" = {
      expr = (inferHoas (descIAt 0 (sigma "X" (u 0) (_X: u 0)))) ? error;
      expected = false;
    };

    # …and inhabits `U(2) = U(suc (max 0 1))`.
    "descIAt-zero-U-cross-U-infers-at-U2" = {
      expr =
        let
          r = inferHoas (descIAt 0 (sigma "X" (u 0) (_X: u 0)));
          target = E.eval [ ] (elab (u 2));
        in
        C.conv 0 r.type target;
      expected = true;
    };

    # Mu rule admits higher-universe I via a Π-binder over a description
    # variable. The Π form `Π(D:Desc^0 (U×U)). μI (U×U) D (pair nat bool)`
    # exercises the desc → mu chain at I = U×U entirely through kernel-
    # primitive rules: descIAt produces D's domain at U(2); muI consumes
    # I and D at the lifted universes. The Π itself lives at U(2)
    # = U(max (Desc^0(U×U)).level (μI ...).level) = U(max 2 1).
    "lifted-pi-desc-mu-at-U-cross-U-checks-at-U2" = {
      expr =
        let
          I = sigma "X" (u 0) (_X: u 0);
          i0 = ann (pair nat bool) I;
        in
        (checkHoas
          (u 2)
          (forall "D" (descIAt 0 I) (D: muI I D i0))) ? error;
      expected = false;
    };

    # Encoder cascade at iLev=1: I = U(0)×U(0) lives at U(1), so the
    # encoder's Π(I:U(iLev)) accepts it only when iLev is threaded.
    "retIAtI-at-U-cross-U-elaborates" = {
      expr =
        let
          iLev1 = levelSuc levelZero;
          I = sigma "X" (u 0) (_X: u 0);
          j = ann (pair nat bool) I;
        in
        (inferHoas (retIAtI iLev1 I levelZero j)) ? error;
      expected = false;
    };

    "retIAtI-at-U-cross-U-inner-descDesc-stamp-carries-iLev" = {
      expr =
        let
          iLev1 = levelSuc levelZero;
          I = sigma "X" (u 0) (_X: u 0);
          j = ann (pair nat bool) I;
          v = E.eval [ ] (elab (retIAtI iLev1 I levelZero j));
          params = v.D._canonRef.params;
        in
        {
          id = v.D._canonRef.id;
          arity = builtins.length params;
          iLevTag = (builtins.elemAt params 0).tag;
          iTag = (builtins.elemAt params 1).tag;
          kTag = (builtins.elemAt params 2).tag;
        };
      expected = {
        id = "descDesc";
        arity = 3;
        iLevTag = "VLevelSuc";
        iTag = "VSigma";
        kTag = "VLevelZero";
      };
    };

    # End-to-end encoder → mu at iLev=1.
    "muIAtI-at-U-cross-U-with-retIAtI" = {
      expr =
        let
          iLev1 = levelSuc levelZero;
          I = sigma "X" (u 0) (_X: u 0);
          j = ann (pair nat bool) I;
          D = retIAtI iLev1 I levelZero j;
        in
        (inferHoas (muIAtI iLev1 I D j)) ? error;
      expected = false;
    };

    # Default iLev=0 clamps I to U(0); I:U(1) must be rejected.
    "retI-default-iLev-rejects-U-cross-U" = {
      expr =
        let
          I = sigma "X" (u 0) (_X: u 0);
          j = ann (pair nat bool) I;
        in
        (inferHoas (retI I levelZero j)) ? error;
      expected = true;
    };

    # Same rejection through the *AtI surface with explicit iLev=0.
    "retIAtI-iLev-zero-rejects-U-cross-U" = {
      expr =
        let
          I = sigma "X" (u 0) (_X: u 0);
          j = ann (pair nat bool) I;
        in
        (inferHoas (retIAtI levelZero I levelZero j)) ? error;
      expected = true;
    };

    # descDesc : Π(iLev : Level)(I : U(iLev))(k : Level). Desc^(suc(max k iLev)) ⊤ — type-checks
    # at the polymorphic universe-tracking forall, and instantiates
    # cleanly at I = ⊤ and sample levels k ∈ {0, 1, 2}. The arg / pi
    # summands quantify over `S : U(k)` with leading level `(suc k)`,
    # forcing the description to live at `desc^(suc k) ⊤`. The ret /
    # rec summands prefix `descArgAt 0 (suc k) I` to encode the
    # I-typed leaf index of `descRet I i` / `descRec I i D`.
    "descDesc-type-checks" = {
      expr = (checkHoas
        (forall "iLev" level (iLev:
          forall "I" (u iLev) (I:
            forall "k" level (k: descAt (levelSuc (levelMax k iLev))))))
        descDesc) ? error;
      expected = false;
    };
    "descDesc-at-unit-level-zero" = {
      expr = (checkHoas
        (descAt (levelSuc levelZero))
        (app (app (app descDesc levelZero) unit) levelZero)).tag;
      expected = "app";
    };
    "descDesc-at-unit-level-one" = {
      expr = (checkHoas
        (descAt (levelSuc (levelSuc levelZero)))
        (app (app (app descDesc levelZero) unit) (levelSuc levelZero))) ? error;
      expected = false;
    };
    "descDesc-at-unit-level-two" = {
      expr = (checkHoas
        (descAt (levelSuc (levelSuc (levelSuc levelZero))))
        (app (app (app descDesc levelZero) unit) (levelSuc (levelSuc levelZero)))) ? error;
      expected = false;
    };
    # Instantiate at I = bool, level zero. Verifies the I-thread
    # accepts non-⊤ index types (the eqDesc-style use case).
    "descDesc-at-bool-level-zero" = {
      expr = (checkHoas
        (descAt (levelSuc levelZero))
        (app (app (app descDesc levelZero) bool) levelZero)) ? error;
      expected = false;
    };

    # ===== __descDesc reserved identifier =====
    #
    # Canonical surface name for the prelude description-of-descriptions
    # term. Elaborates directly to the pre-elaborated `self.descDescTm`
    # — call sites that emit `__descDesc` references avoid re-walking
    # the HOAS tree on every use. Type-checks at the same polymorphic
    # signature as the camelCase `descDesc` since they elaborate to
    # identical Tms.
    "elab-__descDesc-equals-descDescTm" = {
      expr = elab __descDesc == self.descDescTm;
      expected = true;
    };
    "__descDesc-type-checks" = {
      expr = (checkHoas
        (forall "iLev" level (iLev:
          forall "I" (u iLev) (I:
            forall "k" level (k: descAt (levelSuc (levelMax k iLev))))))
        __descDesc) ? error;
      expected = false;
    };
    "__descDesc-at-unit-level-zero" = {
      expr = (checkHoas
        (descAt (levelSuc levelZero))
        (app (app (app __descDesc levelZero) unit) levelZero)).tag;
      expected = "app";
    };

    # Pre-elaborated closed deciders dispatch through the `pre-elab`
    # opaque HOAS node. Each pair (`decideXxx`, `decideXxxHoas`) must
    # elaborate to the identical Tm — closed-term invariance proven by
    # equality of the two elaboration paths. Same precedent as
    # `elab-__descDesc-equals-descDescTm` above.
    "elab-decideEqNat-equals-decideEqNatTm" = {
      expr = elab self.decideEqNat == self.decideEqNatTm
        && self.decideEqNatTm == elab self.decideEqNatHoas;
      expected = true;
    };
    "elab-decideLeNat-equals-decideLeNatTm" = {
      expr = elab self.decideLeNat == self.decideLeNatTm
        && self.decideLeNatTm == elab self.decideLeNatHoas;
      expected = true;
    };
    "elab-decideEqIntZ-equals-decideEqIntZTm" = {
      expr = elab self.decideEqIntZ == self.decideEqIntZTm
        && self.decideEqIntZTm == elab self.decideEqIntZHoas;
      expected = true;
    };
    "elab-decideLeIntZ-equals-decideLeIntZTm" = {
      expr = elab self.decideLeIntZ == self.decideLeIntZTm
        && self.decideLeIntZTm == elab self.decideLeIntZHoas;
      expected = true;
    };

    # ===== iso identity / descDesc-faithfulness regression =====
    #
    # `isoIdentity : Π(I:U(0))(k:Level). Iso (Desc^k I) (μ(descDesc I k) tt)`
    # constructed as identity / refl bundle (see top of file). The
    # kernel's Desc/μ unfolding conv rule equates the two presentations
    # definitionally, so the identity witnesses typecheck against
    # `isoTy` and round-trips collapse to β-η. These tests pin both
    # the polymorphic type-shape and the conv rule's continued
    # consistency with `descDesc`'s body — if the encoding drifts,
    # `isoIdentity` fails to elaborate.

    "iso-type-checks-polymorphic" = {
      expr = (inferHoas isoIdentity).type.tag;
      expected = "VPi";
    };

    # Instantiation at I = ⊤ and concrete levels — confirms the Π
    # body normalises to the Σ-bundle (the Iso record) at each k.
    "iso-at-level-zero-instantiates" = {
      expr = (inferHoas (app (app (app isoIdentity levelZero) unit) levelZero)).type.tag;
      expected = "VSigma";
    };
    "iso-at-level-one-instantiates" = {
      expr = (inferHoas (app (app (app isoIdentity levelZero) unit) (levelSuc levelZero))).type.tag;
      expected = "VSigma";
    };
    "iso-at-level-two-instantiates" = {
      expr = (inferHoas (app (app (app isoIdentity levelZero) unit) (levelSuc (levelSuc levelZero)))).type.tag;
      expected = "VSigma";
    };

    # Instantiation at I ≠ ⊤ — verifies the I-thread accepts non-⊤
    # index types, the prerequisite for `eqDesc A a : Desc A` round-
    # tripping through the descDesc encoding.
    "iso-at-bool-level-zero-instantiates" = {
      expr = (inferHoas (app (app (app isoIdentity levelZero) bool) levelZero)).type.tag;
      expected = "VSigma";
    };

    # Round-trip `from(to D) ≡ D` on prelude descriptions at I=⊤, k=0.
    # Each exercises a different mix of `descDesc ⊤ 0`'s plus-coproduct
    # summands: natDesc hits ret + rec; listDesc hits arg + rec + plus;
    # sumDesc hits arg + plus.
    "iso-roundtrip-natDesc-k0" = {
      expr =
        let
          iso0 = app (app (app isoIdentity levelZero) unit) levelZero;
          to0 = fst_ iso0;
          from0 = fst_ (snd_ iso0);
          roundTrip = app from0 (app to0 natDesc);
        in
        semEq roundTrip natDesc;
      expected = true;
    };
    "iso-roundtrip-listDesc-bool-k0" = {
      expr =
        let
          iso0 = app (app (app isoIdentity levelZero) unit) levelZero;
          to0 = fst_ iso0;
          from0 = fst_ (snd_ iso0);
          D = listDesc bool;
          roundTrip = app from0 (app to0 D);
        in
        semEq roundTrip D;
      expected = true;
    };
    "iso-roundtrip-sumDesc-nat-bool-k0" = {
      expr =
        let
          iso0 = app (app (app isoIdentity levelZero) unit) levelZero;
          to0 = fst_ iso0;
          from0 = fst_ (snd_ iso0);
          D = sumDesc nat bool;
          roundTrip = app from0 (app to0 D);
        in
        semEq roundTrip D;
      expected = true;
    };

    # Round-trip at I = bool, k = 0. `eqDesc bool true_ : Desc bool` is
    # a `retI true_` description — the Theorem 6.96 analogue. Exercises
    # to/from over the I-typed leaf-index encoding without recursion.
    "iso-roundtrip-eqDesc-bool-k0" = {
      expr =
        let
          isoBool0 = app (app (app isoIdentity levelZero) bool) levelZero;
          to0 = fst_ isoBool0;
          from0 = fst_ (snd_ isoBool0);
          D = eqDesc bool true_;
          roundTrip = app from0 (app to0 D);
        in
        semEq roundTrip D;
      expected = true;
    };

    # `toFrom natDesc : Eq (Desc^0 ⊤) (from(to natDesc)) natDesc` —
    # the proof component at a concrete input. Asserts the equality
    # proposition's well-typedness (the type tag is `VBootEq`).
    "iso-toFrom-natDesc-typechecks" = {
      expr =
        let
          iso0 = app (app (app isoIdentity levelZero) unit) levelZero;
          toFrom0 = fst_ (snd_ (snd_ iso0));
        in
        (inferHoas (app toFrom0 natDesc)).type.tag;
      expected = "VBootEq";
    };

    # ===== Indexed-description acceptance (I = Nat / I = Bool) =====
    # These exercise the indexed kernel path directly — the `descI`/`retI`
    # /`recI`/`piI` primitives at non-⊤ indices — rather than the ⊤-slice
    # aliases (`desc`/`descRet`/`descRec`/`descPi`) that specialise I to
    # Unit.

    # `retI 3 : Desc Nat` — j = 3 inhabits I = Nat.
    # Encoded `retI` checks against `descI nat`; the elaborated Tm is an
    # `mkApp ... encodeDescRetTm ...` chain whose value evaluates to the
    # encoded `VDescCon` constructor. Asserts the architectural invariant
    # at the value layer rather than the elaboration-internal Tm shape.
    "indexed-desc-ret-at-nat-checks" = {
      expr =
        let
          tm = checkHoas (descI nat) (retI nat 0 (natLit 3));
        in
        (E.eval [ ] tm).tag;
      expected = "VDescCon";
    };

    # `recI 2 (retI 3) : Desc Nat` — j = 2, subdesc `retI 3 : Desc Nat`.
    "indexed-desc-rec-at-nat-checks" = {
      expr =
        let
          tm = checkHoas (descI nat) (recI nat 0 (natLit 2) (retI nat 0 (natLit 3)));
        in
        (E.eval [ ] tm).tag;
      expected = "VDescCon";
    };

    # `piI 0 Bool (λb. boolElim _ 2 3 b) (retI 4) : Desc Nat` — the index
    # function is bool-dependent, exercising the non-constant f case.
    "indexed-desc-pi-at-nat-dependent-f" = {
      expr =
        let
          fAnn = ann
            (lam "b" bool (b:
              boolElim 0 (lam "_" bool (_: nat))
                (natLit 2)
                (natLit 3)
                b))
            (forall "_" bool (_: nat));
          D = piI nat 0 bool fAnn (retI nat 0 (natLit 4));
        in
        (checkHoas (descI nat) D).tag;
      expected = "app";
    };

    # Rejection: `retI 3 : Desc Bool` fails — j = 3 is a Nat, not a Bool.
    # The `desc-ret` CHECK rule at check.nix:174-177 threads `ty.I` into
    # the check on `tm.j`, producing a type mismatch.
    "indexed-desc-ret-wrong-index-rejects" = {
      expr = (checkHoas (descI bool) (retI bool 0 (natLit 3))) ? error;
      expected = true;
    };

    # `μ (retI 3 : Desc Nat) 3 : U(0)` — mu at the matching target index.
    "indexed-mu-at-nat-checks" = {
      expr = (checkHoas (u 0) (muI nat (retI nat 0 (natLit 3)) (natLit 3))).tag;
      expected = "mu";
    };

    # ===== Datatype macro =====
    # UnitDT: the n=1 degenerate case — singleton constructor with no
    # fields. D = descRet, T = μ descRet, tt = descCon D tt, elim P step
    # scrut reduces to step. Exercises the leaf dispatchStep with no
    # field or IH projection, and the n=1 no-tag encoding.

    "datatype-unit-spec-name" = {
      expr = (datatype "Unit" [ (con "tt" [ ]) ]).name;
      expected = "Unit";
    };
    "datatype-unit-spec-meta" = {
      expr = shallowMeta ((datatype "Unit" [ (con "tt" [ ]) ])._dtypeMeta);
      expected = {
        name = "Unit";
        indexed = false;
        indexTy = unitPrim;
        params = [ ];
        paramArgs = [ ];
        constructors = [{ name = "tt"; fields = [ ]; }];
      };
    };
    "datatype-unit-meta-has-no-cons-alias" = {
      expr = ((datatype "Unit" [ (con "tt" [ ]) ])._dtypeMeta) ? cons;
      expected = false;
    };
    # The macro emits D as `ann <spine> desc`; spine elaborates through
    # the encoded `mkApp ... encodeDescRetTm ...` form. Asserts the
    # post-encoding value-layer invariant: D evaluates to the encoded
    # `VDescCon` constructor.
    "datatype-unit-D-elab" = {
      expr =
        let
          D = (datatype "Unit" [ (con "tt" [ ]) ]).D;
        in
        (E.eval [ ] (elab D)).tag;
      expected = "VDescCon";
    };
    "datatype-unit-D-carries-desc-ref" = {
      expr =
        let
          d = E.eval [ ] (elab (datatype "Unit" [ (con "tt" [ ]) ]).D);
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 1;
        indexed = false;
        params = 0;
      };
    };
    "datatype-unit-T-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" [ ]) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" [ ]) ]).tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Unit" [ (con "tt" [ ]) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-check-T" = {
      expr =
        let U = datatype "Unit" [ (con "tt" [ ]) ];
        in (checkHoas U.T U.tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-elim-reduces-to-step" = {
      # elim (λ_:T. ⊤) tt U.tt  ≡nf≡  tt
      # The motive is constantly ⊤, the step is `tt : ⊤`, the scrutinee
      # is U.tt. descInd on the single-constructor μ descRet reduces
      # straight to the step (no field projection, no IH).
      expr =
        let
          U = datatype "Unit" [ (con "tt" [ ]) ];
          applied = app
            (app
              (app (U.elim 0)
                (lam "x" U.T (_: unit)))
              tt)
            U.tt;
        in
        semEq applied tt;
      expected = true;
    };
    # The macro elim must be INFERABLE as a closed term — bare lam
    # cascades are checkable-only in the bidirectional kernel, so the
    # macro wraps the elim in `ann <body> <full-Π-type>`. This test
    # fires an applied elim through `checkHoas` to prove the chain of
    # `app`s type-checks; nf-equivalence
    # (datatype-unit-elim-reduces-to-step) bypasses checking and would
    # silently mask a non-inferable elim.
    "datatype-unit-elim-checks" = {
      expr =
        let
          U = datatype "Unit" [ (con "tt" [ ]) ];
          applied = app
            (app
              (app (U.elim 0)
                (lam "x" U.T (_: unit)))
              tt)
            U.tt;
        in
        (checkHoas unit applied).tag;
      expected = "app";
    };
    # Direct inference of the closed elim: confirms `ann` pins a Π type
    # the kernel can recover without reducing the body.
    "datatype-unit-elim-infers-pi" = {
      expr =
        let U = datatype "Unit" [ (con "tt" [ ]) ];
        in (inferHoas (U.elim 0)).type.tag;
      expected = "VPi";
    };
    "datatype-rejects-n0" = {
      expr = (builtins.tryEval (datatype "Empty" [ ])).success;
      expected = false;
    };
    "datatype-rejects-duplicate-cons" = {
      expr = (builtins.tryEval
        (datatype "Dup" [ (con "a" [ ]) (con "a" [ ]) ])).success;
      expected = false;
    };

    # BoolDT: n=2 with both arms zero-field. Exercises:
    #   - spineDesc n>=2 (right-associated Bool tag spine).
    #   - encodeTag n>=2 (true_/false_ tag prefixes).
    #   - dispatchStep n>=2 branch case with leaf onTrue / onFalse,
    #     ctx threaded with `pair false_` for the second arm.
    "datatype-bool-spec-name" = {
      expr = (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).name;
      expected = "Bool";
    };
    "datatype-bool-spec-meta" = {
      expr = shallowMeta ((datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ])._dtypeMeta);
      expected = {
        name = "Bool";
        indexed = false;
        indexTy = unitPrim;
        params = [ ];
        paramArgs = [ ];
        constructors = [
          { name = "true"; fields = [ ]; }
          { name = "false"; fields = [ ]; }
        ];
      };
    };
    # Two zero-field ctors produce a plus-coproduct spineDesc with both
    # summands degenerate to descRet. After encoding, the elaborated Tm
    # is an `mkApp ... encodeDescPlusTm ...` chain; the value-layer
    # `VDescCon` assertion captures the architectural invariant.
    "datatype-bool-D-elab" = {
      expr =
        let
          D = (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).D;
        in
        (E.eval [ ] (elab D)).tag;
      expected = "VDescCon";
    };
    "datatype-bool-T-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).false).tag;
      expected = "desc-con";
    };
    # Macro D matches the canonical bool-fold structure: plus of two
    # descRet summands. Compared against a hand-written equivalent via
    # nf to absorb α-renaming.
    "datatype-bool-D-matches-handwritten" = {
      expr =
        let
          macroD = (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).D;
          handD = plus descRet descRet;
        in
        semEq macroD handD;
      expected = true;
    };
    "datatype-bool-D-carries-desc-ref" = {
      expr = let d = E.eval [ ] (elab self.boolDesc); in {
        kind = d._descRef.kind;
        arity = d._descRef.arity;
        indexed = d._descRef.indexed;
        params = builtins.length d._descRef.params;
      };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = false;
        params = 0;
      };
    };
    # True constructor's payload commits the 0th (`boot-inl`) summand of the
    # plus tree, with witness refl : Eq ⊤ tt tt at the ret-leaf.
    "datatype-bool-true-payload-shape" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
        in
        (elab B.true).d.tag;
      expected = "boot-inl";
    };
    # False constructor commits the 1st (`boot-inr`) summand.
    "datatype-bool-false-payload-shape" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
        in
        (elab B.false).d.tag;
      expected = "boot-inr";
    };
    "datatype-bool-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-check-T" = {
      expr =
        let B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
        in (checkHoas B.T B.true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-check-T" = {
      expr =
        let B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
        in (checkHoas B.T B.false).tag;
      expected = "desc-con";
    };
    # Closed elim is inferable as a Π type via the ann wrapper.
    "datatype-bool-elim-infers-pi" = {
      expr =
        let B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
        in (inferHoas (B.elim 0)).type.tag;
      expected = "VPi";
    };
    # Reduction on the true scrutinee selects step_true.
    # Motive: const ⊤. step_true = tt : ⊤. step_false = tt : ⊤.
    # elim P step_true step_false B.true ≡nf≡ tt.
    "datatype-bool-elim-reduces-true" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
          applied = app
            (app
              (app
                (app (B.elim 0)
                  (lam "_" B.T (_: unit)))
                tt)  # step_true
              tt)  # step_false
            B.true;
        in
        semEq applied tt;
      expected = true;
    };
    # Reduction on the false scrutinee selects step_false.
    # Discriminating motive (P b = if b then ⊤ else ⊤ — both arms
    # collapse to ⊤ because we have no second monomorphic ground type
    # in scope at U0 to distinguish them, but the dispatch chain is
    # still exercised structurally and verified by separately checking
    # that the elim chains through a non-collapsing motive in the next
    # test).
    "datatype-bool-elim-reduces-false" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
          applied = app
            (app
              (app
                (app (B.elim 0)
                  (lam "_" B.T (_: unit)))
                tt)
              tt)
            B.false;
        in
        semEq applied tt;
      expected = true;
    };
    # Distinguishing motive: P b = T (the BoolDT type itself).
    # step_true = B.false, step_false = B.true (negation).
    # elim P (B.false) (B.true) B.true ≡nf≡ B.false.
    # elim P (B.false) (B.true) B.false ≡nf≡ B.true.
    # This proves the boolElim dispatch genuinely picks the correct arm
    # rather than collapsing both to a common normal form.
    "datatype-bool-elim-negates-true" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
          neg = scrut: app
            (app
              (app
                (app (B.elim 0)
                  (lam "_" B.T (_: B.T)))
                B.false)
              B.true)
            scrut;
        in
        semEq (neg B.true) B.false;
      expected = true;
    };
    "datatype-bool-elim-negates-false" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
          neg = scrut: app
            (app
              (app
                (app (B.elim 0)
                  (lam "_" B.T (_: B.T)))
                B.false)
              B.true)
            scrut;
        in
        semEq (neg B.false) B.true;
      expected = true;
    };
    # Applied negation chain through checkHoas: proves the entire
    # `app`-cascade is type-checkable (the elim's ann wrapper makes the
    # head of the chain inferable; each step's check rule then
    # validates).
    "datatype-bool-elim-checks-applied" = {
      expr =
        let
          B = datatype "Bool" [ (con "true" [ ]) (con "false" [ ]) ];
          applied = app
            (app
              (app
                (app (B.elim 0)
                  (lam "_" B.T (_: B.T)))
                B.false)
              B.true)
            B.true;
        in
        (checkHoas B.T applied).tag;
      expected = "app";
    };

    # NatDT: n=2 with one fielded constructor (succ takes a recField).
    # Exercises:
    #   - conDesc with recField (descRec extension).
    #   - mkCtor curried lam over fields, ann-wrapped against the
    #     constructor's Π type.
    #   - stepTyOf with fielded cons: Π over the field, then Π over the
    #     IH, terminating in P (succ pred).
    #   - buildStepApply with field projection (fst payload) and IH
    #     projection (fst payloadIH).
    #   - nf-equivalence against the inline natElim adapter. Both
    #     eval-discard their type scaffolding (let_ vs ann) so the
    #     descInd reductions agree.
    "datatype-nat-spec-name" = {
      expr = (datatype "Nat" [
        (con "zero" [ ])
        (con "succ" [ (recField "pred") ])
      ]).name;
      expected = "Nat";
    };
    "datatype-nat-spec-meta" = {
      expr = shallowMeta (
        (datatype "Nat" [
          (con "zero" [ ])
          (con "succ" [ (recField "pred") ])
        ])._dtypeMeta
      );
      expected = {
        name = "Nat";
        indexed = false;
        indexTy = unitPrim;
        params = [ ];
        paramArgs = [ ];
        constructors = [
          { name = "zero"; fields = [ ]; }
          { name = "succ"; fields = [{ name = "pred"; kind = "recAt"; }]; }
        ];
      };
    };
    # Macro D matches the prelude `natDesc` exactly via nf.
    "datatype-nat-D-matches-natDesc" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        semEq N.D natDesc;
      expected = true;
    };
    "datatype-nat-D-carries-desc-ref" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          d = E.eval [ ] (elab N.D);
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = false;
        params = 0;
      };
    };
    "datatype-nat-D-desc-ref-conv-short-circuits" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          d = E.eval [ ] (elab N.D);
          sameRefDifferentBody = d // { d = V.vBootRefl; };
        in
        C.conv 0 d sameRefDifferentBody;
      expected = true;
    };
    "datatype-nat-D-desc-ref-mismatch-falls-back" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          d = E.eval [ ] (elab N.D);
          sameBodyDifferentRef = d // {
            _descRef = d._descRef // { arity = 3; };
          };
        in
        C.conv 0 d sameBodyDifferentRef;
      expected = true;
    };
    "datatype-nat-D-desc-ref-mismatch-does-not-prove-equality" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          d = E.eval [ ] (elab N.D);
          differentRefDifferentBody = d // {
            d = V.vBootRefl;
            _descRef = d._descRef // { arity = 3; };
          };
        in
        C.conv 0 d differentRefDifferentBody;
      expected = false;
    };
    "datatype-desc-ref-name-mismatch-does-not-prove-equality" = {
      expr =
        let
          BoxNat = datatype "BoxNatAudit" [
            (con "box" [ (field "x" nat) ])
          ];
          BoxBool = datatype "BoxBoolAudit" [
            (con "box" [ (field "x" bool) ])
          ];
        in
        {
          desc = C.conv 0 (E.eval [ ] (elab BoxNat.D)) (E.eval [ ] (elab BoxBool.D));
          type = C.conv 0 (E.eval [ ] (elab BoxNat.T)) (E.eval [ ] (elab BoxBool.T));
        };
      expected = {
        desc = false;
        type = false;
      };
    };
    "datatype-desc-ref-same-name-different-field-type-does-not-prove-equality" = {
      expr =
        let
          BoxNat = datatype "BoxAuditSame" [
            (con "box" [ (field "x" nat) ])
          ];
          BoxBool = datatype "BoxAuditSame" [
            (con "box" [ (field "x" bool) ])
          ];
        in
        {
          desc = C.conv 0 (E.eval [ ] (elab BoxNat.D)) (E.eval [ ] (elab BoxBool.D));
          type = C.conv 0 (E.eval [ ] (elab BoxNat.T)) (E.eval [ ] (elab BoxBool.T));
        };
      expected = {
        desc = false;
        type = false;
      };
    };
    # A constructor argument that is checkable-but-not-inferable — a bare
    # `cons`/`nil` list whose element type is inferred from the expected type —
    # must be CHECKED against its declared field type by the chain-flattener,
    # not inferred. Pre-fix the flattener lowered field args in infer mode, so
    # the list head landed in the element-type slot ("string-lit where U
    # expected"). The same value checks fine directly against `listOf string`.
    "flatten-saturated-ctor-checks-unannotated-list-field" = {
      expr =
        let
          One = datatype "OneListFieldRegression" [
            (con "mk" [ (field "xs" (listOf string)) ])
          ];
        in
        !((checkHoas One.T (app One.mk (cons (stringLit "a") nil))) ? error);
      expected = true;
    };
    # Sibling case in the recursive (chain) branch: the head of a list-of-lists
    # is itself a checkable-not-inferable list and must be checked against the
    # element type, not inferred.
    "flatten-recursive-ctor-checks-list-of-lists-head" = {
      expr =
        !((checkHoas (listOf (listOf string))
          (cons (cons (stringLit "a") nil) nil)) ? error);
      expected = true;
    };
    # Recursive cert path: a homogeneous (shared-reference) multi-layer chain
    # triggers `chainValidated`, whose pre-check must use the same checked
    # lowering as the emitted payload so the attestation matches the Tm.
    "flatten-recursive-ctor-cert-path-homogeneous-list-of-lists" = {
      expr =
        let inner = cons (stringLit "a") nil;
        in
        !((checkHoas (listOf (listOf string))
          (cons inner (cons inner nil))) ? error);
      expected = true;
    };
    # `elaborateCtorChecked` path: `pnode`'s two rec fields make `ctorShape`
    # null, so the flattener declines. Its param-instantiated `value : A` field
    # type reads as `ann (listOf string) (u 0)`; unless `fieldTyOf` strips that,
    # the bare `cons`/`nil` head lands in the element-type slot.
    "flatten-declining-ctor-checks-param-instantiated-data-field" = {
      expr =
        let
          PTree = datatypeP "PTreeAnnRegression" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "pleaf" [ ])
              (con "pnode" [ (field "value" A) (recField "left") (recField "right") ])
            ]);
          headList = cons (stringLit "a") nil;
          pnodeTm = app (app (app PTree.pnode headList) PTree.pleaf) PTree.pleaf;
        in
        !((checkHoas (app PTree.T (listOf string)) pnodeTm) ? error);
      expected = true;
    };
    "datatype-nat-T-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [ ])
        (con "succ" [ (recField "pred") ])
      ]).T).tag;
      expected = "mu";
    };
    "datatype-nat-T-check-U0" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (checkHoas (u 0) N.T).tag;
      expected = "mu";
    };
    # Zero commits the 0th (`boot-inl`) summand of the plus tree; the ret-leaf
    # witness is refl : Eq ⊤ tt tt.
    "datatype-nat-zero-payload" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (elab N.zero).d.tag;
      expected = "boot-inl";
    };
    "datatype-nat-zero-carries-desc-con-cert" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          z = elab N.zero;
        in
        {
          hasCert = z ? _descConCert;
          kind = z._descConCert.kind or null;
          fieldCount = z._descConCert.fieldCount or null;
        };
      expected = {
        hasCert = true;
        kind = "datatype-con-payload";
        fieldCount = 0;
      };
    };
    "datatype-nat-zero-checks" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (checkHoas N.T N.zero).tag;
      expected = "desc-con";
    };
    "datatype-nat-zero-check-preserves-desc-con-cert" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (checkHoas N.T N.zero) ? _descConCert;
      expected = true;
    };
    "datatype-nat-zero-cert-bad-payload-rejected" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          goodTm = elab N.zero;
          badTm = goodTm // { d = T.mkTt; };
          result = CH.runCheck (CH.check CH.emptyCtx badTm (E.eval [ ] (elab N.T)));
        in
        result ? error;
      expected = true;
    };
    "datatype-nat-zero-cert-not-used-with-untagged-expected-D" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          untaggedNatDesc = builtins.removeAttrs natDesc [ "_descRef" ];
        in
        (checkHoas (mu untaggedNatDesc tt) N.zero) ? _descConCert;
      expected = false;
    };
    "datatype-nat-zero-cert-mismatch-falls-back" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          badZero = N.zero // {
            _descConCert = N.zero._descConCert // {
              ref = N.zero._descConCert.ref // { arity = 3; };
            };
          };
          result = checkHoas N.T badZero;
        in
        {
          tag = result.tag or null;
          hasCert = result ? _descConCert;
        };
      expected = {
        tag = "desc-con";
        hasCert = false;
      };
    };
    # Constructor succ is fielded — the macro emits an ann-wrapped
    # curried lam, so its top-level _htag is "ann" until applied.
    "datatype-nat-succ-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [ ])
        (con "succ" [ (recField "pred") ])
      ]).succ).tag;
      expected = "ann";
    };
    "datatype-nat-succ-infers-pi" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (inferHoas N.succ).type.tag;
      expected = "VPi";
    };
    # Applied succ commits the 1st (`boot-inr`) summand, carrying the pred
    # recursive argument paired with the ret-leaf refl witness.
    "datatype-nat-succ-applied-payload" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          macroSucc = app N.succ N.zero;
        in
        (Q.nf [ ] (elab macroSucc)).d.tag;
      expected = "boot-inr";
    };
    # Saturated macro-ctor application flattens at elab time to a flat
    # `desc-con` Tm (shared-dTm chain of length 1). The kernel checks
    # it against the type and returns the reconstructed desc-con term.
    "datatype-nat-succ-applied-checks" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (checkHoas N.T (app N.succ N.zero)).tag;
      expected = "desc-con";
    };
    "datatype-nat-elim-infers-pi" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
        in
        (inferHoas (N.elim 0)).type.tag;
      expected = "VPi";
    };

    # nf-equivalence between the macro elim and the inline `ind` adapter
    # for representative (M, B, S, scrut) vectors. Both sides
    # eval-discard their type scaffolding (let_ vs ann), so any
    # divergence after nf is a genuine semantic regression in the
    # macro.
    #
    # Motive M = (λ_:nat. nat). Base B = zero. Step varies per test.
    #
    # Scrutinee 1: zero. The descInd's onTrue branch fires; macro
    # buildStepApply returns step_zero (B), the adapter's onTrue
    # returns base.
    "datatype-nat-elim-nf-gate-zero" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          M = lam "_" nat (_: nat);
          B = zero;
          S = lam "k" nat (k: lam "ih" nat (ih: ih));
          scrut = zero;
          macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
          adapterApplied = ind 0 M B S scrut;
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # Scrutinee 2: succ zero. Both onFalse branches fire; macro
    # projects (fst r, fst rih) and applies step_succ; the adapter
    # emits the same projection chain inline.
    "datatype-nat-elim-nf-gate-one" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          M = lam "_" nat (_: nat);
          B = zero;
          S = lam "k" nat (k: lam "ih" nat (ih: ih));
          scrut = succ zero;
          macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
          adapterApplied = ind 0 M B S scrut;
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # Scrutinee 3: succ (succ zero). Two layers of trampoline; checks
    # the nested descInd reduction agrees.
    "datatype-nat-elim-nf-gate-two" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          M = lam "_" nat (_: nat);
          B = zero;
          S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
          scrut = succ (succ zero);
          macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
          adapterApplied = ind 0 M B S scrut;
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # Scrutinee 4: a fresh-variable neutral scrutinee. This is the
    # critical case — neutral scrutinees do NOT reduce, so both terms
    # must produce the SAME stuck normal form (descInd D motive stepF
    # neutral) modulo α. Distinguishes "macro and adapter happen to
    # agree on closed scrutinees" from "macro and adapter agree as
    # terms".
    "datatype-nat-elim-nf-gate-neutral" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          M = lam "_" nat (_: nat);
          B = zero;
          S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
          # Fresh-variable neutral: the elim is wrapped in an outer lam
          # that binds `n : nat`, then applied to that bound variable. nf
          # cannot reduce it since `n` is neutral.
          macroAtN = lam "n" nat (n:
            app (app (app (app (N.elim 0) M) B) S) n);
          adapterAtN = lam "n" nat (n: ind 0 M B S n);
        in
        semEq macroAtN adapterAtN;
      expected = true;
    };

    # End-to-end semantic test: addition on macro-Nat reduces
    # correctly. add(2, 3) = 5 via the macro elim and macro
    # constructors, exercising the IH projection through actual
    # recursion rather than just nf comparison against the inline
    # adapter.
    "datatype-nat-elim-add-2-3" = {
      expr =
        let
          N = datatype "Nat" [
            (con "zero" [ ])
            (con "succ" [ (recField "pred") ])
          ];
          # add m n = elim (λ_. nat) n (λk.λih. succ ih) m
          # Recursing on m: zero case → n; succ k case → succ (add k n).
          add = m: n:
            app
              (app
                (app
                  (app (N.elim 0)
                    (lam "_" N.T (_: N.T)))
                  n)
                (lam "k" N.T (k: lam "ih" N.T (ih: app N.succ ih))))
              m;
          two = app N.succ (app N.succ N.zero);
          three = app N.succ (app N.succ (app N.succ N.zero));
          five = app N.succ (app N.succ (app N.succ (app N.succ (app N.succ N.zero))));
        in
        semEq (add two three) five;
      expected = true;
    };

    # Universe-K-1 motive: `N.elim 1` applied to a motive that returns
    # `U(0)` inhabits a step type whose All-hypothesis lands in `U(1)`.
    # Exercises the K-threading pipeline at a concrete K: the All witness
    # type inhabits `U(1)`, and the
    # motive level recovered from `checkMotive` lines up.
    "datatype-nat-elim-universe-one" = {
      expr =
        let
          N = datatype "Nat" [ (con "zero" [ ]) (con "succ" [ (recField "pred") ]) ];
          M = lam "_" N.T (_: u 0);
          B = unit;
          S = lam "_k" N.T (_: lam "ih" (u 0) (ih: ih));
          applied = app (app (app (app (N.elim 1) M) B) S) N.zero;
        in
        (checkHoas (u 0) applied).tag;
      expected = "app";
    };

    # Same shape through the HOAS `ind` combinator, which threads K into
    # `N.elim`. `ind` wraps the elim application
    # in a `let_` chain that lifts P/B/S to inferable positions, so the
    # elaborated tag is `let` rather than the bare `app` spine.
    "ind-universe-one" = {
      expr = (checkHoas (u 0) (ind 1 (lam "_" nat (_: u 0)) unit
        (lam "_" nat (_: lam "_" (u 0) (ih: ih)))
        zero)).tag;
      expected = "let";
    };

    # HOAS `ind` accepts a HOAS Level term in its `k` slot (not just a
    # Nix-meta Int). `levelMax levelZero levelZero` is conv-equal to
    # `levelZero` under the kernel's Level normaliser, so the motive
    # `λ_:nat. nat` (returning U(0)) type-checks at this K — but the
    # elaborated Tm carries a `level-max` node end-to-end, exercising
    # the polymorphic-K route from HOAS through `elaborateLevel` and
    # down to `mkAllMotive`'s closure-env-threaded `K_val`.
    "ind-hoas-level-term-accepted" = {
      expr = (checkHoas nat
        (ind (levelMax levelZero levelZero)
          (lam "_" nat (_: nat))
          zero
          (lam "_" nat (_: lam "_" nat (ih: succ ih)))
          zero)).tag;
      expected = "let";
    };

    # The level expression `levelMax levelZero levelZero` survives
    # elaborate verbatim — `elaborateLevel` recurses on the HOAS
    # construct rather than coercing it to a constant. The motive's
    # universe annotation in the elaborated `let_ "P" piMotiveTy …`
    # therefore carries a `level-max` Tm.
    "ind-hoas-level-term-elab-shape" = {
      expr =
        let
          tm = elab (ind (levelMax levelZero levelZero)
            (lam "_" nat (_: nat))
            zero
            (lam "_" nat (_: lam "_" nat (ih: succ ih)))
            zero);
        in
        tm.type.codomain.level.tag;
      expected = "level-max";
    };

    # Universe-polymorphic eliminator: a function quantifying over a
    # bound `k : Level`, with motive `P : nat → U(k)` returning at the
    # bound level. `ind k …` in the body forces `descInd`'s infer rule
    # to thread a `vNe` Level Val through `mkAllMotive`'s closure env
    # — concrete-level coercion at the call site cannot apply, so the
    # K-as-Val discipline is exercised end-to-end.
    "ind-polymorphic-motive-k-bound" = {
      expr =
        let
          ty = forall "k" level (k:
            forall "P" (forall "_" nat (_: u k)) (P:
              forall "B" (app P zero) (_:
                forall "S"
                  (forall "n" nat (n:
                    forall "_" (app P n) (_: app P (succ n))))
                  (_:
                    forall "n" nat (n: app P n)))));
          body = lam "k" level (k:
            lam "P" (forall "_" nat (_: u k)) (P:
              lam "B" (app P zero) (B:
                lam "S"
                  (forall "n" nat (n:
                    forall "_" (app P n) (_: app P (succ n))))
                  (S:
                    lam "n" nat (n: ind k P B S n)))));
        in
        (checkHoas ty body).tag;
      expected = "lam";
    };

    # `reifyLevel` is the inverse of `elaborateLevel`: kernel Level
    # value → HOAS Level node. Concrete chains, `vLevelMax`, and `vNe`
    # (a bound Level variable in the surrounding context) all reify
    # without throwing — closing the round-trip kernel ↔ HOAS for
    # universe levels.
    "reifyLevel-zero" = {
      expr = (fx.tc.hoas.reifyLevel V.vLevelZero)._htag;
      expected = "level-zero";
    };
    "reifyLevel-suc" = {
      expr = (fx.tc.hoas.reifyLevel (V.vLevelSuc V.vLevelZero))._htag;
      expected = "level-suc";
    };
    "reifyLevel-max" = {
      expr = (fx.tc.hoas.reifyLevel (V.vLevelMax V.vLevelZero V.vLevelZero))._htag;
      expected = "level-max";
    };
    # A neutral Level (a bound Level Var at de Bruijn level 0) reifies
    # to a marker. Wrapping the marker under a fresh `forall` that
    # introduces a Level binder at depth 0 elaborates the marker back
    # to `mkVar 0` — proving the round-trip Var → marker → Var.
    "reifyLevel-vNe-round-trips-to-Var" = {
      expr =
        let
          marker = fx.tc.hoas.reifyLevel (V.vNe 0 [ ]);
          wrapped = forall "k" level (_: u marker);
        in
        (elab wrapped).codomain.level.tag;
      expected = "var";
    };
    # Whole-pipeline closure: `reifyType` on a `VU` whose level is
    # `vLevelMax` produces a HOAS `u` node whose level slot carries the
    # reified Level term verbatim.
    "reifyType-VU-non-concrete-level" = {
      expr =
        let
          Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
          uVal = V.vU Kval;
        in
        (fx.tc.elaborate.reifyType uVal)._htag;
      expected = "U";
    };
    "reifyType-VU-non-concrete-level-preserves-max" = {
      expr =
        let
          Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
          uVal = V.vU Kval;
        in
        (fx.tc.elaborate.reifyType uVal).level._htag;
      expected = "level-max";
    };

    # natToLevel surface helper — accepts a Nix Int and emits closed Level
    # syntax. It is not a kernel Nat eliminator.
    "elab-natToLevel-zero-tag" = {
      expr = (elab (natToLevel 0)).tag;
      expected = "level-zero";
    };
    "elab-natToLevel-3-payload" = {
      expr = (elab (natToLevel 3)).pred.pred.pred.tag;
      expected = "level-zero";
    };
    "natToLevel-3-checks-at-Level" = {
      # End-to-end: surface `natToLevel 3` checks against `level`.
      expr = (checkHoas level (natToLevel 3)).tag;
      expected = "level-suc";
    };
    "natToLevel-3-reduces-to-suc3-zero" = {
      expr =
        let
          lhs = E.eval [ ] (elab (natToLevel 3));
          rhs = V.vLevelSuc (V.vLevelSuc (V.vLevelSuc V.vLevelZero));
        in
        fx.tc.conv.conv 0 lhs rhs;
      expected = true;
    };
    "u-natToLevel-1-elaborates-as-U-of-suc-zero" = {
      expr =
        let
          ty = E.eval [ ] (elab (u (natToLevel 1)));
        in
        fx.tc.conv.conv 0 ty (V.vU (V.vLevelSuc V.vLevelZero));
      expected = true;
    };


    # ===== ListDT tests (datatypeP; parameter A; linear-recursive) =====

    # ListDT: 1-param polymorphic, 2 constructors. `cons` carries one
    # data field (head : A) and one recursive field (tail : List A) —
    # this is the profile linearProfile accepts as Just [A].
    "datatype-list-spec-name" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        L.name;
      expected = "List";
    };
    "datatype-list-spec-params" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        builtins.length L.params;
      expected = 1;
    };
    # Macro D applied to nat is nf-equivalent to the prelude `listDesc nat`
    # alias. The polymorphic λA. mono.D fully applies to give the
    # per-instance description; nf normalizes through the
    # `app (ann (λA. ...) ty) nat` β-redex and the ann wrapper.
    "datatype-list-D-matches-listDesc" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        semEq (app L.D nat) (listDesc nat);
      expected = true;
    };
    "datatype-list-D-carries-desc-ref" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          d = E.eval [ ] (elab (app L.D nat));
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = false;
        params = 1;
      };
    };
    # Polymorphic T at A=nat elaborates to a μ value.
    "datatype-list-T-nat-elab" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        (elab (app L.T nat)).tag;
      # app of a lambda-annotated type — elaborated as an app tree.
      # The outer elab tag is "app" (not yet β-reduced); eval reduces
      # to VMu.
      expected = "app";
    };
    # `ListDT.nil nat` type-checks against `ListDT.T nat`.
    "datatype-list-nil-checks" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          result = checkHoas (app L.T nat) (app L.nil nat);
        in
          !(result ? error);
      expected = true;
    };
    # `ListDT.cons nat zero (ListDT.nil nat)` type-checks.
    "datatype-list-cons-one-checks" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          hoasVal = app (app (app L.cons nat) zero) (app L.nil nat);
          result = checkHoas (app L.T nat) hoasVal;
        in
          !(result ? error);
      expected = true;
    };
    # Polymorphic cons at A=nat infers to a Π over head, tail (curried).
    "datatype-list-cons-at-nat-infers-pi" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        (inferHoas (app L.cons nat)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro ListDT.elim against the inline
    # `listElim` adapter on the empty list. Motive (λ_. nat), onNil =
    # zero, onCons returns `succ head` to differentiate base from step.
    "datatype-list-elim-nf-gate-empty" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          M = lam "_" (app L.T nat) (_: nat);
          onNil = zero;
          onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
          scrut = app L.nil nat;
          macroApplied = app (app (app (app (app (L.elim 0) nat) M) onNil) onCons) scrut;
          adapterApplied = listElim 0 nat M onNil
            (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
            (HI.nilAtExplicit nat);
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # nf-gate on a one-element list: cons zero nil. Both sides reduce
    # to `succ zero` after normalization.
    "datatype-list-elim-nf-gate-one" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          M = lam "_" (app L.T nat) (_: nat);
          onNil = zero;
          onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
          scrut = app (app (app L.cons nat) zero) (app L.nil nat);
          macroApplied = app (app (app (app (app (L.elim 0) nat) M) onNil) onCons) scrut;
          adapterApplied = listElim 0 nat M zero
            (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
            (HI.consAtExplicit nat zero (HI.nilAtExplicit nat));
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # nf-gate on a fresh-variable neutral list scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
    "datatype-list-elim-nf-gate-neutral" = {
      expr =
        let
          L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          M = lam "_" (app L.T nat) (_: nat);
          macroAtL = lam "l" (app L.T nat) (l:
            app
              (app (app (app (app (L.elim 0) nat) M) zero)
                (lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)))))
              l);
          adapterAtL = lam "l" (listOf nat) (l:
            listElim 0 nat (lam "_" (listOf nat) (_: nat)) zero
              (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
              l);
        in
        semEq macroAtL adapterAtL;
      expected = true;
    };

    # Tree: non-linear recursive (node has two rec fields). The peel's
    # linearProfile on the false-branch description `descRec (descRec
    # descRet)` returns null; the check falls through to non-trampolined
    # descCon handling without crashing. A payload-shape classifier
    # would mis-read `pair false (pair LEFTREC (pair RIGHTREC tt))` as
    # a list-shape head+rec and crash on the null elemVal —
    # description-shape dispatch avoids that class of miscount.
    "peel-declines-tree-shape" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
          leafZero = app Tree.leaf zero;
          nodeLL = app (app Tree.node leafZero) leafZero;
          result = checkHoas (app Tree.T nat) nodeLL;
        in
          !(result ? error);
      expected = true;
    };

    # ===== SumDT tests (datatypeP; two parameters; non-recursive) =====

    # SumDT: 2-param polymorphic, 2 constructors. Each constructor
    # carries a single data field and no recursive field — exercises
    # the nParams=2 branch of datatypeP's parameter loop. chainShapeOk
    # requires a final rec field, so the chain-flattener declines on
    # `inl`/`inr` and the regular ann-lam cascade handles every
    # application.
    "datatype-sum-spec-name" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
        in
        S.name;
      expected = "Sum";
    };
    "datatype-sum-spec-params" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
        in
        builtins.length S.params;
      expected = 2;
    };
    # Macro D applied to (nat, bool) is nf-equivalent to the prelude
    # `sumDesc nat bool` alias. The polymorphic λA.λB. mono.D fully
    # applies to give the per-instance description; nf normalizes
    # through the two `app (ann (λ. ...) ty) _` β-redexes and the ann
    # wrappers.
    "datatype-sum-D-matches-sumDesc" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
        in
        semEq (app (app S.D nat) bool) (sumDesc nat bool);
      expected = true;
    };
    "datatype-sumDT-level-param-count" = {
      expr = builtins.length self.SumDT.params;
      expected = 3;
    };
    "datatype-sumAt-zero-inl-checks" = {
      expr = !(checkHoas (self.sumAt levelZero nat bool)
        (self.inlAt zero) ? error);
      expected = true;
    };
    "datatype-sumAt-one-inl-checks" = {
      expr = !(checkHoas (self.sumAt (levelSuc levelZero) (u 0) (u 0))
        (self.inlAt unit) ? error);
      expected = true;
    };
    "datatype-sumAt-one-elim-to-zero-level-computes" = {
      expr =
        let
          L = levelSuc levelZero;
          A = u 0;
          B = u 0;
          scrut = self.inlAtExplicit L A B unit;
          result = self.sumElimAt L 0 A B
            (lam "_" (self.sumAt L A B) (_: nat))
            (lam "x" A (_: zero))
            (lam "y" B (_: succ zero))
            scrut;
          checked = checkHoas (eq nat result zero) refl;
        in
        !(checked ? error) && checked.tag == "desc-con";
      expected = true;
    };
    "datatype-sum-D-carries-desc-ref" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          d = E.eval [ ] (elab (app (app S.D nat) bool));
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = false;
        params = 2;
      };
    };
    # Polymorphic T fully applied to (nat, bool) elaborates as an app
    # tree (the outer ann (λA.λB. ...) ty awaiting two β-reductions);
    # eval reduces it to VMu.
    "datatype-sum-T-applied-elab" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
        in
        (elab (app (app S.T nat) bool)).tag;
      expected = "app";
    };
    # `SumDT.inl nat bool zero` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inl-checks" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          hoasVal = app (app (app S.inl nat) bool) zero;
          result = checkHoas (app (app S.T nat) bool) hoasVal;
        in
          !(result ? error);
      expected = true;
    };
    "datatype-sum-inl-check-preserves-desc-con-cert" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          hoasVal = app (app (app S.inl nat) bool) zero;
        in
        (checkHoas (app (app S.T nat) bool) hoasVal) ? _descConCert;
      expected = true;
    };
    "datatype-sum-inl-cert-bad-field-rejected" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          goodTm = elab (app (app (app S.inl nat) bool) zero);
          badTm = goodTm // {
            d = goodTm.d // {
              term = T.mkPair (elab true_) T.mkBootRefl;
            };
          };
          tyVal = E.eval [ ] (elab (app (app S.T nat) bool));
          result = CH.runCheck (CH.check CH.emptyCtx badTm tyVal);
        in
        result ? error;
      expected = true;
    };
    "datatype-sum-inl-cert-wrong-ctor-falls-back" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          goodTm = elab (app (app (app S.inl nat) bool) zero);
          badTm = goodTm // {
            _descConCert = goodTm._descConCert // { ctor = 1; };
          };
          tyVal = E.eval [ ] (elab (app (app S.T nat) bool));
          result = CH.runCheck (CH.check CH.emptyCtx badTm tyVal);
        in
        {
          tag = result.tag or null;
          hasCert = result ? _descConCert;
        };
      expected = {
        tag = "desc-con";
        hasCert = false;
      };
    };
    # `SumDT.inr nat bool true_` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inr-checks" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          hoasVal = app (app (app S.inr nat) bool) true_;
          result = checkHoas (app (app S.T nat) bool) hoasVal;
        in
          !(result ? error);
      expected = true;
    };
    # Polymorphic inl partially applied to its two type parameters
    # infers to a Π over `value` — the curried single-data-field
    # signature.
    "datatype-sum-inl-at-types-infers-pi" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
        in
        (inferHoas (app (app S.inl nat) bool)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro SumDT.elim against the inline
    # `sumElim` adapter on an `inl` scrutinee. Motive picks `nat`
    # (constant), onLeft is identity on Nat, onRight is the Bool→Nat
    # true↦zero false↦zero constant — both sides reduce to `zero` on
    # `inl nat bool zero`.
    "datatype-sum-elim-nf-gate-inl" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          M = lam "_" (app (app S.T nat) bool) (_: nat);
          onLeft = lam "a" nat (a: a);
          onRight = lam "b" bool (_: zero);
          scrut = app (app (app S.inl nat) bool) zero;
          macroApplied =
            app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) scrut;
          adapterApplied =
            sumElim 0 nat bool M onLeft onRight (HI.inlAtExplicit 0 nat bool zero);
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # nf-equivalence on an `inr` scrutinee. Same motive/cases; this
    # exercises the false-branch of the descInd boolElim dispatch.
    "datatype-sum-elim-nf-gate-inr" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          M = lam "_" (app (app S.T nat) bool) (_: nat);
          onLeft = lam "a" nat (a: a);
          onRight = lam "b" bool (_: zero);
          scrut = app (app (app S.inr nat) bool) true_;
          macroApplied =
            app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) scrut;
          adapterApplied =
            sumElim 0 nat bool M onLeft onRight (HI.inrAtExplicit 0 nat bool true_);
        in
        semEq macroApplied adapterApplied;
      expected = true;
    };
    # nf-gate on a fresh-variable neutral Sum scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
    "datatype-sum-elim-nf-gate-neutral" = {
      expr =
        let
          S = datatypeP "Sum"
            [{ name = "A"; kind = u 0; } { name = "B"; kind = u 0; }]
            (ps:
              let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                (con "inl" [ (field "value" A) ])
                (con "inr" [ (field "value" B) ])
              ]);
          M = lam "_" (app (app S.T nat) bool) (_: nat);
          onLeft = lam "a" nat (a: a);
          onRight = lam "b" bool (_: zero);
          macroAtS = lam "s" (app (app S.T nat) bool) (s:
            app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) s);
          adapterAtS = lam "s" (sum nat bool) (s:
            sumElim 0 nat bool (lam "_" (sum nat bool) (_: nat))
              onLeft
              onRight
              s);
        in
        semEq macroAtS adapterAtS;
      expected = true;
    };

    # ===== TreeDT tests (datatypeP; one parameter; non-linear recursion) =====

    # TreeDT is a non-prelude user-defined datatype with two
    # constructors: `leaf` carries one data field, `node` carries two
    # recursive fields. `node`'s shape `descRec (descRec descRet)`
    # falls outside linearProfile's acceptance (no terminal data
    # spine), so the chain-flattener declines and the regular ann-lam
    # cascade handles every application. The eliminator's dispatchStep
    # projects two recursive IHs at positions 0 and 1 of payloadIH
    # (one per rec field, in declaration order).
    "datatype-tree-spec-name" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
        in
        Tree.name;
      expected = "Tree";
    };
    "datatype-tree-spec-params" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
        in
        builtins.length Tree.params;
      expected = 1;
    };
    "datatype-tree-spec-cons" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
        in
        builtins.length Tree._dtypeMeta.constructors;
      expected = 2;
    };
    # Polymorphic T at A=nat elaborates as an app tree (ann-wrapped λA.
    # ... awaiting β); eval reduces to VMu.
    "datatype-tree-T-at-nat-elab" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
        in
        (elab (app Tree.T nat)).tag;
      expected = "app";
    };
    # `Tree.leaf nat zero` type-checks against `Tree.T nat`.
    "datatype-tree-leaf-checks" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
          leafZero = app (app Tree.leaf nat) zero;
          result = checkHoas (app Tree.T nat) leafZero;
        in
          !(result ? error);
      expected = true;
    };
    # `Tree.node nat (leaf 0) (leaf 0)` type-checks against `Tree.T nat`.
    # Exercises the two-rec-fields fallback path: the chain-flatten
    # precondition rejects (chainShapeOk requires the last field to be
    # `rec` and all earlier fields to be `data`), so the application
    # elaborates through the regular ann-lam cascade. The kernel's
    # desc-con peel then sees a `descRec (descRec descRet)` description,
    # linearProfile returns null, and the peel declines without
    # mis-reading the payload.
    "datatype-tree-node-of-leaves-checks" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
          leafZero = app Tree.leaf zero;
          nodeLL = app (app Tree.node leafZero) leafZero;
          result = checkHoas (app Tree.T nat) nodeLL;
        in
          !(result ? error);
      expected = true;
    };
    # Polymorphic leaf at A=nat checks against the Π `(value : nat) → Tree nat`.
    # Reformulated: under smalltt-style insertion, `app Tree.leaf nat` fills
    # the explicit `value` position (solving `?A := U 0`) and yields `VMu`,
    # not `VPi`. Test the principled property — checkability against the
    # specialised Π — via `H.checkHoas`.
    "datatype-tree-leaf-at-nat-infers-pi" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
          treeLeafAtNatTy = forall "value" nat (_: app Tree.T nat);
        in
        !((checkHoas treeLeafAtNatTy Tree.leaf) ? error);
      expected = true;
    };
    # Polymorphic elim at A=nat infers to a Π (over the motive P).
    "datatype-tree-elim-at-nat-infers-pi" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
        in
        (inferHoas (app (Tree.elim 0) nat)).type.tag;
      expected = "VPi";
    };
    # End-to-end semantic test: count leaves of a 2-leaf tree.
    # leafCount = elim with motive (λ_. nat),
    #   step_leaf  = λ_. succ zero
    #   step_node  = λl r il ir. add il ir
    # `node (leaf 0) (leaf 0)` reduces via descInd to `add 1 1 = 2`.
    # The equality `leafCount tree ≡ succ (succ zero)` holds by
    # reduction; refl type-checks against it.
    "datatype-tree-elim-leaf-count-2" = {
      expr =
        let
          Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "leaf" [ (field "value" A) ])
              (con "node" [ (recField "left") (recField "right") ])
            ]);
          Tnat = app Tree.T nat;
          leafZero = app (app Tree.leaf nat) zero;
          nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
          # See `integration-desc-nat-add-2-3`: `app addTm il` requires
          # `addTm` inferable, hence the explicit Π annotation.
          addTm = ann
            (lam "m" nat (m: lam "n" nat (n:
              ind 0 (lam "_" nat (_: nat))
                n
                (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                m)))
            (forall "m" nat (_: forall "n" nat (_: nat)));
          M = lam "_" Tnat (_: nat);
          sLeaf = lam "v" nat (_: succ zero);
          sNode = lam "l" Tnat (_:
            lam "r" Tnat (_:
              lam "il" nat (il:
                lam "ir" nat (ir: app (app addTm il) ir))));
          countTm = app (app (app (app (app (Tree.elim 0) nat) M) sLeaf) sNode) nodeLL;
          two = succ (succ zero);
          eqTy = eq nat countTm two;
        in
        (checkHoas eqTy refl).tag;
      expected = "desc-con";
    };

    "ornament-spike-inserted-field-forget-typechecks" = {
      expr =
        let
          baseD = ann (descArg unitPrim 0 nat (_: descRet)) desc;
          ornD = ann (descArg unitPrim 0 bool (_: baseD)) desc;
          baseT = mu baseD ttPrim;
          ornT = mu ornD ttPrim;
          muFam = lam "i" unitPrim (i: mu ornD i);
          motive = lam "i" unitPrim (i:
            lam "_" (mu ornD i) (_: baseT));
          step = lam "i" unitPrim (i:
            lam "d" (interpD 0 unitPrim ornD muFam i) (d:
              lam "_ih" (allD 0 unitPrim ornD 0 muFam motive i d) (_:
                descCon baseD ttPrim (snd_ d))));
          forget = ann
            (lam "x" ornT (x: descInd ornD motive step ttPrim x))
            (forall "x" ornT (_: baseT));
          ornValue = descCon ornD ttPrim
            (pair true_ (pair zero bootRefl));
        in
        (checkHoas baseT (app forget ornValue)).tag;
      expected = "app";
    };

    "fastpath-sum-anonymous-mu-param-checks" = {
      expr =
        let
          baseD = descRet;
          baseT = mu baseD tt;
          baseValue = descCon baseD tt bootRefl;
        in
        (checkHoas (sum baseT unit) (inl baseValue)).tag;
      expected = "desc-con";
    };

    "anonymous-mu-raw-checked-conv-erases-injection-annotations" = {
      expr =
        let
          baseD = descRet;
          baseT = mu baseD tt;
          baseValue = descCon baseD tt bootRefl;
          rawT = E.eval [ ] (elab baseT);
          checkedT = E.eval [ ] (CH.runCheck (CH.checkType CH.emptyCtx (elab baseT)));
          rawValue = E.eval [ ] (elab baseValue);
          checkedValue = E.eval [ ] (CH.runCheck (CH.check CH.emptyCtx (elab baseValue) checkedT));
        in
        {
          type = C.conv 0 rawT checkedT;
          value = C.conv 0 rawValue checkedValue;
        };
      expected = {
        type = true;
        value = true;
      };
    };

    "fastpath-list-anonymous-mu-param-checks" = {
      expr =
        let
          baseD = descRet;
          baseT = mu baseD tt;
          baseValue = descCon baseD tt bootRefl;
        in
        (checkHoas (listOf baseT)
          (cons baseValue nil)).tag;
      expected = "desc-con";
    };

    "fastpath-monomorphic-field-anonymous-mu-checks" = {
      expr =
        let
          baseD = descRet;
          baseT = mu baseD tt;
          baseValue = descCon baseD tt bootRefl;
          Box = datatype "BoxAudit" [
            (con "box" [ (field "x" baseT) ])
          ];
        in
        (checkHoas Box.T (app Box.box baseValue)).tag;
      expected = "desc-con";
    };

    # ===== W-type tests (datatypeP; dependent parameter kinds) =====

    # W is parameterised by S (shapes : U) and P (positions : S → U).
    # The second parameter's KIND depends on the first — `P : S → U`
    # cannot be expressed with a fixed Hoas kind, so `datatypeP`
    # accepts `kind` as either a Hoas (fixed) OR a function
    # `markers → Hoas` (dependent on already-bound parameter
    # markers). This mirrors the existing `field`/`fieldD` and
    # `piField`/`piFieldD` dependency pattern at the parameter level.
    #
    # The single ctor `sup` carries one data field (s : S) and one
    # dependent pi field (f : (P s) → W S P), exercising piFieldD's
    # `prev`-threaded type construction. chainShapeOk requires
    # last.kind == "recAt"; sup's last field is "piD", so the
    # chain-flattener declines and the regular ann-lam cascade handles
    # every application.
    "datatype-w-spec-name" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
        in
        W.name;
      expected = "W";
    };
    "datatype-w-spec-params" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
        in
        builtins.length W.params;
      expected = 2;
    };
    # W's macro D fully applied to (bool, λs.boolElim _ unit void s) is
    # definitionally equal to the hand-written `descArg bool (s: descPi
    # (boolP s) descRet)` from the integration-desc-wtype-wellformed
    # test. Pins the D-emission shape against the canonical W-type
    # description.
    "datatype-w-D-matches-wDesc" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          macroD = app (app W.D bool) boolP;
          manualD = descArg unit 0 bool (s:
            descPi 0 (app boolP s) descRet);
        in
        semEq macroD manualD;
      expected = true;
    };
    "datatype-w-D-carries-desc-ref" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          d = E.eval [ ] (elab (app (app W.D bool) boolP));
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 1;
        indexed = false;
        params = 2;
      };
    };
    # `W.T bool boolP` reduces to `μ wBoolDesc` and inhabits `U(0)`,
    # matching the `integration-desc-wtype-wellformed` shape test.
    "datatype-w-T-wellformed" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          Tw = app (app W.T bool) boolP;
          result = checkHoas (u 0) Tw;
        in
          !(result ? error);
      expected = true;
    };
    # Polymorphic `sup` partially applied to its two type parameters
    # infers to a Π over `s : bool` (the head of the curried field
    # signature). Validates that datatypeP's poly-ctor wrapper composes
    # the two `ann (λS λP. ...)` outer layers without losing
    # inferability.
    "datatype-w-sup-at-types-infers-pi" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        in
        (inferHoas (app (app W.sup bool) boolP)).type.tag;
      expected = "VPi";
    };
    # End-to-end ctor application: `sup false_ (λx:void. absurd Tw x)`
    # is a vacuous-position W value (P false_ = void, so f's domain is
    # empty and absurd discharges the body). Type-checks against `Tw =
    # W bool boolP`. Exercises piFieldD's dependent type-construction
    # and the absurd-on-void elimination through the macro's ctor type.
    "datatype-w-sup-vacuous-checks" = {
      expr =
        let
          W = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          Tw = app (app W.T bool) boolP;
          vacuous = lam "x" void (x: absurd Tw x);
          sup0 = app (app (app (app W.sup bool) boolP) false_) vacuous;
          result = checkHoas Tw sup0;
        in
          !(result ? error);
      expected = true;
    };

    "datatype-fieldAt-level-zero-matches-field" = {
      expr =
        let
          BoxAt = datatype "Box" [ (con "box" [ (fieldAt 0 "value" nat) ]) ];
          Box0 = datatype "Box" [ (con "box" [ (field "value" nat) ]) ];
        in
        semEq BoxAt.D Box0.D;
      expected = true;
    };
    "datatype-piFieldDAt-level-zero-matches-piFieldD" = {
      expr =
        let
          WAt = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldDAt 0 "f" (prev: app P prev.s)) ])
              ]);
          W0 = datatypeP "W"
            [{ name = "S"; kind = u 0; }
              { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); }]
            (ps:
              let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
                (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
              ]);
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        in
        semEq (app (app WAt.D bool) boolP) (app (app W0.D bool) boolP);
      expected = true;
    };
    "datatypePAt-level-zero-matches-datatypeP" = {
      expr =
        let
          ListAt = datatypePAt "List" [{ name = "A"; kind = u 0; }] (_: 0) (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
          List0 = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (con "nil" [ ])
              (con "cons" [ (field "head" A) (recField "tail") ])
            ]);
        in
        semEq (app ListAt.D nat) (app List0.D nat);
      expected = true;
    };

    "datatype-w-level-param-spec-name" = {
      expr = self.WDT.name;
      expected = "W";
    };
    "datatype-w-level-param-D-carries-desc-ref" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          d = E.eval [ ] (elab (wDesc levelZero bool boolP));
        in
        {
          kind = d._descRef.kind;
          arity = d._descRef.arity;
          indexed = d._descRef.indexed;
          params = builtins.length d._descRef.params;
        };
      expected = {
        kind = "datatype-desc";
        arity = 1;
        indexed = false;
        params = 3;
      };
    };
    "datatype-w-level-param-D-level-is-k" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          d = E.eval [ ] (elab (wDesc levelZero bool boolP));
        in
        C.convLevel d._descRef.level V.vLevelZero;
      expected = true;
    };
    "datatype-w-level-param-D-matches-manual-wDescAt" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          manualWDescAt = k: S: P:
            descArgAt unitPrim k k S (s:
              descPiAt k k (app P s) (retI unitPrim k ttPrim));
        in
        semEq (wDesc levelZero bool boolP)
          (manualWDescAt levelZero bool boolP);
      expected = true;
    };
    "datatype-w-level-param-sup-at-zero-infers-pi" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        in
        (inferHoas (app (app (app self.WDT.sup levelZero) bool) boolP)).type.tag;
      expected = "VPi";
    };
    "datatype-w-level-param-sup-vacuous-checks" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          Tw = w levelZero bool boolP;
          vacuous = lam "x" void (x: absurd Tw x);
          sup0 = sup levelZero bool boolP false_ vacuous;
          result = checkHoas Tw sup0;
        in
          !(result ? error);
      expected = true;
    };
    "datatype-w-level-param-elim-reduces-vacuous" = {
      expr =
        let
          boolP = lam "s" bool (s:
            boolElim 1 (lam "_" bool (_: u 0)) unit void s);
          Tw = w levelZero bool boolP;
          vacuous = lam "x" void (x: absurd Tw x);
          sup0 = sup levelZero bool boolP false_ vacuous;
          Qw = lam "_" Tw (_: unit);
          step = lam "s" bool (s:
            lam "f" (forall "_" (app boolP s) (_: Tw)) (_:
              lam "ih_f" (forall "_" (app boolP s) (_: unit)) (_:
                tt)));
          reduced = wElim levelZero 0 bool boolP Qw step sup0;
        in
        semEq reduced tt;
      expected = true;
    };
    "datatype-w-level-param-D-typechecks-under-level-binder" = {
      expr =
        let
          ty = forall "k" level (k:
            forall "S" (u k) (S:
              forall "P" (forall "_" S (_: u k)) (_:
                descAt k)));
          tm = lam "k" level (k:
            lam "S" (u k) (S:
              lam "P" (forall "_" S (_: u k)) (P:
                wDesc k S P)));
        in
        (checkHoas ty tm).tag;
      expected = "lam";
    };
    "datatype-w-level-param-T-typechecks-under-level-binder" = {
      expr =
        let
          ty = forall "k" level (k:
            forall "S" (u k) (S:
              forall "P" (forall "_" S (_: u k)) (_:
                u k)));
          tm = lam "k" level (k:
            lam "S" (u k) (S:
              lam "P" (forall "_" S (_: u k)) (P:
                w k S P)));
        in
        (checkHoas ty tm).tag;
      expected = "lam";
    };
    "datatype-w-level-param-sup-typechecks-under-level-binder" = {
      expr =
        let
          ty = forall "k" level (k:
            forall "S" (u k) (S:
              forall "P" (forall "_" S (_: u k)) (P:
                forall "s" S (s:
                  forall "f" (forall "_" (app P s) (_: w k S P)) (_:
                    w k S P)))));
          tm = lam "k" level (k:
            lam "S" (u k) (S:
              lam "P" (forall "_" S (_: u k)) (P:
                app (app (app self.WDT.sup k) S) P)));
        in
        (checkHoas ty tm).tag;
      expected = "lam";
    };

    # ===== datatypeI / datatypePI regressions =====
    # The macro's output should be definitionally equal to the public
    # prelude aliases for Fin (monomorphic indexed), Vec (parametric
    # indexed), and Eq (parametric indexed with parameter-dependent index
    # type). Function fields are closed by wrapping in `lam` over fresh
    # markers so both sides sit under the same de Bruijn environment.

    "datatypeI-fin-D-matches-finDesc" = {
      expr =
        let
          FinDT = self.datatypeI "Fin" self.nat [
            (self.conI "fzero" [ (self.field "m" self.nat) ]
              (p: self.succ p.m))
            (self.conI "fsuc" [
              (self.field "m" self.nat)
              (self.recFieldAt "k" (p: p.m))
            ]
              (p: self.succ p.m))
          ];
        in
        semEq FinDT.D self.finDesc;
      expected = true;
    };
    "datatypeI-fin-D-carries-desc-ref" = {
      expr = let d = E.eval [ ] (elab self.FinDT.D); in {
        kind = d._descRef.kind;
        arity = d._descRef.arity;
        indexed = d._descRef.indexed;
        params = builtins.length d._descRef.params;
      };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = true;
        params = 0;
      };
    };

    # `FinDT.T` is an `ann`-lam family-as-function. Applying both sides
    # to a fresh marker β-reduces binder names out of the comparison —
    # the semantics is checked by application, matching the pattern used
    # by `datatypePI-eq-T-matches-eqDT`.
    "datatypeI-fin-T-matches-fin" = {
      expr =
        let
          FinDT = self.datatypeI "Fin" self.nat [
            (self.conI "fzero" [ (self.field "m" self.nat) ]
              (p: self.succ p.m))
            (self.conI "fsuc" [
              (self.field "m" self.nat)
              (self.recFieldAt "k" (p: p.m))
            ]
              (p: self.succ p.m))
          ];
          macroForm = lam "n" self.nat (n: app FinDT.T n);
          handForm = lam "n" self.nat (n: app self.fin n);
        in
        semEq macroForm handForm;
      expected = true;
    };

    "datatypeI-fin-fzero-matches" = {
      expr =
        let
          FinDT = self.datatypeI "Fin" self.nat [
            (self.conI "fzero" [ (self.field "m" self.nat) ]
              (p: self.succ p.m))
            (self.conI "fsuc" [
              (self.field "m" self.nat)
              (self.recFieldAt "k" (p: p.m))
            ]
              (p: self.succ p.m))
          ];
          macroForm = FinDT.fzero;
          handForm = self.fzero;
        in
        semEq macroForm handForm;
      expected = true;
    };

    "datatypeI-fin-fsuc-matches" = {
      expr =
        let
          FinDT = self.datatypeI "Fin" self.nat [
            (self.conI "fzero" [ (self.field "m" self.nat) ]
              (p: self.succ p.m))
            (self.conI "fsuc" [
              (self.field "m" self.nat)
              (self.recFieldAt "k" (p: p.m))
            ]
              (p: self.succ p.m))
          ];
          macroForm = lam "m" self.nat (m:
            lam "k" (app self.fin m) (k:
              app FinDT.fsuc k));
          handForm = lam "m" self.nat (m:
            lam "k" (app self.fin m) (k:
              self.fsuc k));
        in
        semEq macroForm handForm;
      expected = true;
    };

    "datatypePI-vec-D-matches-vecDesc" = {
      expr =
        let
          VecDT = self.datatypePI "Vec"
            [{ name = "A"; kind = u 0; }]
            (_: self.nat)
            (ps:
              let A = builtins.elemAt ps 0; in [
                (self.conI "vnil" [ ] (_: self.zero))
                (self.conI "vcons"
                  [
                    (self.field "m" self.nat)
                    (self.field "x" A)
                    (self.recFieldAt "xs" (p: p.m))
                  ]
                  (p: self.succ p.m))
              ]);
          macroForm = lam "A" (u 0) (A: app VecDT.D A);
          handForm = lam "A" (u 0) (A: self.vecDesc A);
        in
        semEq macroForm handForm;
      expected = true;
    };
    "datatypePI-vec-D-carries-desc-ref" = {
      expr = let d = E.eval [ ] (elab (app self.VecDT.D nat)); in {
        kind = d._descRef.kind;
        arity = d._descRef.arity;
        indexed = d._descRef.indexed;
        params = builtins.length d._descRef.params;
      };
      expected = {
        kind = "datatype-desc";
        arity = 2;
        indexed = true;
        params = 1;
      };
    };

    # Same α-equivalence pattern as `datatypeI-fin-T-matches-fin`: apply
    # `VecDT.T A` and `self.vec A` to a fresh nat marker so the inner
    # index binder is β-reduced out of the resulting comparison.
    "datatypePI-vec-T-matches-vec" = {
      expr =
        let
          VecDT = self.datatypePI "Vec"
            [{ name = "A"; kind = u 0; }]
            (_: self.nat)
            (ps:
              let A = builtins.elemAt ps 0; in [
                (self.conI "vnil" [ ] (_: self.zero))
                (self.conI "vcons"
                  [
                    (self.field "m" self.nat)
                    (self.field "x" A)
                    (self.recFieldAt "xs" (p: p.m))
                  ]
                  (p: self.succ p.m))
              ]);
          macroForm = lam "A" (u 0) (A:
            lam "n" self.nat (n: app (app VecDT.T A) n));
          handForm = lam "A" (u 0) (A:
            lam "n" self.nat (n: app (self.vec A) n));
        in
        semEq macroForm handForm;
      expected = true;
    };

    "datatypePI-eq-D-matches-eqDesc" = {
      expr =
        let
          EqDT = self.datatypePI "Eq"
            [{ name = "A"; kind = u 0; }
              { name = "a"; kind = ms: builtins.elemAt ms 0; }]
            (ps: builtins.elemAt ps 0)
            (ps:
              let a = builtins.elemAt ps 1; in [
                (self.conI "refl" [ ] (_: a))
              ]);
          macroForm = lam "A" (u 0) (A:
            lam "a" A (a: app (app EqDT.D A) a));
          handForm = lam "A" (u 0) (A:
            lam "a" A (a: self.eqDesc A a));
        in
        semEq macroForm handForm;
      expected = true;
    };
    "datatypePI-eq-D-carries-desc-ref" = {
      expr = let d = E.eval [ ] (elab (app (app self.EqDT.D nat) zero)); in {
        kind = d._descRef.kind;
        arity = d._descRef.arity;
        indexed = d._descRef.indexed;
        params = builtins.length d._descRef.params;
      };
      expected = {
        kind = "datatype-desc";
        arity = 1;
        indexed = true;
        params = 2;
      };
    };

    "datatypePI-eq-T-matches-eqDT" = {
      expr =
        let
          EqDT = self.datatypePI "Eq"
            [{ name = "A"; kind = u 0; }
              { name = "a"; kind = ms: builtins.elemAt ms 0; }]
            (ps: builtins.elemAt ps 0)
            (ps:
              let a = builtins.elemAt ps 1; in [
                (self.conI "refl" [ ] (_: a))
              ]);
          macroForm = lam "A" (u 0) (A:
            lam "a" A (a:
              lam "b" A (b:
                app (app (app EqDT.T A) a) b)));
          handForm = lam "A" (u 0) (A:
            lam "a" A (a:
              lam "b" A (b: self.eqDT A a b)));
        in
        semEq macroForm handForm;
      expected = true;
    };

    # ===== Fin prelude =====
    # `Fin : Nat → U` is indexed over Nat. Two constructors: `fzero m : Fin (succ m)`
    # and `fsuc m k : Fin (succ m)` with `k : Fin m`. `Fin 0` is vacuous — the
    # ret-leaf obligation `Eq Nat (succ m) 0` is uninhabited — and `absurdFin0`
    # discharges the empty-case via no-confusion on Nat.

    "fin-as-type-checks" = {
      # fin : Nat → U. Applied to a concrete Nat, we get a type at U(0).
      expr =
        let
          ty = app fin (succ (succ zero));
        in
        (checkHoas (u 0) ty).tag;
      expected = "app";
    };

    "fin0-as-type-checks" = {
      # Fin 0 is a valid type (just uninhabited).
      expr = (checkHoas (u 0) (app fin zero)).tag;
      expected = "app";
    };

    "fzero-at-fin1-checks" = {
      # fzero : Fin (succ zero) = Fin 1.
      expr = (checkHoas (app fin (succ zero)) fzero).tag;
      expected = "desc-con";
    };

    "fzero-payload-homogeneous-lifts-erased" = {
      expr =
        let
          tm = checkHoas (app fin (succ zero)) fzero;
          payload = tm.d.term;
        in
        {
          dTag = tm.d.tag;
          fieldTag = payload.fst.tag;
          retTag = payload.snd.tag;
        };
      expected = {
        dTag = "boot-inl";
        fieldTag = "desc-con";
        retTag = "boot-refl";
      };
    };

    "fzero-cert-wrong-target-falls-back" = {
      expr =
        let
          goodTm = elab (fzeroAt zero);
          badTm = goodTm // {
            _descConCert = goodTm._descConCert // {
              target = elab zero;
            };
          };
          tyVal = E.eval [ ] (elab (app fin (succ zero)));
          result = CH.runCheck (CH.check CH.emptyCtx badTm tyVal);
        in
        {
          tag = result.tag or null;
          hasCert = result ? _descConCert;
        };
      expected = {
        tag = "desc-con";
        hasCert = false;
      };
    };

    "fzero-cert-missing-target-falls-back" = {
      expr =
        let
          goodTm = elab (fzeroAt zero);
          badTm = goodTm // {
            _descConCert = builtins.removeAttrs goodTm._descConCert [ "target" ];
          };
          tyVal = E.eval [ ] (elab (app fin (succ zero)));
          result = CH.runCheck (CH.check CH.emptyCtx badTm tyVal);
        in
        {
          tag = result.tag or null;
          hasCert = result ? _descConCert;
        };
      expected = {
        tag = "desc-con";
        hasCert = false;
      };
    };

    "fzero-at-fin2-checks" = {
      # fzero : Fin 2.
      expr = (checkHoas (app fin (succ (succ zero))) fzero).tag;
      expected = "desc-con";
    };

    "fsuc-at-fin2-checks" = {
      # fsuc fzero : Fin 2.
      expr =
        let
          two = succ (succ zero);
        in
        (checkHoas (app fin two) (fsuc fzero)).tag;
      expected = "desc-con";
    };

    # β-reduction on `finElim P Pz Ps 2 (fzero 1)` — collapses to `Pz 1`.
    # Motive is constant: P n k = nat. Pz m = zero. Ps m k ih = succ ih.
    # Expected NF: `zero` (which nf's to `descCon natDesc tt (pair true_ refl)`).
    "finElim-beta-on-fzero" = {
      expr =
        let
          two = succ (succ zero);
          oneN = succ zero;
          P = lam "n" nat (n: lam "_k" (app fin n) (_: nat));
          Pz = lam "m" nat (_: zero);
          Ps = lam "m" nat (m: lam "_k" (app fin m) (_: lam "ih" nat (ih: succ ih)));
          elimmed = finElim 0 P Pz Ps two (fzeroAt oneN);
        in
        semEq elimmed zero;
      expected = true;
    };

    # β-reduction on `finElim P Pz Ps 2 (fsuc 1 (fzero 0))`:
    #   → Ps 1 (fzero 0) (finElim P Pz Ps 1 (fzero 0))
    #   → Ps 1 (fzero 0) (Pz 0)
    #   → Ps 1 (fzero 0) zero
    #   → succ zero.
    "finElim-beta-on-fsuc" = {
      expr =
        let
          two = succ (succ zero);
          oneN = succ zero;
          P = lam "n" nat (n: lam "_k" (app fin n) (_: nat));
          Pz = lam "m" nat (_: zero);
          Ps = lam "m" nat (m: lam "_k" (app fin m) (_: lam "ih" nat (ih: succ ih)));
          elimmed = finElim 0 P Pz Ps two (fsucAt oneN (fzeroAt zero));
        in
        semEq elimmed (succ zero);
      expected = true;
    };

    # `absurdFin0` type-checks at any target type, when applied to a Fin 0
    # inhabitant. Fin 0 has no canonical inhabitant; we supply a neutral via
    # a lam-binder so checkHoas can type-check the elimination.
    "absurdFin0-checks-at-constant-target" = {
      expr =
        let
          tm = lam "x" (app fin zero) (x: absurdFin0 nat x);
        in
        (checkHoas (forall "_" (app fin zero) (_: nat)) tm).tag;
      expected = "lam";
    };

    # ===== Le prelude =====
    # `Le : Nat → Nat → U` is the Agda `Data.Nat.Base._≤_` inductive
    # predicate, doubly indexed via `Σ Nat (_: Nat)`. Two constructors:
    #   leZ  : ∀ n. Le 0 n
    #   leSS : ∀ m n. Le m n → Le (suc m) (suc n)
    # Decidability via `decideLeNat` recurses simultaneously on both
    # arguments, matching the constructor shape.

    "le-as-type-checks" = {
      # `le 0 5 : U(0)`. Doubly-indexed; surface curries the Σ-typed kernel index.
      expr =
        let
          five = succ (succ (succ (succ (succ zero))));
        in
        (checkHoas (u 0) (le zero five)).tag;
      expected = "app";
    };

    "le-zero-zero-as-type-checks" = {
      # `Le 0 0` is inhabited (by `leZ 0`); contrast with `Fin 0` which is vacuous.
      expr = (checkHoas (u 0) (le zero zero)).tag;
      expected = "app";
    };

    "leZ-at-le05-checks" = {
      # `leZ 5 : le 0 5`.
      expr =
        let
          five = succ (succ (succ (succ (succ zero))));
        in
        (checkHoas (le zero five) leZ).tag;
      expected = "desc-con";
    };

    "leSS-at-le12-checks" = {
      # `leSS 0 1 (leZ 1) : le 1 2`.
      expr =
        let
          oneN = succ zero;
        in
        (checkHoas (le oneN (succ oneN)) (leSS leZ)).tag;
      expected = "desc-con";
    };

    "leSS-at-le23-checks" = {
      # Two-step suc-suc: `leSS 1 2 (leSS 0 1 (leZ 1)) : le 2 3`.
      expr =
        let
          oneN = succ zero;
          twoN = succ oneN;
          threeN = succ twoN;
          inner = leSS leZ;
        in
        (checkHoas (le twoN threeN) (leSS inner)).tag;
      expected = "desc-con";
    };

    # β-reduction on `leElim` with constant motive `P m n _ = nat`,
    # `Pz n = zero`, `Ps m n lemn ih = succ ih`. Mirrors `finElim-beta-*`.

    "leElim-beta-on-leZ" = {
      # `leElim 0 P Pz Ps 0 5 (leZ 5)` → `Pz 5` → `zero`.
      expr =
        let
          five = succ (succ (succ (succ (succ zero))));
          P = lam "m" nat (mv: lam "n" nat (nv:
            lam "_le" (le mv nv) (_: nat)));
          Pz = lam "n" nat (_: zero);
          Ps = lam "m" nat (mv: lam "n" nat (nv:
            lam "_lemn" (le mv nv) (_:
              lam "ih" nat (ih: succ ih))));
          elimmed = leElim 0 P Pz Ps zero five (leZAt five);
        in
        semEq elimmed zero;
      expected = true;
    };

    "leElim-beta-on-leSS" = {
      # `leElim 0 P Pz Ps 2 3 (leSS 1 2 (leSS 0 1 (leZ 1)))`:
      #   → Ps 1 2 _ (leElim … 1 2 (leSS 0 1 (leZ 1)))
      #   → Ps 1 2 _ (Ps 0 1 _ (leElim … 0 1 (leZ 1)))
      #   → Ps 1 2 _ (Ps 0 1 _ (Pz 1))
      #   → Ps 1 2 _ (Ps 0 1 _ zero)
      #   → Ps 1 2 _ (succ zero)
      #   → succ (succ zero) ≡ 2.
      expr =
        let
          oneN = succ zero;
          twoN = succ oneN;
          threeN = succ twoN;
          P = lam "m" nat (mv: lam "n" nat (nv:
            lam "_le" (le mv nv) (_: nat)));
          Pz = lam "n" nat (_: zero);
          Ps = lam "m" nat (mv: lam "n" nat (nv:
            lam "_lemn" (le mv nv) (_:
              lam "ih" nat (ih: succ ih))));
          inner = leSSAt zero oneN (leZAt oneN);
          outer = leSSAt oneN twoN inner;
          elimmed = leElim 0 P Pz Ps twoN threeN outer;
        in
        semEq elimmed twoN;
      expected = true;
    };

    # ===== Decidable surface =====
    # HoTT Book §1.7: True = ⊤, False = ⊥, And P Q = Σ P (_:Q),
    # Or P Q = P + Q, Not P = P → ⊥, Iff P Q = (P→Q) × (Q→P). Agda
    # `Relation.Nullary.Dec`: `Dec P := P ⊎ ¬ P` with `yes` / `no`
    # constructors and a `sumElim`-derived eliminator `decElim`. All
    # defined notions; zero kernel additions. Surface name `or_` carries
    # a trailing underscore because `or` is reserved in Nix identifier
    # position (mirrors `true_` / `false_`).

    "decidable-True-elaborates" = {
      # True = unit (HoTT Book §1.7).
      expr = (elab True).tag;
      expected = "unit";
    };

    "decidable-False-elaborates" = {
      # False = void = empty (HoTT Book §1.7).
      expr = (elab False).tag;
      expected = "empty";
    };

    "decidable-and-elaborates" = {
      # and P Q := Σ P (_:Q); elaborates to a sigma.
      expr = (elab (and unit unit)).tag;
      expected = "sigma";
    };

    "decidable-or-elaborates" = {
      # or_ P Q := P + Q; SumDT.T applied at both summands → app.
      expr = (elab (or_ unit unit)).tag;
      expected = "app";
    };

    "decidable-not-elaborates" = {
      # not P := P → void; elaborates to pi.
      expr = (elab (not unit)).tag;
      expected = "pi";
    };

    "decidable-iff-elaborates" = {
      # iff P Q := and (P→Q) (Q→P); outer connective is and → sigma.
      expr = (elab (iff unit unit)).tag;
      expected = "sigma";
    };

    "decidable-dec-elaborates" = {
      # dec P := sum P (not P); SumDT.T applied → app.
      expr = (elab (dec unit)).tag;
      expected = "app";
    };

    "decidable-yes-checks" = {
      # yes True tt : dec True. yes routes through SumDT.inl → desc-con.
      expr = (checkHoas (dec True) (yes True tt)).tag;
      expected = "desc-con";
    };

    "decidable-no-checks" = {
      # no False idVoid : dec False, where idVoid : void → void = not False.
      # (The empty type is the only `P` for which `not P` is non-vacuously
      # inhabited — by the identity on void.) Routes through SumDT.inr.
      expr =
        let
          idVoid = lam "x" void (x: x);
        in
        (checkHoas (dec False) (no False idVoid)).tag;
      expected = "desc-con";
    };

    "decidable-decElim-beta-on-yes" = {
      # decElim True M oy on (yes True tt) → oy tt → zero.
      expr =
        let
          M = lam "_" (dec True) (_: nat);
          oy = lam "_" True (_: zero);
          on = lam "_" (not True) (_: succ zero);
          elimmed = decElim True M oy on (yes True tt);
        in
        semEq elimmed zero;
      expected = true;
    };

    "decidable-decElim-beta-on-no" = {
      # decElim False M oy on (no False idVoid) → on idVoid → succ zero.
      expr =
        let
          idVoid = lam "x" void (x: x);
          M = lam "_" (dec False) (_: nat);
          oy = lam "x" False (x: absurd nat x);
          on = lam "_" (not False) (_: succ zero);
          elimmed = decElim False M oy on (no False idVoid);
        in
        semEq elimmed (succ zero);
      expected = true;
    };

    # ===== Compositional decidability =====
    # Agda `Relation.Nullary.Product` / `.Sum` / `.Negation`. Each test
    # confirms the canonical β-normal form is `yes _` (inl) or `no _`
    # (inr) by reducing `decElim` against a constant-`nat` motive that
    # returns `zero` on the yes-branch and `succ zero` on the no-branch.
    # If decAnd / decOr / decNot return the expected polarity, the
    # composed expression reduces to the corresponding nat literal.

    "decAnd-yes-yes-reduces-yes" = {
      # decAnd True True (yes _ tt) (yes _ tt) ≡ yes (and True True) (pair tt tt).
      expr =
        let
          d = decAnd True True (yes True tt) (yes True tt);
          # Probe: decElim against a motive that returns zero on yes, succ zero on no.
          probe = decElim (and True True)
            (lam "_" (dec (and True True)) (_: nat))
            (lam "_" (and True True) (_: zero))
            (lam "_" (not (and True True)) (_: succ zero))
            d;
        in
        semEq probe zero;
      expected = true;
    };

    "decAnd-yes-no-reduces-no" = {
      # decAnd True False (yes _ tt) (no _ idVoid) reduces to `no _ refut`.
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decAnd True False (yes True tt) (no False idVoid);
          probe = decElim (and True False)
            (lam "_" (dec (and True False)) (_: nat))
            (lam "_" (and True False) (_: zero))
            (lam "_" (not (and True False)) (_: succ zero))
            d;
        in
        semEq probe (succ zero);
      expected = true;
    };

    "decAnd-no-yes-reduces-no" = {
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decAnd False True (no False idVoid) (yes True tt);
          probe = decElim (and False True)
            (lam "_" (dec (and False True)) (_: nat))
            (lam "_" (and False True) (_: zero))
            (lam "_" (not (and False True)) (_: succ zero))
            d;
        in
        semEq probe (succ zero);
      expected = true;
    };

    "decOr-yes-yes-reduces-yes" = {
      expr =
        let
          d = decOr True True (yes True tt) (yes True tt);
          probe = decElim (or_ True True)
            (lam "_" (dec (or_ True True)) (_: nat))
            (lam "_" (or_ True True) (_: zero))
            (lam "_" (not (or_ True True)) (_: succ zero))
            d;
        in
        semEq probe zero;
      expected = true;
    };

    "decOr-yes-no-reduces-yes" = {
      # Either side `yes` makes the disjunction `yes`.
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decOr True False (yes True tt) (no False idVoid);
          probe = decElim (or_ True False)
            (lam "_" (dec (or_ True False)) (_: nat))
            (lam "_" (or_ True False) (_: zero))
            (lam "_" (not (or_ True False)) (_: succ zero))
            d;
        in
        semEq probe zero;
      expected = true;
    };

    "decOr-no-yes-reduces-yes" = {
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decOr False True (no False idVoid) (yes True tt);
          probe = decElim (or_ False True)
            (lam "_" (dec (or_ False True)) (_: nat))
            (lam "_" (or_ False True) (_: zero))
            (lam "_" (not (or_ False True)) (_: succ zero))
            d;
        in
        semEq probe zero;
      expected = true;
    };

    "decOr-no-no-reduces-no" = {
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decOr False False (no False idVoid) (no False idVoid);
          probe = decElim (or_ False False)
            (lam "_" (dec (or_ False False)) (_: nat))
            (lam "_" (or_ False False) (_: zero))
            (lam "_" (not (or_ False False)) (_: succ zero))
            d;
        in
        semEq probe (succ zero);
      expected = true;
    };

    "decNot-yes-reduces-no" = {
      # decNot of yes(P) is no(not P): we can't have `not P` if we have `P`.
      expr =
        let
          d = decNot True (yes True tt);
          probe = decElim (not True)
            (lam "_" (dec (not True)) (_: nat))
            (lam "_" (not True) (_: zero))
            (lam "_" (not (not True)) (_: succ zero))
            d;
        in
        semEq probe (succ zero);
      expected = true;
    };

    "decNot-no-reduces-yes" = {
      # decNot of no(P) is yes(not P): we have a refutation, so `not P` holds.
      expr =
        let
          idVoid = lam "x" void (x: x);
          d = decNot False (no False idVoid);
          probe = decElim (not False)
            (lam "_" (dec (not False)) (_: nat))
            (lam "_" (not False) (_: zero))
            (lam "_" (not (not False)) (_: succ zero))
            d;
        in
        semEq probe zero;
      expected = true;
    };

    # ===== Nat decidability witnesses =====
    # Probe pattern: each test applies `decElim` against a constant-nat
    # motive that returns `zero` on the yes branch and `succ zero` on the
    # no branch; the result's polarity is encoded as the reduced literal.

    "predNat-of-zero-is-zero" = {
      expr = semEq (app predNat zero) zero;
      expected = true;
    };

    "predNat-of-suc-3-is-2" = {
      expr =
        let
          two = succ (succ zero);
          three = succ two;
        in
        semEq (app predNat three) two;
      expected = true;
    };

    "decideEqNat-yes-on-0-0" = {
      expr =
        let
          d = app (app decideEqNat zero) zero;
          P = bootEq nat zero zero;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideEqNat-yes-on-3-3" = {
      expr =
        let
          three = succ (succ (succ zero));
          d = app (app decideEqNat three) three;
          P = bootEq nat three three;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideEqNat-no-on-3-5" = {
      expr =
        let
          three = succ (succ (succ zero));
          five = succ (succ three);
          d = app (app decideEqNat three) five;
          P = bootEq nat three five;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideEqNat-no-on-5-3" = {
      expr =
        let
          three = succ (succ (succ zero));
          five = succ (succ three);
          d = app (app decideEqNat five) three;
          P = bootEq nat five three;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideLeNat-yes-on-0-0" = {
      expr =
        let
          d = app (app decideLeNat zero) zero;
          P = le zero zero;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeNat-yes-on-0-5" = {
      expr =
        let
          five = succ (succ (succ (succ (succ zero))));
          d = app (app decideLeNat zero) five;
          P = le zero five;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeNat-yes-on-3-5" = {
      expr =
        let
          three = succ (succ (succ zero));
          five = succ (succ three);
          d = app (app decideLeNat three) five;
          P = le three five;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeNat-no-on-3-0" = {
      expr =
        let
          three = succ (succ (succ zero));
          d = app (app decideLeNat three) zero;
          P = le three zero;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideLeNat-no-on-5-3" = {
      expr =
        let
          three = succ (succ (succ zero));
          five = succ (succ three);
          d = app (app decideLeNat five) three;
          P = le five three;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    # ===== IntZ — literature-canonical 2-constructor Int =====
    # Agda `Data.Integer.Base` form. Tests cover constructor checks,
    # `intzLit` Nix-meta bridge at boundary cases (0, -1, ±n), and the
    # four-case `intzLe` cascade reducing to the appropriate Nat / unit /
    # void target in each sign quadrant.

    "intz-pos-checks" = {
      # intzPos 3 : intz. Routes through IntZDT.pos → desc-con.
      expr = (checkHoas intz (intzPos (natLit 3))).tag;
      expected = "desc-con";
    };

    "intz-negSucc-checks" = {
      # intzNegSucc 0 : intz (this is -1). Routes through IntZDT.negSucc.
      expr = (checkHoas intz (intzNegSucc (natLit 0))).tag;
      expected = "desc-con";
    };

    "intz-lit-zero-equals-pos-0" = {
      expr = semEq (intzLit 0) (intzPos (natLit 0));
      expected = true;
    };

    "intz-lit-positive-equals-pos" = {
      expr = semEq (intzLit 5) (intzPos (natLit 5));
      expected = true;
    };

    "intz-lit-negative-one-equals-negSucc-0" = {
      expr = semEq (intzLit (-1)) (intzNegSucc (natLit 0));
      expected = true;
    };

    "intz-lit-negative-three-equals-negSucc-2" = {
      expr = semEq (intzLit (-3)) (intzNegSucc (natLit 2));
      expected = true;
    };

    "intzLe-pos-pos-reduces-to-le" = {
      # intzLe (pos 2) (pos 5) ≡ le 2 5 (delegate to Nat Le).
      expr =
        let
          two = natLit 2;
          five = natLit 5;
        in
        semEq (intzLe (intzPos two) (intzPos five)) (le two five);
      expected = true;
    };

    "intzLe-pos-negSucc-reduces-to-void" = {
      # intzLe (pos _) (negSucc _) ≡ void (positives are never ≤ negatives).
      expr = semEq (intzLe (intzPos (natLit 2)) (intzNegSucc (natLit 0))) void;
      expected = true;
    };

    "intzLe-negSucc-pos-reduces-to-unit" = {
      # intzLe (negSucc _) (pos _) ≡ unit (negatives are always ≤ positives).
      expr = semEq (intzLe (intzNegSucc (natLit 0)) (intzPos (natLit 2))) unit;
      expected = true;
    };

    "intzLe-negSucc-negSucc-reduces-to-flipped-le" = {
      # intzLe (negSucc 2) (negSucc 0): -3 ≤ -1 iff Nat-le-flipped(0, 2) iff le 0 2.
      # negSucc is monotonically decreasing in its argument: bigger Nat → smaller IntZ.
      expr =
        let
          zeroN = natLit 0;
          two = natLit 2;
        in
        semEq (intzLe (intzNegSucc two) (intzNegSucc zeroN)) (le zeroN two);
      expected = true;
    };

    "signsDiffer-types-as-refutation" = {
      # signsDiffer is a refutation `(m n : Nat) → Eq IntZ (pos m) (negSucc n) → void`.
      # Wrap in a closed lam abstracting m, n, e and check against the expected Π-type.
      expr =
        let
          refutTy = forall "m" nat (mv:
            forall "n" nat (nv:
              forall "_e" (bootEq intz (intzPos mv) (intzNegSucc nv)) (_:
                void)));
          refut = lam "m" nat (mv:
            lam "n" nat (nv:
              lam "e" (bootEq intz (intzPos mv) (intzNegSucc nv)) (e:
                ann (signsDiffer mv nv e) void)));
          r = checkHoas refutTy refut;
        in
        if r ? tag then r.tag else (r.msg or "ERROR-NO-MSG");
      expected = "lam";
    };

    "signsDifferRev-types-as-refutation" = {
      # `(m n : Nat) → Eq IntZ (negSucc m) (pos n) → void`.
      expr =
        let
          refutTy = forall "m" nat (mv:
            forall "n" nat (nv:
              forall "_e" (bootEq intz (intzNegSucc mv) (intzPos nv)) (_:
                void)));
          refut = lam "m" nat (mv:
            lam "n" nat (nv:
              lam "e" (bootEq intz (intzNegSucc mv) (intzPos nv)) (e:
                ann (signsDifferRev mv nv e) void)));
          r = checkHoas refutTy refut;
        in
        if r ? tag then r.tag else (r.msg or "ERROR-NO-MSG");
      expected = "lam";
    };

    # ===== Decidability witnesses over IntZ =====
    # Sign-quadrant cascade over the IntZ surface. Each test runs the
    # `decElim`-probe pattern (yes ⇒ `zero`, no ⇒ `succ zero`) and compares
    # the elaborated normal form against the expected sentinel.

    "decideEqIntZ-pos-pos-yes" = {
      expr =
        let
          three = natLit 3;
          m = intzPos three;
          n = intzPos three;
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideEqIntZ-pos-pos-no" = {
      expr =
        let
          m = intzPos (natLit 3);
          n = intzPos (natLit 5);
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideEqIntZ-pos-negSucc-no" = {
      expr =
        let
          m = intzPos (natLit 0);
          n = intzNegSucc (natLit 0);
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideEqIntZ-negSucc-pos-no" = {
      expr =
        let
          m = intzNegSucc (natLit 0);
          n = intzPos (natLit 0);
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideEqIntZ-negSucc-negSucc-yes" = {
      expr =
        let
          m = intzNegSucc (natLit 2);
          n = intzNegSucc (natLit 2);
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideEqIntZ-negSucc-negSucc-no" = {
      expr =
        let
          m = intzNegSucc (natLit 2);
          n = intzNegSucc (natLit 0);
          d = app (app decideEqIntZ m) n;
          P = bootEq intz m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideLeIntZ-pos-pos-yes" = {
      expr =
        let
          m = intzPos (natLit 2);
          n = intzPos (natLit 5);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeIntZ-pos-pos-no" = {
      expr =
        let
          m = intzPos (natLit 5);
          n = intzPos (natLit 2);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideLeIntZ-pos-negSucc-no" = {
      # +0 ≤ -1 is false.
      expr =
        let
          m = intzPos (natLit 0);
          n = intzNegSucc (natLit 0);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "decideLeIntZ-negSucc-pos-yes" = {
      # -1 ≤ +0 is true.
      expr =
        let
          m = intzNegSucc (natLit 0);
          n = intzPos (natLit 0);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeIntZ-negSucc-negSucc-flipped-yes" = {
      # -3 ≤ -1 is true; quadrant flips arguments so `decideLeNat 0 2`.
      expr =
        let
          m = intzNegSucc (natLit 2);
          n = intzNegSucc (natLit 0);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "decideLeIntZ-negSucc-negSucc-flipped-no" = {
      # -1 ≤ -3 is false; flipped delegate `decideLeNat 2 0`.
      expr =
        let
          m = intzNegSucc (natLit 0);
          n = intzNegSucc (natLit 2);
          d = app (app decideLeIntZ m) n;
          P = intzLe m n;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    # ===== Refinement-predicate carrier + composite predicates =====
    # End-to-end exercise of the decidable surface stack: connectives
    # (decAnd / decOr / decNot), Nat decidability (decideLeNat /
    # decideEqNat), and IntZ decidability (decideLeIntZ / decideEqIntZ).
    # Each composite test elaborates a probe term whose β-normal form is
    # `zero` for the yes branch and `succ zero` for the no branch, then
    # compares against the expected sentinel.

    "refinementPred-types-as-sigma" = {
      # refinementPred IntZ (λ_. True) : U(0). Type-only check; the
      # carrier `Σ (x:IntZ) (Dec True)` is well-formed at U(0).
      expr = (checkHoas (u 0)
        (refinementPred intz (_x: True))).tag;
      expected = "sigma";
    };

    "composite-x-ge-zero-yes-on-3" = {
      # x ≥ 0 via decideLeIntZ (pos 0) x; at x = pos 3 reduces to yes.
      expr =
        let
          x = intzLit 3;
          zeroI = intzLit 0;
          d = app (app decideLeIntZ zeroI) x;
          P = intzLe zeroI x;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-ge-zero-no-on-neg-one" = {
      # At x = -1 (negSucc 0): decideLeIntZ (pos 0) (negSucc 0) → no.
      expr =
        let
          x = intzLit (-1);
          zeroI = intzLit 0;
          d = app (app decideLeIntZ zeroI) x;
          P = intzLe zeroI x;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "composite-x-in-0-100-yes-on-50" = {
      # 0 ≤ x ≤ 100 via decAnd (decideLeIntZ 0 x) (decideLeIntZ x 100).
      expr =
        let
          x = intzLit 50;
          zeroI = intzLit 0;
          hundred = intzLit 100;
          P1 = intzLe zeroI x;
          P2 = intzLe x hundred;
          d1 = app (app decideLeIntZ zeroI) x;
          d2 = app (app decideLeIntZ x) hundred;
          d = decAnd P1 P2 d1 d2;
          P = and P1 P2;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-in-0-100-yes-on-boundary-0" = {
      expr =
        let
          x = intzLit 0;
          zeroI = intzLit 0;
          hundred = intzLit 100;
          P1 = intzLe zeroI x;
          P2 = intzLe x hundred;
          d1 = app (app decideLeIntZ zeroI) x;
          d2 = app (app decideLeIntZ x) hundred;
          d = decAnd P1 P2 d1 d2;
          P = and P1 P2;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-in-0-100-no-on-neg-one" = {
      # Left-boundary violation: x = -1 fails the lower bound.
      expr =
        let
          x = intzLit (-1);
          zeroI = intzLit 0;
          hundred = intzLit 100;
          P1 = intzLe zeroI x;
          P2 = intzLe x hundred;
          d1 = app (app decideLeIntZ zeroI) x;
          d2 = app (app decideLeIntZ x) hundred;
          d = decAnd P1 P2 d1 d2;
          P = and P1 P2;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    # Right-boundary violation: x = 101 fails the upper bound — DISABLED.
    #
    # The workload reduces `decideLeIntZ x 100` whose Nat-Le path peels
    # `min(x, 100) = 100` recursive layers. Each layer adds ~16 `evalF`
    # frames to the libnix C++ stack and ~30 units of Nix `max-call-depth`
    # via the `app ihM np` boundary in the inner step body. That boundary
    # invokes a fresh `descInd` nested under the current one — the existing
    # `vDescIndLinearF` shortcut at `tc/eval/desc.nix` flattens layers
    # within a single `descInd` invocation but does not span the
    # cross-invocation cascade. At depth 100 the cumulative stack just
    # exceeds the 8192 KiB libnix default.
    #
    # Re-enable when the kernel evaluator's recursive call sites in
    # `tc/eval/{core,desc}.nix` and `tc/quote.nix` are defunctionalized
    # into an explicit Frame ADT driven by `builtins.genericClosure` /
    # `builtins.foldl'`. The acceptance gate is: `decideLeNat N N` at
    # N=10000 must normalize under `nix-instantiate --eval --strict` at
    # default `ulimit -s 8192` and default `max-call-depth 10000`.
    # Stronger falsifier recommended at acceptance: also pass at
    # N=100000 — if N=10000 passes and N=100000 fails, an O(N) site has
    # been missed.

    "composite-x-ne-zero-no-on-0" = {
      # x ≠ 0 via decNot (decideEqIntZ x 0); at x = 0 the inner is yes,
      # so decNot returns no.
      expr =
        let
          x = intzLit 0;
          zeroI = intzLit 0;
          P0 = bootEq intz x zeroI;
          d0 = app (app decideEqIntZ x) zeroI;
          d = decNot P0 d0;
          P = not P0;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "composite-x-ne-zero-yes-on-neg-one" = {
      expr =
        let
          x = intzLit (-1);
          zeroI = intzLit 0;
          P0 = bootEq intz x zeroI;
          d0 = app (app decideEqIntZ x) zeroI;
          d = decNot P0 d0;
          P = not P0;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-ne-zero-yes-on-1" = {
      expr =
        let
          x = intzLit 1;
          zeroI = intzLit 0;
          P0 = bootEq intz x zeroI;
          d0 = app (app decideEqIntZ x) zeroI;
          d = decNot P0 d0;
          P = not P0;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-eq-0-or-1-yes-on-0" = {
      # x = 0 ∨ x = 1 via decOr (decideEqIntZ x 0) (decideEqIntZ x 1).
      expr =
        let
          x = intzLit 0;
          zeroI = intzLit 0;
          oneI = intzLit 1;
          P0 = bootEq intz x zeroI;
          P1 = bootEq intz x oneI;
          d = decOr P0 P1
            (app (app decideEqIntZ x) zeroI)
            (app (app decideEqIntZ x) oneI);
          P = or_ P0 P1;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-eq-0-or-1-yes-on-1" = {
      expr =
        let
          x = intzLit 1;
          zeroI = intzLit 0;
          oneI = intzLit 1;
          P0 = bootEq intz x zeroI;
          P1 = bootEq intz x oneI;
          d = decOr P0 P1
            (app (app decideEqIntZ x) zeroI)
            (app (app decideEqIntZ x) oneI);
          P = or_ P0 P1;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-eq-0-or-1-no-on-2" = {
      expr =
        let
          x = intzLit 2;
          zeroI = intzLit 0;
          oneI = intzLit 1;
          P0 = bootEq intz x zeroI;
          P1 = bootEq intz x oneI;
          d = decOr P0 P1
            (app (app decideEqIntZ x) zeroI)
            (app (app decideEqIntZ x) oneI);
          P = or_ P0 P1;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "composite-x-eq-0-or-1-no-on-neg-one" = {
      expr =
        let
          x = intzLit (-1);
          zeroI = intzLit 0;
          oneI = intzLit 1;
          P0 = bootEq intz x zeroI;
          P1 = bootEq intz x oneI;
          d = decOr P0 P1
            (app (app decideEqIntZ x) zeroI)
            (app (app decideEqIntZ x) oneI);
          P = or_ P0 P1;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "composite-x-ne-neg-one-no-on-neg-one" = {
      # ¬(x = -1) via decNot (decideEqIntZ x (negSucc 0)).
      expr =
        let
          x = intzLit (-1);
          negOne = intzLit (-1);
          Peq = bootEq intz x negOne;
          d = decNot Peq (app (app decideEqIntZ x) negOne);
          P = not Peq;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == noSentinel;
      expected = true;
    };

    "composite-x-ne-neg-one-yes-on-neg-two" = {
      expr =
        let
          x = intzLit (-2);
          negOne = intzLit (-1);
          Peq = bootEq intz x negOne;
          d = decNot Peq (app (app decideEqIntZ x) negOne);
          P = not Peq;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    "composite-x-ne-neg-one-yes-on-zero" = {
      expr =
        let
          x = intzLit 0;
          negOne = intzLit (-1);
          Peq = bootEq intz x negOne;
          d = decNot Peq (app (app decideEqIntZ x) negOne);
          P = not Peq;
        in
        Q.nf [ ] (elab (decProbeNat P d)) == yesSentinel;
      expected = true;
    };

    # ===== Vec prelude =====
    # `Vec A : Nat → U` is the indexed list family. Two constructors:
    # `vnil A : Vec A 0` (ret-leaf witness at zero) and
    # `vcons A m x xs : Vec A (succ m)` with `x : A`, `xs : Vec A m`.
    # `vhead A n (vcons A n x xs) ≡ x` — vnil case is unreachable via the
    # `natCaseU unit A` motive (unit at n=0, A at n=succ _).

    "vec-as-type-checks" = {
      # vec nat 2 : U(0).
      expr = (checkHoas (u 0) (app (vec nat) (succ (succ zero)))).tag;
      expected = "app";
    };

    "vec0-as-type-checks" = {
      # vec nat 0 is a valid type (with vnil as sole inhabitant).
      expr = (checkHoas (u 0) (app (vec nat) zero)).tag;
      expected = "app";
    };

    "vnil-at-vec0-checks" = {
      # vnil : vec nat 0.
      expr = (checkHoas (app (vec nat) zero) vnil).tag;
      expected = "desc-con";
    };

    "vcons-at-vec1-checks" = {
      # vcons zero vnil : vec nat 1.
      expr =
        let
          oneN = succ zero;
        in
        (checkHoas (app (vec nat) oneN) (vcons zero vnil)).tag;
      expected = "desc-con";
    };

    # β-reduction on `vecElim P Pn Pc 0 (vnil A)` — collapses to `Pn`.
    # Motive P n xs = nat (constant). Pn = zero. Pc m x xs ih = succ ih.
    # Expected nf: zero.
    "vecElim-beta-on-vnil" = {
      expr =
        let
          P = lam "n" nat (n: lam "_xs" (app (vec nat) n) (_: nat));
          Pn = zero;
          Pc = lam "m" nat (_m: lam "_x" nat (_: lam "_xs" (app (vec nat) _m) (_:
            lam "ih" nat (ih: succ ih))));
          elimmed = vecElim 0 nat P Pn Pc zero (vnilAt nat);
        in
        semEq elimmed zero;
      expected = true;
    };

    # β-reduction on `vecElim P Pn Pc 1 (vcons 0 vnil)`:
    #   → Pc 0 zero vnil (vecElim P Pn Pc 0 vnil)
    #   → Pc 0 zero (vnil A) Pn
    #   → succ Pn = succ zero.
    "vecElim-beta-on-vcons" = {
      expr =
        let
          oneN = succ zero;
          P = lam "n" nat (n: lam "_xs" (app (vec nat) n) (_: nat));
          Pn = zero;
          Pc = lam "m" nat (_m: lam "_x" nat (_: lam "_xs" (app (vec nat) _m) (_:
            lam "ih" nat (ih: succ ih))));
          vs = vconsAt nat zero zero (vnilAt nat);
          elimmed = vecElim 0 nat P Pn Pc oneN vs;
        in
        semEq elimmed (succ zero);
      expected = true;
    };

    # `vhead A n (vcons x xs) ≡ x`.
    # At A = nat, n = 0, x = zero, xs = vnil:
    #   vhead nat 0 (vcons zero vnil) ≡ zero.
    "vhead-beta-on-vcons" = {
      expr =
        let
          vs = vconsAt nat zero zero (vnilAt nat);
          hd = app (app (vhead nat) zero) vs;
        in
        semEq hd zero;
      expected = true;
    };

    # `vtail A n (vcons x xs) ≡ xs`.
    # At A = nat, n = 0, x = zero, xs = vnil:
    #   vtail nat 0 (vcons zero vnil) ≡ vnil.
    "vtail-beta-on-vcons" = {
      expr =
        let
          vs = vconsAt nat zero zero (vnilAt nat);
          tl = app (app (vtail nat) zero) vs;
        in
        semEq tl (vnilAt nat);
      expected = true;
    };

    # ===== Eq-as-description =====
    # `eqDT A a b = μ A (retI a) b` expresses propositional equality
    # as a single-constructor indexed inductive family; `reflDT` is
    # the canonical witness at the diagonal. `eqToEqDT` / `eqDTToEq`
    # form an iso with bootstrap identity, and `eqIsoFwd` / `eqIsoBwd`
    # prove the iso identity as HOAS terms.

    "eqDesc-at-nat-zero-checks" = {
      # eqDesc nat zero : Desc nat. The forwarder emits an app spine
      # over `EqDT.D`; under nf both layers β-reduce to the macro's
      # description body, which for the single-ctor refl spine is
      # exactly `retI zero`.
      expr = semEq (eqDesc nat zero) (retI nat 0 zero);
      expected = true;
    };

    "eqDT-at-refl-checks" = {
      # eqDT nat zero zero : U(0). Forwarder's app spine β-reduces under
      # nf to the bare `muI nat (retI zero) zero`.
      expr = semEq (eqDT nat zero zero) (muI nat (retI nat 0 zero) zero);
      expected = true;
    };

    "eqDT-value-head-projection-is-finite" = {
      expr = let v = E.eval [ ] (elab (eqDT nat zero zero)); in {
        tag = v.tag;
        dTag = v.D.tag;
        iTag = v.i.tag;
        hasDescRef = v.D ? _descRef;
        descKind = v.D._descRef.kind;
        params = builtins.length (v.D._descRef.params or [ ]);
        paramTags = map (p: p.tag) (v.D._descRef.params or [ ]);
      };
      expected = {
        tag = "VMu";
        dTag = "VDescCon";
        iTag = "VDescCon";
        hasDescRef = true;
        descKind = "datatype-desc";
        params = 2;
        paramTags = [ "VMu" "VDescCon" ];
      };
    };

    "eqDT-deep-nat-head-projection-5000" = {
      expr =
        let
          n = natLit 5000;
          v = E.eval [ ] (elab (eqDT nat n n));
        in
        {
          tag = v.tag;
          dTag = v.D.tag;
          iTag = v.i.tag;
          hasDescRef = v.D ? _descRef;
          descKind = v.D._descRef.kind;
          params = builtins.length (v.D._descRef.params or [ ]);
          paramTags = map (p: p.tag) (v.D._descRef.params or [ ]);
        };
      expected = {
        tag = "VMu";
        dTag = "VDescCon";
        iTag = "VDescCon";
        hasDescRef = true;
        descKind = "datatype-desc";
        params = 2;
        paramTags = [ "VMu" "VDescCon" ];
      };
    };

    "reflDT-at-zero-checks" = {
      # reflDT nat zero : eqDT nat zero zero.
      expr = (checkHoas (eqDT nat zero zero) (reflDT nat zero)).tag;
      expected = "desc-con";
    };

    "reflDT-at-anonymous-mu-checks" = {
      expr =
        let
          baseD = descRet;
          baseT = mu baseD tt;
          baseValue = descCon baseD tt bootRefl;
        in
        {
          explicit = (checkHoas (eqDT baseT baseValue baseValue)
            (reflDT baseT baseValue)).tag;
          public = (checkHoas (eq baseT baseValue baseValue) refl).tag;
        };
      expected = {
        explicit = "desc-con";
        public = "desc-con";
      };
    };

    "reflDT-check-cert-projection-is-finite" = {
      expr =
        let
          tm = checkHoas (eqDT nat zero zero) (reflDT nat zero);
        in
        {
          tag = tm.tag;
          dTag = tm.D.tag;
          iTag = tm.i.tag;
          payloadTag = tm.d.tag;
          hasCert = tm ? _descConCert;
          certKind = tm._descConCert.kind;
          certRefKind = tm._descConCert.ref.kind;
          certParams = builtins.length (tm._descConCert.ref.params or [ ]);
        };
      expected = {
        tag = "desc-con";
        dTag = "ann";
        iTag = "ann";
        payloadTag = "boot-refl";
        hasCert = true;
        certKind = "datatype-con-payload";
        certRefKind = "datatype-desc";
        certParams = 2;
      };
    };

    "eqToEqDT-at-refl-checks" = {
      # eqToEqDT nat 0 0 bootRefl : eqDT nat 0 0.
      expr = (checkHoas (eqDT nat zero zero)
        (eqToEqDT nat zero zero bootRefl)).tag;
      expected = "boot-j";
    };

    "eqDTToEq-at-reflDT-checks" = {
      # eqDTToEq nat 0 0 (reflDT nat 0) : bootEq nat 0 0.
      expr = (checkHoas (bootEq nat zero zero)
        (eqDTToEq nat zero zero (reflDT nat zero))).tag;
      expected = "desc-ind";
    };

    # nf-roundtrip at the bootRefl case:
    # `eqDTToEq (eqToEqDT bootRefl) ≡ bootRefl`.
    "eq-iso-fwd-at-refl-nf" = {
      expr =
        let
          t = eqDTToEq nat zero zero (eqToEqDT nat zero zero bootRefl);
        in
        semEq t bootRefl;
      expected = true;
    };

    # nf-roundtrip at the reflDT case: `eqToEqDT (eqDTToEq reflDT) ≡ reflDT`.
    # descInd on descCon exposes bootRefl; bootJ on bootRefl fires to reflDT.
    "eq-iso-bwd-at-reflDT-nf" = {
      expr =
        let
          t = eqToEqDT nat zero zero (eqDTToEq nat zero zero (reflDT nat zero));
        in
        semEq t (reflDT nat zero);
      expected = true;
    };

    # Iso proofs type-check at their claimed propositions. These are
    # the `to ∘ from ≡ id` / `from ∘ to ≡ id` acceptance witnesses.
    "eq-iso-fwd-checks" = {
      # eqIsoFwd nat 0 0 : Π(e : bootEq nat 0 0). bootEq (bootEq nat 0 0) (...) e.
      expr =
        let
          ty = forall "e" (bootEq nat zero zero) (e:
            bootEq (bootEq nat zero zero)
              (eqDTToEq nat zero zero (eqToEqDT nat zero zero e))
              e);
        in
        (checkHoas ty (eqIsoFwd nat zero zero)).tag;
      expected = "lam";
    };

    "eq-iso-bwd-checks" = {
      # eqIsoBwd nat 0 0 : Π(x : eqDT nat 0 0). bootEq (eqDT nat 0 0) (...) x.
      expr =
        let
          ty = forall "x" (eqDT nat zero zero) (x:
            bootEq (eqDT nat zero zero)
              (eqToEqDT nat zero zero (eqDTToEq nat zero zero x))
              x);
        in
        (checkHoas ty (eqIsoBwd nat zero zero)).tag;
      expected = "lam";
    };

    # Cascade onInl bodies in `encodeDescElim` must use saturated
    # `app` chains. Over-applied forms like
    # `app (app (app (app onRec j) D) ihD)` leave a curried Nix
    # lambda where the elaborator expects an HOAS attrset; elab then
    # throws "not an HOAS node (lambda)" when the body is forced.
    # The bug hides behind two outer `lam`s, so it only surfaces when
    # consumers walk the elaborated Tm tree deeply (e.g. extractDocs).
    "encodeDescElim-elab-deep-forces" = {
      expr = (builtins.tryEval
        (builtins.deepSeq (elab encodeDescElim) true)).success;
      expected = true;
    };

    "encodeDescElim-infers" = {
      expr = (inferHoas encodeDescElim).type.tag;
      expected = "VPi";
    };

    # ----- canonApp: generic identity-tagged HOAS application -----
    # Generic counterpart of `descDescApp` for user-registered
    # canonical descriptions. Eval applies `body` to each param and
    # stamps the resulting `VDescCon` with `_canonRef = { id; params; }`
    # so conv/quote short-circuit on the canonical identity instead of
    # forcing `.D`. Tests below pin the eval-time stamping shape and
    # the conv short-circuit at arities other than descDesc's
    # `[iLev, I, L]` shape.

    "canon-app-evals-to-VDescCon" = {
      expr = (E.eval [ ] (elab
        (canonApp "Tri" [ nat bool unit ]
          (lam "A" (u 0) (_:
            lam "B" (u 0) (_:
              lam "C" (u 0) (_: natDesc))))))).tag;
      expected = "VDescCon";
    };

    "canon-app-stamps-id" = {
      expr = (E.eval [ ] (elab
        (canonApp "myId" [ nat ]
          (lam "A" (u 0) (_: natDesc)))))._canonRef.id;
      expected = "myId";
    };

    "canon-app-stamps-params-length" = {
      expr = builtins.length
        (E.eval [ ] (elab
          (canonApp "Tri" [ nat bool unit ]
            (lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)))))))._canonRef.params;
      expected = 3;
    };

    "canon-app-conv-self-equal" = {
      expr =
        let
          body =
            lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)));
          v1 = E.eval [ ] (elab (canonApp "Tri" [ nat bool unit ] body));
          v2 = E.eval [ ] (elab (canonApp "Tri" [ nat bool unit ] body));
        in
        C.conv 0 v1 v2;
      expected = true;
    };

    "canon-app-conv-distinct-first-param-rejects" = {
      expr =
        let
          body =
            lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)));
          v1 = E.eval [ ] (elab (canonApp "Tri" [ nat bool unit ] body));
          v2 = E.eval [ ] (elab (canonApp "Tri" [ bool bool unit ] body));
        in
        C.conv 0 v1 v2;
      expected = false;
    };

    "canon-app-conv-distinct-id-rejects" = {
      expr =
        let
          body =
            lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)));
          v1 = E.eval [ ] (elab (canonApp "Tri-A" [ nat bool unit ] body));
          v2 = E.eval [ ] (elab (canonApp "Tri-B" [ nat bool unit ] body));
        in
        C.conv 0 v1 v2;
      expected = false;
    };

    "canon-app-quote-emits-canon-app-tag" = {
      expr =
        let
          body = lam "A" (u 0) (_: natDesc);
          v    = E.eval [ ] (elab (canonApp "MyOne" [ nat ] body));
        in (Q.quote 0 v).tag;
      expected = "canon-app";
    };

    "canon-app-quote-emits-id" = {
      expr =
        let
          body = lam "A" (u 0) (_: natDesc);
          v    = E.eval [ ] (elab (canonApp "MyOne" [ nat ] body));
        in (Q.quote 0 v).id;
      expected = "MyOne";
    };

    "canon-app-quote-emits-params-length" = {
      expr =
        let
          body =
            lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)));
          v = E.eval [ ] (elab (canonApp "Tri" [ nat bool unit ] body));
        in builtins.length (Q.quote 0 v).params;
      expected = 3;
    };

    "canon-app-quote-emits-body-tm" = {
      expr =
        let
          body = lam "A" (u 0) (_: natDesc);
          v    = E.eval [ ] (elab (canonApp "MyOne" [ nat ] body));
          q    = Q.quote 0 v;
        in builtins.isAttrs q.body && q.body ? tag;
      expected = true;
    };

    "canon-app-roundtrip-eval-quote-eval-VDescCon" = {
      expr =
        let
          body = lam "A" (u 0) (_: natDesc);
          v    = E.eval [ ] (elab (canonApp "MyOne" [ nat ] body));
          tm'  = Q.quote 0 v;
          v'   = E.eval [ ] tm';
        in v'.tag;
      expected = "VDescCon";
    };

    "canon-app-roundtrip-preserves-canonRef-id" = {
      expr =
        let
          body = lam "A" (u 0) (_: natDesc);
          v    = E.eval [ ] (elab (canonApp "MyOne" [ nat ] body));
          tm'  = Q.quote 0 v;
          v'   = E.eval [ ] tm';
        in v'._canonRef.id;
      expected = "MyOne";
    };

    # End-to-end through VMu wrapper: μ(canonApp id [p1..pn] body) i,
    # mimicking the freeFx-as-μ pattern. Conv on VMu × VMu reaches the
    # inner VDescCon-stamped value via `v.D`; the canon stamp short-
    # circuits without forcing `.D`'s body.
    "canon-app-mu-self-equal" = {
      expr =
        let
          body =
            lam "A" (u 0) (_:
              lam "B" (u 0) (_:
                lam "C" (u 0) (_: natDesc)));
          mkMu = mu (canonApp "Tri" [ nat bool unit ] body) tt;
          v1 = E.eval [ ] (elab mkMu);
          v2 = E.eval [ ] (elab mkMu);
        in
        C.conv 0 v1 v2;
      expected = true;
    };
  };
}
