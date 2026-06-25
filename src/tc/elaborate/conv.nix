# Meta-aware conversion for elaboration.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;
  C = fx.tc.conv;
  E = fx.tc.eval;
  V = fx.tc.value;

  Eff = self.metaEff;
  Resp = self.metaResp;

  pure_ = K.pure Eff Resp H.unit;
  bind_ = K.bind Eff Resp H.unit H.unit;

  unique = xs:
    builtins.foldl'
      (acc: x:
        if builtins.elem x acc then acc else acc ++ [ x ]
      ) [ ]
      xs;

  tagOf = v:
    if self.isVMeta v then "VMeta"
    else if builtins.isAttrs v then v.tag or null
    else null;

  idsInList = xs: builtins.concatLists (map metaIdsVal xs);

  idsInElim = elim:
    let t = elim.tag; in
    if t == "EApp" then metaIdsVal elim.arg
    else if t == "EFst" then [ ]
    else if t == "ESnd" then [ ]
    else if t == "EBootSumElim" then
      idsInList [
        elim.left
        elim.right
        elim.motive
        elim.onLeft
        elim.onRight
      ]
    else if t == "EBootJ" then
      idsInList [
        elim.type
        elim.lhs
        elim.motive
        elim.base
        elim.rhs
      ]
    else if t == "EStrEq" then metaIdsVal elim.arg
    else if t == "EStrLen" then [ ]
    else if t == "EIntEq" || t == "EIntLeL" || t == "EIntLeR" then metaIdsVal elim.arg
    else if t == "EDescInd" then
      idsInList [
        elim.D
        elim.motive
        elim.step
        elim.i
      ]
    else if t == "EInterpD" then
      idsInList [
        elim.level
        elim.I
        elim.X
        elim.i
      ]
    else if t == "EAllD" then
      idsInList [
        elim.level
        elim.I
        elim.K
        elim.X
        elim.M
        elim.i
        elim.d
      ]
    else if t == "EEverywhereD" then
      idsInList [
        elim.level
        elim.I
        elim.K
        elim.X
        elim.M
        elim.ih
        elim.i
        elim.d
      ]
    else if t == "ELiftElim" then
      idsInList [
        elim.l
        elim.m
        elim.eq
        elim.A
      ]
    else if t == "ESquashElim" then
      idsInList [
        elim.A
        elim.B
        elim.f
      ]
    else [ ];

  idsInSpine = spine:
    builtins.concatLists (map idsInElim spine);

  idsInVal = v:
    let t = tagOf v; in
    if t == "VMeta" then [ v.id ] ++ idsInSpine v.spine
    else if t == "VPi" then metaIdsVal v.domain
    else if t == "VLam" then metaIdsVal v.domain
    else if t == "VSigma" then metaIdsVal v.fst
    else if t == "VPair" then idsInList [ v.fst v.snd ]
    else if t == "VBootSum" then idsInList [ v.left v.right ]
    else if t == "VBootInl" then idsInList [ v.left v.right v.val ]
    else if t == "VBootInr" then idsInList [ v.left v.right v.val ]
    else if t == "VBootEq" then idsInList [ v.type v.lhs v.rhs ]
    else if t == "VSquash" then metaIdsVal v.A
    else if t == "VSquashIntro" then metaIdsVal v.a
    else if t == "VDesc" then idsInList [ v.level v.I ]
    else if t == "VMu" then idsInList [ v.I v.D v.i ]
    # `_canonRef`-tagged VDescCons stand for closed canonical terms whose
    # `.D`/`.i`/`.d` slots are built by applying a canonical body to
    # `params` (see eval/desc.nix:206, 222). User-introduced metas can
    # therefore only flow through `params`; walking the body would descend
    # into self-referential canonical encodings (e.g. `descDesc` nesting
    # through `Lift`/`LevelMax`) and stack-overflow. Mirrors the kernel
    # `canonRefConv` short-circuit at conv.nix:427-430.
    else if t == "VDescCon" then
      if v ? _canonRef
      then idsInList (v._canonRef.params or [ ])
      else idsInList [ v.D v.i v.d ]
    else if t == "VInterpD" then
      idsInList [
        v.level
        v.I
        v.D
        v.X
        v.i
      ]
    else if t == "VAllD" then
      idsInList [
        v.level
        v.I
        v.D
        v.K
        v.X
        v.M
        v.i
        v.d
      ]
    else if t == "VEverywhereD" then
      idsInList [
        v.level
        v.I
        v.D
        v.K
        v.X
        v.M
        v.ih
        v.i
        v.d
      ]
    else if t == "VLift" then idsInList [ v.l v.m v.eq v.A ]
    else if t == "VLiftIntro" then idsInList [ v.l v.m v.eq v.A v.a ]
    else if t == "VLevelSuc" then metaIdsVal v.pred
    else if t == "VLevelMax" then idsInList [ v.lhs v.rhs ]
    else if t == "VOpaqueLam" then metaIdsVal v.piTy
    else if t == "VNe" then idsInSpine v.spine
    else [ ];

  metaIdsVal = v: idsInVal v;

  containsMeta = v: metaIdsVal v != [ ];

  constraintFor = d: ty: lhs: rhs: {
    tag = "conv";
    depth = d;
    type = ty;
    inherit lhs rhs;
    mentions = unique (metaIdsVal lhs ++ metaIdsVal rhs ++ metaIdsVal ty);
    status = "postponed";
    position = null;
  };

  emitConvConstraint = d: ty: lhs: rhs:
    bind_ (self.emitConstraint (constraintFor d ty lhs rhs))
      (_cid: pure_ true);

  andThen = first: next:
    bind_ first (ok: if ok then next else pure_ false);

  elabConvPi = d: ty: lhs: rhs:
    let
      x = V.freshVar d;
      lhsBody = self.elabAppF 10000000 lhs x;
      rhsBody = self.elabAppF 10000000 rhs x;
      # Closure env may carry `VMeta`s; the overlay instantiator threads
      # meta-aware dispatch through the body so a meta never reaches the
      # kernel CEK machine (kernel-purity, value.nix:13-17).
      bodyTy = self.instantiateOverlay ty.closure x;
    in
    elabConv (d + 1) bodyTy lhsBody rhsBody;

  elabConvSigma = d: ty: lhs: rhs:
    let
      lhsFst = self.elabFst lhs;
      rhsFst = self.elabFst rhs;
      lhsSnd = self.elabSnd lhs;
      rhsSnd = self.elabSnd rhs;
      sndTy = self.instantiateOverlay ty.closure lhsFst;
    in
    andThen
      (elabConv d ty.fst lhsFst rhsFst)
      (elabConv d sndTy lhsSnd rhsSnd);

  # Structural Pi-type equality (§6.2): compare two VPi *types* by their
  # domains and (under a fresh var) their codomains. Distinct from
  # `elabConvPi` above, which η-decomposes two values *of* Pi type. Fires
  # when both sides are VPi values inhabiting a universe — e.g. residual
  # `m_B → Nat` vs explicit `Nat → Nat` after partial application of an
  # implicit-Pi head. Mirrors kernel conv.nix:230-233.
  elabConvPiTypes = d: lhs: rhs:
    let
      x = V.freshVar d;
      lhsBody = self.instantiateOverlay lhs.closure x;
      rhsBody = self.instantiateOverlay rhs.closure x;
      uZero = V.vU V.vLevelZero;
    in
    andThen
      (elabConv d uZero lhs.domain rhs.domain)
      (elabConv (d + 1) uZero lhsBody rhsBody);

  elabConvSigmaTypes = d: lhs: rhs:
    let
      x = V.freshVar d;
      lhsBody = self.instantiateOverlay lhs.closure x;
      rhsBody = self.instantiateOverlay rhs.closure x;
      uZero = V.vU V.vLevelZero;
    in
    andThen
      (elabConv d uZero lhs.fst rhs.fst)
      (elabConv (d + 1) uZero lhsBody rhsBody);

  elabConv = d: ty: lhs: rhs:
    let
      hasMeta = containsMeta ty || containsMeta lhs || containsMeta rhs;
      tyTag = tagOf ty;
      lhsTag = tagOf lhs;
      rhsTag = tagOf rhs;
    in
    if !hasMeta then pure_ (C.conv d lhs rhs)
    else if tyTag == "VPi" then elabConvPi d ty lhs rhs
    else if tyTag == "VSigma" then elabConvSigma d ty lhs rhs
    else if lhsTag == "VPi" && rhsTag == "VPi"
    then elabConvPiTypes d lhs rhs
    else if lhsTag == "VSigma" && rhsTag == "VSigma"
    then elabConvSigmaTypes d lhs rhs
    else emitConvConstraint d ty lhs rhs;

  type0 = {
    ctx = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
    ty = V.vUnit;
  };
  meta0 = self.mkVMeta 0 [ ] type0;
  piUnitUnit = V.vPi "_" V.vUnit (V.mkClosure [ ] fx.tc.term.mkUnit);
  sigmaUnitUnit = V.vSigma "_" V.vUnit (V.mkClosure [ ] fx.tc.term.mkUnit);
in
{
  scope = {
    elabConv = api.leaf {
      value = elabConv;
      description = "elabConv d ty lhs rhs: meta-aware conversion for elaboration. Rigid comparisons delegate to kernel conversion; comparisons involving `VMeta` emit postponed `conv` constraints; Pi/Sigma types are compared structurally using overlay eliminators so metas retain their spines.";
      signature = "elabConv : Depth -> Val -> ElabVal -> ElabVal -> Comp Bool";
      tests = {
        "elabConv-rigid-true" = {
          expr = (self.runElab H.unit (elabConv 0 V.vUnit V.vTt V.vTt)).value;
          expected = true;
        };
        "elabConv-rigid-false" = {
          expr = (self.runElab H.unit
            (elabConv 0 V.vString (V.vStringLit "a") (V.vStringLit "b"))).value;
          expected = false;
        };
        "elabConv-meta-emits-one-constraint" = {
          expr =
            let r = self.runElab H.unit (elabConv 0 V.vUnit meta0 V.vTt);
            in builtins.length r.state.constraints;
          expected = 1;
        };
        "elabConv-meta-constraint-shape" = {
          expr =
            let
              r = self.runElab H.unit (elabConv 0 V.vUnit meta0 V.vTt);
              c = builtins.head r.state.constraints;
            in
            {
              inherit (c) tag depth status mentions;
              lhsTag = c.lhs._vTag;
              rhsTag = c.rhs.tag;
              typeTag = c.type.tag;
            };
          expected = {
            tag = "conv";
            depth = 0;
            status = "solved";
            mentions = [ 0 ];
            lhsTag = "VMeta";
            rhsTag = "VTt";
            typeTag = "VUnit";
          };
        };
        "elabConv-pi-meta-spine" = {
          expr =
            let
              rhs = V.vLam "x" V.vUnit (V.mkClosure [ ] fx.tc.term.mkTt);
              r = self.runElab H.unit (elabConv 0 piUnitUnit meta0 rhs);
              c = builtins.head r.state.constraints;
            in
            (builtins.head c.lhs.spine).tag;
          expected = "EApp";
        };
        "elabConv-sigma-meta-emits-component-constraints" = {
          expr =
            let
              rhs = V.vPair V.vTt V.vTt;
              r = self.runElab H.unit (elabConv 0 sigmaUnitUnit meta0 rhs);
            in
            builtins.length r.state.constraints;
          expected = 2;
        };
        # Regression: opening a meta-bearing closure must stay in the overlay.
        # `elabConvPiTypes` opens both Pi closures, whose envs capture a
        # `VMeta` lifted in the body. Kernel instantiation would route the
        # meta into the CEK machine, whose `KLift_X` reads `.tag` (absent on
        # `VMeta`) and crashes.
        "elabConv-pitypes-meta-closure-stays-out-of-kernel" = {
          expr =
            let
              liftBody = fx.tc.term.mkLift fx.tc.term.mkLevelZero
                (fx.tc.term.mkLevelSuc fx.tc.term.mkLevelZero)
                fx.tc.term.mkBootRefl
                (fx.tc.term.mkVar 1);
              pi = V.vPi "x" meta0 (V.mkClosure [ meta0 ] liftBody);
            in
            (self.runElab H.unit (elabConv 0 (V.vU V.vLevelZero) pi pi)).value;
          expected = true;
        };
      };
    };
  };

}
