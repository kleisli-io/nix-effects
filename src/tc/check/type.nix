# Type formation (§7.5, §8.2).
#
# `checkTypeLevel : Ctx → Tm → Computation { term; level; }` verifies
# that `tm` is a type and returns both the elaborated term and the
# universe level it inhabits. `level` is a Level *value*
# (`V.vLevelZero`, `V.vLevelSuc`, `V.vLevelMax`) — not a Nix integer —
# so level-polymorphic types (`U(k)` for a variable `k : Level`) flow
# through without ad-hoc integer machinery. Levels come from the
# typing derivation, not post-hoc value inspection: e.g., `Π(x:A). B`
# computes its level as the `vLevelMax` of domain/codomain levels.
# The fallback path delegates to `infer` and succeeds iff the inferred
# type is a universe; in that case `.type.level` is already a Level
# value and is forwarded verbatim.
#
# `checkType` is the thin wrapper that forgets the level.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  C = fx.tc.conv;

  K = fx.kernel;
  pure = K.pure;
  send = K.send;
  bind = K.bind;

  D = fx.diag.error;

  # Shared `U(0)` value — every small-type sort check targets this.
  vU0 = V.vU V.vLevelZero;

  # Shared `suc zero` Level value — `desc I`'s universe level.
  vLevelSucZero = V.vLevelSuc V.vLevelZero;

  # Algebraic `vLevelMax` normalisation. The Level lattice's neutral
  # element is `VLevelZero`; `vLevelSuc` is monotone and distributes
  # over `max` (`max (suc a) (suc b) = suc (max a b)`); `max` is
  # idempotent (`max x x = x`). Applying these rules eagerly keeps
  # iso-grade level expressions in normal form so `convLevel` does not
  # have to reason modulo distributivity. Without `suc`-distribution,
  # `max(suc 0, suc k)` stays stuck for abstract `k` and the All-type
  # for `descArg L`-summands at `L > 0` rejects motives whose codomain
  # universe is below `L`.
  vLevelMaxOpt = a: b:
    if a.tag == "VLevelZero" then b
    else if b.tag == "VLevelZero" then a
    else if a.tag == "VLevelSuc" && b.tag == "VLevelSuc"
    then V.vLevelSuc (vLevelMaxOpt a.pred b.pred)
    else if a == b then a
    else V.vLevelMax a b;

  # `levelOf : Ctx → Tm → LevelVal | null` — pure structural walker
  # reading a description Tm's intrinsic universe level without
  # demanding inference of its index sub-terms. The bidirectional
  # discipline accepts canonical leaves (`descRet ttPrim`, `descRet
  # refl`, …) at index positions only via CHECK against the parent
  # description's I-type; switching CHECK→INFER on a sub-description
  # to read its level breaks any description containing such a leaf.
  # `levelOf` reads the level from the constructor's tag fields
  # (`tm.k`, `tm.D`, …) and returns the same `LevelVal` algebra the
  # CHECK rules produce in their result types — so callers can
  # propagate it without monadic plumbing.
  #
  # `var` falls back to `ctx.types[idx].level` when the variable's
  # type is a `VDesc`. Any unrecognised shape returns `null`; callers
  # treat that as "level not statically derivable" and either
  # conservatively skip the level constraint or default to
  # `vLevelZero`.
  evalK = ctx: kTm:
    if kTm.tag == "level-zero"
    then V.vLevelZero
    else E.eval ctx.env kTm;

  levelOf = ctx: tm:
    let t = tm.tag; in
    if t == "desc-ret" then V.vLevelZero
    else if t == "desc-arg" then
      let
        kVal = evalK ctx tm.k;
        sVal = E.eval ctx.env tm.S;
        ctx' = self.extend ctx "_" sVal;
        bodyLev = levelOf ctx' tm.T;
      in if bodyLev == null then null
         else vLevelMaxOpt kVal bodyLev
    else if t == "desc-rec" then levelOf ctx tm.D
    else if t == "desc-pi" then
      let
        kVal = evalK ctx tm.k;
        bodyLev = levelOf ctx tm.D;
      in if bodyLev == null then null
         else vLevelMaxOpt kVal bodyLev
    else if t == "desc-plus" then
      let
        aLev = levelOf ctx tm.A;
        bLev = levelOf ctx tm.B;
      in if aLev == null || bLev == null then null
         else vLevelMaxOpt aLev bLev
    else if t == "var" then
      let ty = self.lookupType ctx tm.idx;
      in if ty.tag == "VDesc" then ty.level else null
    else null;

  # Decide whether a description Tm tag is one of the kernel's
  # canonical introduction forms (`desc-ret`/`-arg`/`-rec`/`-pi`/
  # `-plus`). The bidirectional discipline propagates the parent
  # description's I-type and level through CHECK on these — sound
  # under the desc-* CHECK rules' `max ≡` validation. Non-canonical
  # shapes (`var`, `app`, `let`, `ann`, …) lack a check-mode rule and
  # must be INFERed; the inferred VDesc carries its actual level.
  #
  # Implemented as an attrset `?` lookup (single `OpHasAttr`) rather
  # than a chain of `||`-disjoined `==` tests: in deep cons-chain
  # CHECK the desc-con rule fires once per layer with `tm.D.tag ==
  # "ann"` (the elaborator emits an annotated description per
  # constructor), so the non-canonical branch dominates and the
  # disjunction-chain pays N `==` primops per layer. The cached
  # attrset shifts this to one `OpHasAttr` per layer regardless of
  # the tag.
  canonicalDescTags = {
    "desc-ret" = null;
    "desc-arg" = null;
    "desc-rec" = null;
    "desc-pi" = null;
    "desc-plus" = null;
  };
  isCanonicalDescTag = t: canonicalDescTags ? ${t};
in {
  scope = {
    inherit levelOf;

    # `checkDescAtAnyLevel : Ctx → Tm → Val → Computation { term; level; }`
    # — admit a description term at any universe level under a known
    # index type `iTyVal`. Canonical introduction forms route through
    # CHECK at the level-zero soundness anchor (the desc-* CHECK rules
    # validate internal levels via `max ≡`); non-canonical shapes are
    # INFERed and the result type's `VDesc` is structurally validated
    # to carry the expected I. The returned `level` is the description's
    # actual intrinsic level: from `levelOf` after CHECK on canonical
    # forms (the walker reads each constructor's tag fields), or from
    # the inferred `VDesc.level` directly on non-canonical shapes —
    # the latter covers `app descDesc k : desc^(suc k) ⊤` and other
    # opaque-but-typeable descriptions whose level the syntactic walker
    # cannot recover from the Tm alone.
    checkDescAtAnyLevel = ctx: dTm: iTyVal:
      if isCanonicalDescTag dTm.tag
      then bind (self.check ctx dTm (V.vDesc V.vLevelZero iTyVal)) (resTm:
        let lv = self.levelOf ctx resTm;
            actualLev = if lv == null then V.vLevelZero else lv;
        in pure { term = resTm; level = actualLev; })
      else bind (self.infer ctx dTm) (dResult:
        let
          dTy = dResult.type;
          # Recognise an encoded description type `μ⊤(descDesc I L) tt`
          # via the §6.6 conv rule: build `vDesc lev iTyVal` for a
          # candidate `lev` and ask conv whether it matches `dTy`. Conv
          # fires the symmetric `VDesc ↔ VMu` unfolding internally —
          # this is the same mechanism used at conv.nix:344-355. The
          # candidate-level scan is bounded by the prelude's maximum
          # description level (descriptions at L ≥ 4 are not exercised
          # by current prelude code; can extend if pathological cases
          # emerge).
          tryDescAtLevel = lev:
            if C.conv ctx.depth (V.vDesc lev iTyVal) dTy
            then lev else null;
          scanLevels = candidates:
            if candidates == [] then null
            else
              let
                lev = builtins.head candidates;
                hit = tryDescAtLevel lev;
              in if hit != null then hit
                 else scanLevels (builtins.tail candidates);
          # Common prelude levels in increasing order. L=0 is the
          # ⊤-slice; L=1 is descDesc itself; L=2/3 cover descriptions
          # of descriptions of descriptions and similar nesting.
          candidateLevels =
            let l0 = V.vLevelZero;
                l1 = V.vLevelSuc l0;
                l2 = V.vLevelSuc l1;
                l3 = V.vLevelSuc l2;
            in [ l0 l1 l2 l3 ];
        in
        if dTy.tag == "VDesc"
        then if !(C.conv ctx.depth dTy.I iTyVal)
             then send "typeError" {
               error = D.mkKernelError {
                 rule     = "checkDescAtAnyLevel";
                 msg      = "description index type mismatch";
                 expected = Q.quote ctx.depth iTyVal;
                 got      = Q.quote ctx.depth dTy.I;
               };
             }
             else pure { term = dResult.term; level = dTy.level; }
        else if dTy.tag == "VMu"
        then
          let matchedLev = scanLevels candidateLevels; in
          if matchedLev != null
          then pure { term = dResult.term; level = matchedLev; }
          else send "typeError" {
            error = D.mkKernelError {
              rule     = "checkDescAtAnyLevel";
              msg      = "encoded description type does not match expected index";
              expected = Q.quote ctx.depth iTyVal;
              got      = Q.quote ctx.depth dTy;
            };
          }
        else send "typeError" {
          error = D.mkKernelError {
            rule     = "checkDescAtAnyLevel";
            msg      = "expected description type";
            expected = { tag = "desc"; };
            got      = Q.quote ctx.depth dTy;
          };
        });
    checkTypeLevel = ctx: tm:
      let t = tm.tag; in
      if t == "nat" then pure { term = T.mkNat; level = V.vLevelZero; }
      else if t == "unit" then pure { term = T.mkUnit; level = V.vLevelZero; }
      else if t == "string" then pure { term = T.mkString; level = V.vLevelZero; }
      else if t == "int" then pure { term = T.mkInt; level = V.vLevelZero; }
      else if t == "float" then pure { term = T.mkFloat; level = V.vLevelZero; }
      else if t == "attrs" then pure { term = T.mkAttrs; level = V.vLevelZero; }
      else if t == "path" then pure { term = T.mkPath; level = V.vLevelZero; }
      else if t == "function" then pure { term = T.mkFunction; level = V.vLevelZero; }
      else if t == "any" then pure { term = T.mkAny; level = V.vLevelZero; }
      else if t == "level" then pure { term = T.mkLevel; level = V.vLevelZero; }
      else if t == "U" then
        # `U(k) : U(suc k)`. The level argument must itself be a Level
        # term; the check sub-delegation catches malformed levels with
        # a positioned error. The resulting universe level is the
        # evaluated `k` lifted by `suc`.
        bind (self.check ctx tm.level V.vLevel) (lTm:
          let lVal = E.eval ctx.env lTm; in
          pure { term = T.mkU lTm; level = V.vLevelSuc lVal; })
      else if t == "list" then
        bind (self.checkTypeLevel ctx tm.elem) (r:
          pure { term = T.mkList r.term; level = r.level; })
      else if t == "sum" then
        bind (self.checkTypeLevel ctx tm.left) (lr:
          bind (self.checkTypeLevel ctx tm.right) (rr:
            pure { term = T.mkSum lr.term rr.term;
                   level = vLevelMaxOpt lr.level rr.level; }))
      else if t == "pi" then
        bind (self.checkTypeLevel ctx tm.domain) (dr:
          let domVal = E.eval ctx.env dr.term;
              ctx' = self.extend ctx tm.name domVal;
          in bind (self.checkTypeLevel ctx' tm.codomain) (cr:
            pure { term = T.mkPi tm.name dr.term cr.term;
                   level = vLevelMaxOpt dr.level cr.level; }))
      else if t == "sigma" then
        bind (self.checkTypeLevel ctx tm.fst) (fr:
          let fstVal = E.eval ctx.env fr.term;
              ctx' = self.extend ctx tm.name fstVal;
          in bind (self.checkTypeLevel ctx' tm.snd) (sr:
            pure { term = T.mkSigma tm.name fr.term sr.term;
                   level = vLevelMaxOpt fr.level sr.level; }))
      else if t == "eq" then
        bind (self.checkTypeLevel ctx tm.type) (ar:
          let aVal = E.eval ctx.env ar.term; in
          bind (self.check ctx tm.lhs aVal) (lTm:
            bind (self.check ctx tm.rhs aVal) (rTm:
              pure { term = T.mkEq ar.term lTm rTm; level = ar.level; })))
      # `Squash A : U(l)` for `A : U(l)` — propositional truncation
      # preserves the universe level.
      else if t == "squash" then
        bind (self.checkTypeLevel ctx tm.A) (ar:
          pure { term = T.mkSquash ar.term; level = ar.level; })
      else if t == "desc" then
        # `desc^k I : U(suc k)` — I is a small type, k a level.
        let
          atLevel = kVal:
            bind (self.check ctx tm.I vU0) (iTm:
              pure { term = T.mkDesc tm.k iTm;
                     level = if tm.k.tag == "level-zero"
                             then vLevelSucZero
                             else V.vLevelSuc kVal; });
        in
          if tm.k.tag == "level-zero"
          then atLevel V.vLevelZero
          else bind (self.check ctx tm.k V.vLevel) (kTm:
            atLevel (E.eval ctx.env kTm))
      else if t == "mu" then
        # `μ I D i : U(max levelOf(I) levelOf(D))` where `I : U(kI)`,
        # `D : Desc^kD I`, `i : I`. The Tm carries I explicitly
        # (`T.mkMu I D i`), so the rule routes I through
        # `checkTypeLevel` (admitting any universe, not just U(0))
        # and D through `checkDescAtAnyLevel`, which dispatches on
        # D's tag: canonical introduction forms (`desc-ret`/`-arg`/
        # `-rec`/`-pi`/`-plus`) take CHECK at the level-zero
        # soundness anchor — admitting check-only canonical leaves
        # (`tt`, `refl`) at index positions and using `levelOf` to
        # recover the actual level structurally; non-canonical D
        # (e.g. `app descDesc k : desc^(suc k) ⊤`) takes INFER, with
        # the inferred `VDesc.level` flowing directly into the μ
        # result. The result level is `vLevelMaxOpt iLev dLev`.
        bind (self.checkTypeLevel ctx tm.I) (iResult:
          let iTyTm = iResult.term;
              iLev = iResult.level;
              iTyVal = E.eval ctx.env iTyTm; in
          bind (self.checkDescAtAnyLevel ctx tm.D iTyVal) (dInfo:
            bind (self.check ctx tm.i iTyVal) (iTm:
              pure { term = T.mkMu iTyTm dInfo.term iTm;
                     level = vLevelMaxOpt iLev dInfo.level; })))
      else if t == "let" then
        # `let x : A = v in body` as a type: A a type, v : A, body a type
        # in the extended context. The level is the body's level, since
        # `let` is resolved by substitution (the body is evaluated under
        # `env` prefixed by `vVal`). Routing `let` through CHECK keeps
        # `body` eligible for the check-only leaves (`tt`, `refl`, and
        # eliminators like `desc-ind` whose scrutinee uses canonical
        # leaves) that are accepted only under a known target type.
        bind (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
          bind (self.check ctx tm.val aVal) (vTm:
            let
              vVal = E.eval ctx.env vTm;
              ctx' = {
                env = [ vVal ] ++ ctx.env;
                types = [ aVal ] ++ ctx.types;
                depth = ctx.depth + 1;
              };
            in bind (self.checkTypeLevel ctx' tm.body) (r:
              pure { term = T.mkLet tm.name aTm vTm r.term; level = r.level; })))
      # Fallback: infer and check it's a universe, extract level.
      else
        bind (self.infer ctx tm) (result:
          if result.type.tag == "VU"
          then pure { term = result.term; level = result.type.level; }
          else send "typeError" {
            error = D.mkKernelError {
              rule     = "checkTypeLevel";
              msg      = "expected a type (universe)";
              expected = { tag = "U"; };
              got      = Q.quote ctx.depth result.type;
            };
          });

    checkType = ctx: tm:
      bind (self.checkTypeLevel ctx tm) (r: pure r.term);
  };
  tests = {};
}
