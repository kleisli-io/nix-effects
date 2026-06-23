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
{ self, fx, api, ... }:

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
  yield = self._yield.wrap;

  D = fx.diag.error;

  # Shared `U(0)` value — every small-type sort check targets this.
  vU0 = V.vU V.vLevelZero;

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

  # Entry-yield budget for non-leaf `checkTypeLevel` heads — same
  # discipline and soundness argument as `check.nix` (see the table
  # there). Budgeting this helper removes the segment break its
  # per-entry yields used to provide, so it must divide its grant
  # through its own fanout table: the recursive invariant (Σ child
  # budgets ≤ b − 1 at every budgeted entry) then bounds un-yielded
  # entries per native segment by `entryBudget` across `check`/`infer`/
  # `checkTypeLevel` mixtures. Fanout = max number of checker
  # sub-computations any branch of that tag's arm starts. The fallback
  # arm's only sub-computation is one `infer`, so the default is 1.
  # `checkDescAtAnyLevel` is budgeted as a fanout-2 head at its own
  # definition; the Σ-child-budgets invariant covers `mu`'s third child.
  entryBudget = 64;
  entryFanout = {
    "U" = 1;
    "boot-sum" = 2;
    "pi" = 2;
    "sigma" = 2;
    "boot-eq" = 3;
    "squash" = 1;
    "desc" = 2;
    "mu" = 3;
    "let" = 3;
  };

in
{
  scope = {
    checkDescAtAnyLevel = api.leaf {
      description = "checkDescAtAnyLevel: description checking at any universe level — accepts both primitive `VDesc` results and encoded `VMu` descriptions (the `VDesc ↔ μ_⊤(descDesc I L)` correspondence) and threads the universe level back to the caller for downstream encoding decisions.";
      signature = "checkDescAtAnyLevel : Ctx -> Tm -> Val -> Computation { term; level }";
      doc = ''
        Trusted-annotation fast path: when `dTm` is a `T.mkAnnTrusted`
        with a complete `_descRef`, build a canonical description term
        directly (skipping the unfolding scan) and reuse the carried
        level. Otherwise fall through to inference and dispatch on the
        inferred type's tag:

        - `VDesc`: the level is already on the type; conv-check that the
          index type matches `iTyVal` and forward.
        - `VMu`: the description is encoded — scan a bounded list of
          candidate universe levels (the prelude exercises `L = 0..3`)
          and ask `conv` whether `V.vDesc lev iTyVal` unifies with the
          inferred type. Conv fires the symmetric `VDesc ↔ VMu`
          unfolding internally (same mechanism as
          `conv.nix:344-355`).
        - Anything else: emit a `typeError` — not a description.

        Used by `desc-con` checking (`check.nix`) for `_descConCert`
        validation, by `infer.nix` for `desc-ind` motive and branch
        checking, and by `type.nix:mu` to thread the description level
        into the `μ` type's universe level.
      '';
      # Strategy: a primitive `VDesc` result carries its level directly.
      # An encoded description has type `VMu Unit (descDescAt iLev I k)
      # tt`; recover `iLev/I/k` only from that canonical stamp.
      value = ctx0: dTm: iTyVal:
        # Budgeted like a fanout-2 `check` head (cf. `checkMotive`): a
        # budget-left entry skips its head yield so trusted-description
        # validation threads the bindP fast path; an exhausted or
        # budget-less entry yields, resetting the window. Each branch
        # starts at most two sequential checker children (e.g. the index
        # check plus the canonical-term build), so Σ child budgets
        # ≤ b − 1. The param-list walk below keeps its own head-yield
        # (unbounded width).
        let
          b = ctx0.eb or 0;
          ctx = ctx0 // { eb = ((if b > 0 then b else entryBudget) - 1) / 2; };
          body =
            let
          checkInferredDesc = dResult:
            let
              dTy = dResult.type;
              descDescRef =
                if dTy.tag == "VMu"
                  && builtins.isAttrs dTy.D
                  && dTy.D ? _canonRef
                  && (dTy.D._canonRef.id or null) == "descDesc"
                then dTy.D._canonRef
                else null;
              refParams =
                if descDescRef == null || !(descDescRef ? params)
                  || builtins.length descDescRef.params != 3
                then null
                else descDescRef.params;
              refI =
                if refParams == null || builtins.length refParams < 3
                then null
                else builtins.elemAt refParams 1;
              refLevel =
                if refParams == null || builtins.length refParams < 3
                then null
                else builtins.elemAt refParams 2;
              encodedRefLevel =
                if refI != null
                  && refLevel != null
                  && C.conv ctx.depth dTy.I V.vUnit
                  && C.conv ctx.depth dTy.i V.vTt
                  && C.conv ctx.depth refI iTyVal
                then refLevel
                else null;
            in
            if dTy.tag == "VDesc"
            then if !(C.conv ctx.depth dTy.I iTyVal)
            then
              send "typeError"
                {
                  error = D.mkKernelError {
                    rule = "checkDescAtAnyLevel";
                    msg = "description index type mismatch";
                    expected = Q.quote ctx.depth iTyVal;
                    got = Q.quote ctx.depth dTy.I;
                    term = { tag = dTm.tag; };
                    frame = D.captureFrame ctx;
                  };
                }
            else pure { term = dResult.term; level = dTy.level; }
            else if dTy.tag == "VMu"
            then
              if encodedRefLevel != null
              then pure { term = dResult.term; level = encodedRefLevel; }
              else
                send "typeError" {
                  error = D.mkKernelError {
                    rule = "checkDescAtAnyLevel";
                    msg = "encoded description type does not match expected index";
                    expected = Q.quote ctx.depth iTyVal;
                    got = Q.quote ctx.depth dTy;
                    term = { tag = dTm.tag; };
                    frame = D.captureFrame ctx;
                  };
                }
            else
              send "typeError" {
                error = D.mkKernelError {
                  rule = "checkDescAtAnyLevel";
                  msg = "expected description type";
                  expected = { tag = "desc"; };
                  got = Q.quote ctx.depth dTy;
                  term = { tag = dTm.tag; };
                  frame = D.captureFrame ctx;
                };
              };
          inferDesc = bind (self.infer ctx dTm) checkInferredDesc;
          inferParamTerms = params:
            # Head-yield: defers the list walk so a run of pure-leaf params
            # can't cascade at width.
            yield (if params == [ ] then pure [ ]
            else
              bind (self.infer ctx (builtins.head params)) (pResult:
                bind (inferParamTerms (builtins.tail params)) (rest:
                  pure ([ pResult.term ] ++ rest))));
          hasCompleteDescRef = tm:
            tm ? _descRef
            && (tm._descRef.kind or null) == "datatype-desc"
            && (tm._descRef.signature.complete or false);
          generatedParamTerm = tm:
            let t = tm.tag or null; in
            # `params` reaching here are `inferParamTerms` outputs: `self.infer`
            # has already checked each non-trusted `ann` body against its kind
            # annotation, and trusted anns are correct by construction. A
            # kind-validated `ann` param is therefore safe to trust without
            # re-materializing the generated description body.
            if t == "ann" then true
            else if t == "mu" then hasCompleteDescRef tm.D
            else if t == "desc-con" then hasCompleteDescRef tm.D
            else t == "unit" || t == "string" || t == "int"
              || t == "float" || t == "attrs" || t == "path"
              || t == "function" || t == "any" || t == "level"
              || t == "U" || t == "tt" || t == "level-zero"
              || t == "level-suc" || t == "level-max"
              || t == "var";
          canonicalTrustedDescTerm = kVal:
            bind (inferParamTerms (dTm._descRef.params or [ ])) (params:
              let
                descTyTm = T.mkDesc (Q.quote ctx.depth kVal) (Q.quote ctx.depth iTyVal);
                ref = dTm._descRef // {
                  I = Q.quote ctx.depth iTyVal;
                  level = Q.quote ctx.depth kVal;
                  inherit params;
                };
                certifiedGeneratedDesc =
                  (dTm._descRef.kind or null) == "datatype-desc"
                  && (dTm._descRef.signature.complete or false)
                  && builtins.all generatedParamTerm params;
                bodyComp =
                  if certifiedGeneratedDesc
                  then pure dTm.term
                  else self.check ctx dTm.term (V.vDesc kVal iTyVal);
              in
              bind bodyComp (bodyTm:
                pure (T.mkAnnTrustedWithDescRef bodyTm descTyTm ref)));
        in
        if dTm.tag == "ann"
          && (dTm.trusted or false)
          && dTm.type.tag == "desc"
          && (dTm ? _descRef)
        then
          let
            iTm = dTm.type.I;
            iVal = E.eval ctx.env iTm;
            kTm = dTm.type.k;
            kVal =
              if kTm.tag == "level-zero"
              then V.vLevelZero
              else E.eval ctx.env kTm;
          in
          if C.conv ctx.depth iVal iTyVal
          then
            bind (canonicalTrustedDescTerm kVal)
              (term:
                pure { inherit term; level = kVal; })
          else
            bind (self.check ctx iTm vU0) (iCheckedTm:
              let iCheckedVal = E.eval ctx.env iCheckedTm; in
              if C.conv ctx.depth iCheckedVal iTyVal
              then
                bind (canonicalTrustedDescTerm kVal)
                  (term:
                    pure { inherit term; level = kVal; })
              else inferDesc)
        else inferDesc;
        in
        if b > 0 then body else yield body;
    };

    checkTypeLevel = api.leaf {
      description = "checkTypeLevel: type-formation judgement — verifies that `tm` is a type and returns both the elaborated term and the universe Level value it inhabits.";
      signature = "checkTypeLevel : Ctx -> Tm -> Computation { term; level }";
      doc = ''
        `level` is a kernel Level *value* (`V.vLevelZero`,
        `V.vLevelSuc`, `V.vLevelMax`) — not a Nix integer — so
        level-polymorphic types (`U(k)` for a variable `k : Level`)
        flow through without ad-hoc integer machinery. Levels come
        from the typing derivation, not post-hoc value inspection
        (e.g., `Π(x:A). B` computes its level as the `vLevelMax` of
        domain/codomain levels). The fallback path delegates to
        `infer` and succeeds iff the inferred type is a universe; in
        that case `.type.level` is already a Level value and is
        forwarded verbatim.
      '';
      value = ctx0: tm:
        let
          t = tm.tag;
          # Leaf tags: arm is `pure { …; level = vLevelZero }`. Left
          # un-yielded for the bindP fast path. Every recursive type-former
          # (U, pi, sigma, …) is excluded → budgeted like `check`/`infer`
          # heads; an exhausted entry yields → flat descent (flips ckPi).
          isLeaf = builtins.elem t [
            "unit" "string" "int" "float" "attrs" "path" "function" "any" "level"
          ];
          b = ctx0.eb or 0;
          fan = entryFanout.${t} or 1;
          childEb =
            if fan == 0 then 0
            else ((if b > 0 then b else entryBudget) - 1) / fan;
          ctx = if isLeaf || childEb == b then ctx0 else ctx0 // { eb = childEb; };
          body =
            if t == "unit" then pure { term = T.mkUnit; level = V.vLevelZero; }
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
          bind (self.check ctx tm.level V.vLevel)
            (lTm:
              let lVal = E.eval ctx.env lTm; in
              pure { term = T.mkU lTm; level = V.vLevelSuc lVal; })
        else if t == "boot-sum" then
          bind (self.checkTypeLevel ctx tm.left)
            (lr:
              bind (self.checkTypeLevel ctx tm.right) (rr:
                pure {
                  term = T.mkBootSum lr.term rr.term;
                  level = vLevelMaxOpt lr.level rr.level;
                }))
        else if t == "pi" then
          bind (self.checkTypeLevel ctx tm.domain)
            (dr:
              let
                domVal = E.eval ctx.env dr.term;
                ctx' = self.extend ctx tm.name domVal;
              in
              bind (self.checkTypeLevel ctx' tm.codomain) (cr:
                pure {
                  # Carry forward the `_plicity` sidecar so the elaborator
                  # overlay can still observe implicit binders on a Pi that
                  # has round-tripped through the kernel type-formation
                  # judgement. Plicity is opaque metadata to the kernel
                  # rules (eval/core.nix already preserves it on values);
                  # without this line `inferTm` on an `ann _ ({A:U}→...)`
                  # produces a plicity-stripped VPi and `insertImplicits`
                  # cannot peel.
                  term = (T.mkPi tm.name dr.term cr.term)
                    // (if tm ? _plicity then { _plicity = tm._plicity; } else { });
                  level = vLevelMaxOpt dr.level cr.level;
                }))
        else if t == "sigma" then
          bind (self.checkTypeLevel ctx tm.fst)
            (fr:
              let
                fstVal = E.eval ctx.env fr.term;
                ctx' = self.extend ctx tm.name fstVal;
              in
              bind (self.checkTypeLevel ctx' tm.snd) (sr:
                pure {
                  term = T.mkSigma tm.name fr.term sr.term;
                  level = vLevelMaxOpt fr.level sr.level;
                }))
        else if t == "boot-eq" then
          bind (self.checkTypeLevel ctx tm.type)
            (ar:
              let aVal = E.eval ctx.env ar.term; in
              bind (self.check ctx tm.lhs aVal) (lTm:
                bind (self.check ctx tm.rhs aVal) (rTm:
                  pure { term = T.mkBootEq ar.term lTm rTm; level = ar.level; })))
        # `Squash A : U(l)` for `A : U(l)` — propositional truncation
        # preserves the universe level.
        else if t == "squash" then
          bind (self.checkTypeLevel ctx tm.A)
            (ar:
              pure { term = T.mkSquash ar.term; level = ar.level; })
        else if t == "desc" then
        # `desc^k I : U(suc (max k iLev))` for `I : U(iLev)`. Emit
        # `mkDescAt` carrying the synthesised `iLev` so eval/conv can
        # recover it without re-running `checkTypeLevel`; at `iLev=0`
        # the level-zero `mkDesc` convenience form emits the same slot.
          let
            atLevel = kVal:
              bind (self.checkTypeLevel ctx tm.I) (iResult:
                pure {
                  term = T.mkDescAt
                    (Q.quote ctx.depth iResult.level)
                    tm.k
                    iResult.term;
                  level = V.vLevelSuc (vLevelMaxOpt kVal iResult.level);
                });
          in
          if tm.k.tag == "level-zero"
          then atLevel V.vLevelZero
          else
            bind (self.check ctx tm.k V.vLevel) (kTm:
              atLevel (E.eval ctx.env kTm))
        else if t == "mu" then
        # `μ I D i : U(max levelOf(I) levelOf(D))`. I is explicit, so
        # route it through `checkTypeLevel`; D is inferred by
        # `checkDescAtAnyLevel`, which accepts primitive `VDesc` results
        # and encoded `VMu` descriptions via the Desc/descDesc conversion.
          bind (self.checkTypeLevel ctx tm.I)
            (iResult:
              let
                iTyTm = iResult.term;
                iLev = iResult.level;
                iTyVal = E.eval ctx.env iTyTm;
              in
              bind (self.checkDescAtAnyLevel ctx tm.D iTyVal) (dInfo:
                bind (self.check ctx tm.i iTyVal) (iTm:
                  pure {
                    term = T.mkMu iTyTm dInfo.term iTm;
                    level = vLevelMaxOpt iLev dInfo.level;
                  })))
        else if t == "let" then
        # `let x : A = v in body` as a type: A a type, v : A, body a type
        # in the extended context. The level is the body's level, since
        # `let` is resolved by substitution (the body is evaluated under
        # `env` prefixed by `vVal`). Routing `let` through CHECK keeps
        # `body` eligible for the check-only leaves (`tt`, `refl`, and
        # eliminators like `desc-ind` whose scrutinee uses canonical
        # leaves) that are accepted only under a known target type.
          bind (self.checkType ctx tm.type)
            (aTm:
              let aVal = E.eval ctx.env aTm; in
              bind (self.check ctx tm.val aVal) (vTm:
                let
                  vVal = E.eval ctx.env vTm;
                  d = ctx.depth + 1;
                  e = ctx.eb or 0;
                  ctx' = {
                    env = V.envCons vVal ctx.env;
                    types = V.envCons aVal ctx.types;
                    depth = d;
                    eb = e;
                  };
                in
                builtins.seq d (builtins.seq e
                  (bind (self.checkTypeLevel ctx' tm.body) (r:
                    pure { term = T.mkLet tm.name aTm vTm r.term; level = r.level; })))))
        # Fallback: infer and check it's a universe, extract level.
        else
          bind (self.infer ctx tm) (result:
            if result.type.tag == "VU"
            then pure { term = result.term; level = result.type.level; }
            else
              send "typeError" {
                error = D.mkKernelError {
                  rule = "checkTypeLevel";
                  msg = "expected a type (universe)";
                  expected = { tag = "U"; };
                  got = Q.quote ctx.depth result.type;
                  term = { tag = tm.tag; };
                  frame = D.captureFrame ctx;
                };
              });
        in
        if isLeaf then body
        else if b > 0 then body
        else yield body;
    };

    checkType = api.leaf {
      description = "checkType: thin wrapper around `checkTypeLevel` that discards the level — verifies `tm` is a type and returns the elaborated term only.";
      signature = "checkType : Ctx -> Tm -> Computation Tm";
      value = ctx: tm:
        bind (self.checkTypeLevel ctx tm) (r: pure r.term);
    };
  };

  tests = { };
}
