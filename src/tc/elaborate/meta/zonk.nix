# Tm-side metavariable substitution. Counterpart of forceMeta
# (Val-side, ./context.nix:73).
{ self, fx, api, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  # mkMeta / quote live at elaborate scope, not meta-dir self.
  M = fx.tc.elaborate.meta;

  ok = v: { value = v; };
  err = e: { error = e; };

  # Sub-field values are left as thunks so the caller's stack depth is
  # constant; recursion fires only on consumer field access.
  rebuildFields = depth: state: tm: spec:
    let
      addField = acc: f: acc // {
        ${f.name} = lazyZonk (depth + f.under) state tm.${f.name};
      };
    in tm // (builtins.foldl' addField { } spec);

  rebuildDescRef = depth: state: ref:
    ref // {
      I = lazyZonk depth state ref.I;
      level = lazyZonk depth state ref.level;
    } // (if ref ? params
          then { params = map (lazyZonk depth state) ref.params; }
          else { });

  withDescRef = depth: state: tm:
    if tm ? _descRef
    then tm // { _descRef = rebuildDescRef depth state tm._descRef; }
    else tm;

  # Precondition: state.delta has no Hole entries (pre-scanned by
  # zonkTm). Reaching one here is an invariant violation.
  lazyZonk = depth: state: tm:
    if !(builtins.isAttrs tm) then tm
    else if !(tm ? tag) then tm
    else
      let t = tm.tag; in

      if t == "meta" then
        let entry = self.lookupMeta state tm.id; in
        if entry == null
        then throw "tc.elaborate.meta.zonk: meta ${toString tm.id} not registered in state"
        else if self.isHole entry
        then throw "tc.elaborate.meta.zonk: unsolved meta ${toString tm.id} reached during lazy zonk — pre-scan invariant violated"
        else lazyZonk depth state (M.quote depth entry.tm)

      else if t == "var"
           || t == "unit" || t == "tt" || t == "empty"
           || t == "boot-refl" || t == "funext"
           || t == "level" || t == "level-zero"
           || t == "string" || t == "int" || t == "float"
           || t == "attrs" || t == "path" || t == "derivation"
           || t == "function" || t == "any"
           || t == "string-lit" || t == "int-lit" || t == "float-lit"
           || t == "attrs-lit" || t == "path-lit" || t == "derivation-lit"
           || t == "fn-lit" || t == "any-lit"
           || t == "lit-val"
      then tm

      else if t == "let" then rebuildFields depth state tm [
        { name = "type"; under = 0; }
        { name = "val";  under = 0; }
        { name = "body"; under = 1; }
      ]
      else if t == "ann" then
        rebuildFields depth state (withDescRef depth state tm) [
          { name = "term"; under = 0; }
          { name = "type"; under = 0; }
        ]
      else if t == "pi" then rebuildFields depth state tm [
        { name = "domain";   under = 0; }
        { name = "codomain"; under = 1; }
      ]
      else if t == "lam" then rebuildFields depth state tm [
        { name = "domain"; under = 0; }
        { name = "body";   under = 1; }
      ]
      else if t == "app" then rebuildFields depth state tm [
        { name = "fn";  under = 0; }
        { name = "arg"; under = 0; }
      ]
      else if t == "sigma" then rebuildFields depth state tm [
        { name = "fst"; under = 0; }
        { name = "snd"; under = 1; }
      ]
      else if t == "pair" then rebuildFields depth state tm [
        { name = "fst"; under = 0; }
        { name = "snd"; under = 0; }
      ]
      else if t == "fst" then rebuildFields depth state tm [
        { name = "pair"; under = 0; }
      ]
      else if t == "snd" then rebuildFields depth state tm [
        { name = "pair"; under = 0; }
      ]

      else if t == "absurd" then rebuildFields depth state tm [
        { name = "type"; under = 0; }
        { name = "term"; under = 0; }
      ]
      else if t == "boot-sum" then rebuildFields depth state tm [
        { name = "left";  under = 0; }
        { name = "right"; under = 0; }
      ]
      else if t == "boot-inl" || t == "boot-inr" then rebuildFields depth state tm [
        { name = "left";  under = 0; }
        { name = "right"; under = 0; }
        { name = "term";  under = 0; }
      ]
      else if t == "boot-sum-elim" then rebuildFields depth state tm [
        { name = "left";    under = 0; }
        { name = "right";   under = 0; }
        { name = "motive";  under = 0; }
        { name = "onLeft";  under = 0; }
        { name = "onRight"; under = 0; }
        { name = "scrut";   under = 0; }
      ]
      else if t == "boot-eq" then rebuildFields depth state tm [
        { name = "type"; under = 0; }
        { name = "lhs";  under = 0; }
        { name = "rhs";  under = 0; }
      ]
      else if t == "boot-j" then rebuildFields depth state tm [
        { name = "type";   under = 0; }
        { name = "lhs";    under = 0; }
        { name = "motive"; under = 0; }
        { name = "base";   under = 0; }
        { name = "rhs";    under = 0; }
        { name = "eq";     under = 0; }
      ]
      else if t == "squash" then rebuildFields depth state tm [
        { name = "A"; under = 0; }
      ]
      else if t == "squash-intro" then rebuildFields depth state tm [
        { name = "a"; under = 0; }
      ]
      else if t == "squash-elim" then rebuildFields depth state tm [
        { name = "A"; under = 0; }
        { name = "B"; under = 0; }
        { name = "f"; under = 0; }
        { name = "x"; under = 0; }
      ]
      else if t == "desc" then rebuildFields depth state tm [
        { name = "iLev"; under = 0; }
        { name = "k";    under = 0; }
        { name = "I";    under = 0; }
      ]
      else if t == "mu" then rebuildFields depth state tm [
        { name = "I"; under = 0; }
        { name = "D"; under = 0; }
        { name = "i"; under = 0; }
      ]
      else if t == "desc-con" then rebuildFields depth state tm [
        { name = "D"; under = 0; }
        { name = "i"; under = 0; }
        { name = "d"; under = 0; }
      ]
      else if t == "desc-ind" then rebuildFields depth state tm [
        { name = "D";      under = 0; }
        { name = "motive"; under = 0; }
        { name = "step";   under = 0; }
        { name = "i";      under = 0; }
        { name = "scrut";  under = 0; }
      ]
      else if t == "desc-desc-app" then rebuildFields depth state tm [
        { name = "iLev"; under = 0; }
        { name = "I";    under = 0; }
        { name = "L";    under = 0; }
      ]
      else if t == "canon-app" then
        tm // {
          params = map (lazyZonk depth state) tm.params;
          body = lazyZonk depth state tm.body;
        }
      else if t == "interp-d" then rebuildFields depth state tm [
        { name = "level"; under = 0; }
        { name = "I";     under = 0; }
        { name = "D";     under = 0; }
        { name = "X";     under = 0; }
        { name = "i";     under = 0; }
      ]
      else if t == "all-d" then rebuildFields depth state tm [
        { name = "level"; under = 0; }
        { name = "I";     under = 0; }
        { name = "D";     under = 0; }
        { name = "K";     under = 0; }
        { name = "X";     under = 0; }
        { name = "M";     under = 0; }
        { name = "i";     under = 0; }
        { name = "d";     under = 0; }
      ]
      else if t == "everywhere-d" then rebuildFields depth state tm [
        { name = "level"; under = 0; }
        { name = "I";     under = 0; }
        { name = "D";     under = 0; }
        { name = "K";     under = 0; }
        { name = "X";     under = 0; }
        { name = "M";     under = 0; }
        { name = "ih";    under = 0; }
        { name = "i";     under = 0; }
        { name = "d";     under = 0; }
      ]
      else if t == "lift" then rebuildFields depth state tm [
        { name = "l";  under = 0; }
        { name = "m";  under = 0; }
        { name = "eq"; under = 0; }
        { name = "A";  under = 0; }
      ]
      else if t == "lift-intro" then rebuildFields depth state tm [
        { name = "l";  under = 0; }
        { name = "m";  under = 0; }
        { name = "eq"; under = 0; }
        { name = "A";  under = 0; }
        { name = "a";  under = 0; }
      ]
      else if t == "lift-elim" then rebuildFields depth state tm [
        { name = "l";  under = 0; }
        { name = "m";  under = 0; }
        { name = "eq"; under = 0; }
        { name = "A";  under = 0; }
        { name = "x";  under = 0; }
      ]
      else if t == "level-suc" then rebuildFields depth state tm [
        { name = "pred"; under = 0; }
      ]
      else if t == "level-max" then rebuildFields depth state tm [
        { name = "lhs"; under = 0; }
        { name = "rhs"; under = 0; }
      ]
      else if t == "U" then rebuildFields depth state tm [
        { name = "level"; under = 0; }
      ]
      else if t == "str-eq" then rebuildFields depth state tm [
        { name = "lhs"; under = 0; }
        { name = "rhs"; under = 0; }
      ]
      else if t == "opaque-lam" then rebuildFields depth state tm [
        { name = "piTy"; under = 0; }
      ]

      else throw "tc.elaborate.meta.zonk: unhandled Tm tag '${t}'";

  findFirstHole = state:
    let
      go = ids:
        if ids == [ ] then null
        else
          let entry = state.delta.${builtins.head ids}; in
          if self.isHole entry then entry else go (builtins.tail ids);
    in go (builtins.attrNames state.delta);

  zonkTm = depth: state: tm:
    let hole = findFirstHole state; in
    if hole != null
    then err {
      tag = "unsolved-meta";
      id = hole.id;
      ctx = (hole.type or { }).ctx or null;
    }
    else ok (lazyZonk depth state tm);

  emptyState = {
    delta = { };
    constraints = [ ];
    mentions = { };
    metaOrder = [ ];
    nextMetaId = 0;
    nextConstraintId = 0;
  };

  deepPiCascade = n:
    builtins.foldl'
      (acc: _: T.mkPi "_" T.mkTt acc)
      T.mkTt
      (builtins.genList (i: i) n);
in
{
  scope = {
    zonkTm = api.leaf {
      value = zonkTm;
      description = "zonkTm depth state tm: substitute solved metas in `tm`. Returns `{ error = { unsolved-meta; id; ctx; } }` if any `Hole` is in `state.delta`; else `{ value = tm' }` with thunked sub-fields (stack-safe, forcing deferred to consumer access).";
      signature = "zonkTm : Depth -> ElabState -> Tm -> Result Tm";
      tests = {
        "zonk-leaf-tt" = {
          expr = (zonkTm 0 { delta = { }; } T.mkTt).value.tag;
          expected = "tt";
        };
        "zonk-unsolved-meta-errors" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkHole 0 ty; }; };
              tm = M.mkMeta 0 [ ];
              r = zonkTm 0 state tm;
            in r.error.tag or "no-error";
          expected = "unsolved-meta";
        };
        "zonk-unsolved-meta-error-id" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "7" = self.mkHole 7 ty; }; };
              tm = M.mkMeta 7 [ ];
              r = zonkTm 0 state tm;
            in r.error.id or null;
          expected = 7;
        };
        "zonk-solved-meta-substitutes" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkSolved 0 V.vTt ty; }; };
              tm = M.mkMeta 0 [ ];
              r = zonkTm 0 state tm;
            in r.value.tag or "error";
          expected = "tt";
        };
        "zonk-app-recurses-into-args" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkSolved 0 V.vTt ty; }; };
              meta = M.mkMeta 0 [ ];
              tm = T.mkApp T.mkTt meta;
              r = zonkTm 0 state tm;
            in r.value.arg.tag or "error";
          expected = "tt";
        };
        "zonk-app-keeps-fn" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkSolved 0 V.vTt ty; }; };
              meta = M.mkMeta 0 [ ];
              tm = T.mkApp T.mkTt meta;
              r = zonkTm 0 state tm;
            in r.value.fn.tag or "error";
          expected = "tt";
        };
        "zonk-unsolved-propagates-through-app" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkHole 0 ty; }; };
              meta = M.mkMeta 0 [ ];
              tm = T.mkApp T.mkTt meta;
              r = zonkTm 0 state tm;
            in r.error.tag or "no-error";
          expected = "unsolved-meta";
        };
        "zonk-pi-recurses-under-binder" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkSolved 0 V.vUnit ty; }; };
              meta = M.mkMeta 0 [ ];
              tm = T.mkPi "x" meta T.mkTt;
              r = zonkTm 0 state tm;
            in r.value.domain.tag or "error";
          expected = "unit";
        };
        "zonk-leaves-non-meta-app-unchanged" = {
          expr =
            let
              state = { delta = { }; };
              tm = T.mkApp T.mkTt T.mkTt;
              r = zonkTm 0 state tm;
            in r.value.tag;
          expected = "app";
        };
        "zonk-stack-safe-5000-pi-cascade-tag" = {
          expr = (zonkTm 0 emptyState (deepPiCascade 5000)).value.tag;
          expected = "pi";
        };
        # Probe lazy-zonk field access on a real elaborator output.
        # Post-implicit-migration `H.inl` is a poly-ctor with implicit
        # type args; bare `H.elab (H.inl H.tt)` leaves `?A`/`?B` unsolved
        # and throws. `H.checkHoas` supplies the expected sum type so
        # all metas resolve; the result is a meta-free `desc-con` Tm.
        "zonk-stack-safe-h-inl-tt-tag" = {
          expr = (zonkTm 0 emptyState (fx.tc.hoas.checkHoas
            (fx.tc.hoas.sum fx.tc.hoas.unit fx.tc.hoas.unit)
            (fx.tc.hoas.inl fx.tc.hoas.tt))).value.tag;
          expected = "desc-con";
        };
        "zonk-stack-safe-h-inl-tt-d-tag" = {
          expr = (zonkTm 0 emptyState (fx.tc.hoas.checkHoas
            (fx.tc.hoas.sum fx.tc.hoas.unit fx.tc.hoas.unit)
            (fx.tc.hoas.inl fx.tc.hoas.tt))).value.d.tag;
          expected = "boot-inl";
        };
        "zonk-stack-safe-h-inl-tt-d-term-tag" = {
          expr = (zonkTm 0 emptyState (fx.tc.hoas.checkHoas
            (fx.tc.hoas.sum fx.tc.hoas.unit fx.tc.hoas.unit)
            (fx.tc.hoas.inl fx.tc.hoas.tt))).value.d.term.tag;
          expected = "pair";
        };
      };
    };
  };
}
