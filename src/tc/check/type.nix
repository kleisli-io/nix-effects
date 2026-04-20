# Type formation (§7.5, §8.2).
#
# `checkTypeLevel : Ctx → Tm → Computation { term; level; }` verifies
# that `tm` is a type and returns both the elaborated term and the
# universe level it inhabits. Levels come from the typing derivation,
# not post-hoc value inspection: e.g., `Π(x:A). B` computes its level
# as the max of domain/codomain levels in context. The fallback path
# delegates to `infer` and succeeds iff the inferred type is a
# universe.
#
# `checkType` is the thin wrapper that forgets the level.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  Q = fx.tc.quote;

  K = fx.kernel;
  pure = K.pure;
  send = K.send;
  bind = K.bind;

  typeError = msg: expected: got: term:
    send "typeError" { inherit msg expected got term; };
in {
  scope = {
    checkTypeLevel = ctx: tm:
      let t = tm.tag; in
      if t == "nat" then pure { term = T.mkNat; level = 0; }
      else if t == "bool" then pure { term = T.mkBool; level = 0; }
      else if t == "unit" then pure { term = T.mkUnit; level = 0; }
      else if t == "void" then pure { term = T.mkVoid; level = 0; }
      else if t == "string" then pure { term = T.mkString; level = 0; }
      else if t == "int" then pure { term = T.mkInt; level = 0; }
      else if t == "float" then pure { term = T.mkFloat; level = 0; }
      else if t == "attrs" then pure { term = T.mkAttrs; level = 0; }
      else if t == "path" then pure { term = T.mkPath; level = 0; }
      else if t == "function" then pure { term = T.mkFunction; level = 0; }
      else if t == "any" then pure { term = T.mkAny; level = 0; }
      else if t == "U" then pure { term = tm; level = tm.level + 1; }
      else if t == "list" then
        bind (self.checkTypeLevel ctx tm.elem) (r:
          pure { term = T.mkList r.term; level = r.level; })
      else if t == "sum" then
        bind (self.checkTypeLevel ctx tm.left) (lr:
          bind (self.checkTypeLevel ctx tm.right) (rr:
            let lvl = if lr.level >= rr.level then lr.level else rr.level;
            in pure { term = T.mkSum lr.term rr.term; level = lvl; }))
      else if t == "pi" then
        bind (self.checkTypeLevel ctx tm.domain) (dr:
          let domVal = E.eval ctx.env dr.term;
              ctx' = self.extend ctx tm.name domVal;
          in bind (self.checkTypeLevel ctx' tm.codomain) (cr:
            let lvl = if dr.level >= cr.level then dr.level else cr.level;
            in pure { term = T.mkPi tm.name dr.term cr.term; level = lvl; }))
      else if t == "sigma" then
        bind (self.checkTypeLevel ctx tm.fst) (fr:
          let fstVal = E.eval ctx.env fr.term;
              ctx' = self.extend ctx tm.name fstVal;
          in bind (self.checkTypeLevel ctx' tm.snd) (sr:
            let lvl = if fr.level >= sr.level then fr.level else sr.level;
            in pure { term = T.mkSigma tm.name fr.term sr.term; level = lvl; }))
      else if t == "eq" then
        bind (self.checkTypeLevel ctx tm.type) (ar:
          let aVal = E.eval ctx.env ar.term; in
          bind (self.check ctx tm.lhs aVal) (lTm:
            bind (self.check ctx tm.rhs aVal) (rTm:
              pure { term = T.mkEq ar.term lTm rTm; level = ar.level; })))
      else if t == "desc" then
        # `desc I : U(1)` — I is a small type.
        bind (self.check ctx tm.I (V.vU 0)) (iTm:
          pure { term = T.mkDesc iTm; level = 1; })
      else if t == "mu" then
        # `μ I D i : U(0)` where `I : U(0)`, `D : Desc I`, `i : I`. The
        # Tm carries I explicitly (`T.mkMu I D i`), so the rule checks
        # I directly rather than recovering it from `infer tm.D`. This
        # routes D through `check.nix`'s desc-ret/-arg/-rec/-pi CHECK
        # rules, which accept check-only canonical leaves (`tt`, `refl`,
        # `pair`) at index positions — a bare `retI ttPrim` is a
        # well-formed `Desc unit` but non-inferable, because the kernel
        # has no `tt` infer rule. Removing the redundant `infer tm.D`
        # here eliminates the cascade to the catch-all at
        # `infer.nix:418`.
        bind (self.check ctx tm.I (V.vU 0)) (iTyTm:
          let iTyVal = E.eval ctx.env iTyTm; in
          bind (self.check ctx tm.D (V.vDesc iTyVal)) (dTm:
            bind (self.check ctx tm.i iTyVal) (iTm:
              pure { term = T.mkMu iTyTm dTm iTm; level = 0; })))
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
          else typeError "expected a type (universe)" { tag = "U"; }
            (Q.quote ctx.depth result.type) tm);

    checkType = ctx: tm:
      bind (self.checkTypeLevel ctx tm) (r: pure r.term);
  };
  tests = {};
}
