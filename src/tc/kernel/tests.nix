# Acceptance tests for the flat predicate-stack datum: universe synthesis, the
# well-typedness of the internalized functions, the base/refine equations for
# beta and decide, the derived El at the base and one refinement, the membership
# decoder, and the conv/quote round-trip guard.
{ self, fx, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  C = fx.tc.conv;
  Q = fx.tc.quote;

  inherit (self.ktype) P andB KType beta psi El betaFn decideFn ElFn betaTy decideTy elTy iota refine;
  inherit (self) decide;

  app = H.app;
  ev = h: E.eval [ ] (H.elab h);
  conv = a: b: C.conv 0 (ev a) (ev b);
  chk = ty: h: !((H.checkHoas ty h) ? error);

  # Universe level of a closed type term, as a Nix Int (counts VLevelSuc).
  levelInt = v:
    let go = acc: x:
      let tag = if x ? tag then x.tag else "?"; in
      if tag == "VLevelZero" then acc
      else if tag == "VLevelSuc" then go (acc + 1) x.pred
      else throw "kernel/tests: non-concrete level (${tag})";
    in go 0 v;
  uInfo = h:
    let inf = H.inferHoas h; in
    { tag = inf.type.tag; level = levelInt inf.type.level; };

  # A concrete base description, its carrier, a witness, and predicates over it.
  B = H.datatype "B" [ (H.con "tt0" [ ]) (H.con "ff0" [ ]) ];
  BoolDesc = B.D;
  A = H.mu BoolDesc H.tt;
  xWit = app B.tt0 H.tt;
  pTrue = H.lam "x" A (_: H.true_);
  pFalse = H.lam "x" A (_: H.false_);

  c0 = iota A;
  cT = refine c0 pTrue;
  cF = refine c0 pFalse;
  cTF = refine (refine c0 pTrue) pFalse;
in
{
  scope = { };
  tests = {
    # Universe synthesis: KType : U_1 (single universe, no per-refinement rise).
    "ktype-typechecks" = { expr = uInfo KType; expected = { tag = "VU"; level = 1; }; };

    # The internalized functions are well-typed closed kernel terms.
    "betaFn-checks" = { expr = chk betaTy betaFn; expected = true; };
    "decideFn-checks" = { expr = chk decideTy decideFn; expected = true; };
    "elFn-checks" = { expr = chk elTy ElFn; expected = true; };

    # P (the membership decoder) and andB.
    "p-true-conv-unit" = { expr = conv (P H.true_) H.unit; expected = true; };
    "p-false-conv-void" = { expr = conv (P H.false_) H.void; expected = true; };
    "andB-tt" = { expr = conv (andB H.true_ H.true_) H.true_; expected = true; };
    "andB-tf" = { expr = conv (andB H.true_ H.false_) H.false_; expected = true; };

    # beta is the base carrier, constant along refinement.
    "beta-iota-conv-mu" = { expr = conv (beta c0) A; expected = true; };
    "beta-refine-conv-mu" = { expr = conv (beta cTF) A; expected = true; };

    # El_0(iota D) ~= Sigma x:mu D. Unit (empty stack decides true; P true ~> Unit).
    # Sigma-with-Unit-codomain does NOT eta-collapse to mu D under conv.
    "el-iota-conv-sigma-unit" = {
      expr = conv (El c0) (H.sigma "x" A (_: H.unit));
      expected = true;
    };
    "el-no-eta-collapse" = { expr = conv (El c0) A; expected = false; };

    # Constructors are genuinely well-typed (a real kernel judgment).
    "iota-checks" = { expr = chk KType c0; expected = true; };
    "refine-checks" = { expr = chk KType cT; expected = true; };
    "refine-over-refine-checks" = { expr = chk KType cTF; expected = true; };

    # decide = psi: iota accepts unconditionally; refine conjoins the lower
    # decider with the new predicate.
    "decide-iota-true" = { expr = conv (app (decide c0) xWit) H.true_; expected = true; };
    "decide-refine-conj" = {
      expr = conv (app (decide cT) xWit)
        (andB (app (decide c0) xWit) (app pTrue xWit));
      expected = true;
    };
    "decide-psi-collapse" = {
      expr = conv (app (decide cT) xWit) (app (psi cT) xWit);
      expected = true;
    };
    "decide-false" = { expr = conv (app (decide cF) xWit) H.false_; expected = true; };

    # decide drives El membership: P(true) ~> Unit (inhabited), P(false) ~> Void
    # (empty), so decide t x = true iff El t is inhabited at x.
    "decide-true-el-unit" = { expr = conv (P (app (decide c0) xWit)) H.unit; expected = true; };
    "decide-false-el-void" = { expr = conv (P (app (decide cF) xWit)) H.void; expected = true; };

    # conv/quote round-trip on a flat code: quoting then re-evaluating preserves
    # conv-equality.
    "probe-quote-roundtrip" = {
      expr = let q = Q.quote 0 (ev cT); in C.conv 0 (ev cT) (E.eval [ ] q);
      expected = true;
    };
    "probe-conv-discriminates" = { expr = conv cT cF; expected = false; };
  };
}
