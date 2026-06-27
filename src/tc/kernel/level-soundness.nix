# Synthesised universes carry term-independent levels.
#
# Every `U(L)` the checker uses as a classifier has `L` resting only on
# `zero`/`suc`/`max`/bare-`var` bases — never an applied neutral (`f x`). A
# term-dependent level would make `U(a) = U(b)` hinge on term equality and break
# well-foundedness (Girard). `admitLevel` (shared from `conv`) guards every site
# that reads a level off a universe to classify with it: the `infer` introduction
# rules, the `checkTypeLevel` boundary, and eliminator-motive codomains.
# Application may still carry a term-dependent `U(L)` as a term's type, but it can
# never classify anything — every promotion to type position re-gates.
#
# Pinned on three axes: coverage (gate fires on term-dependent levels),
# gate-correctness (no over-reject of polymorphic/closed levels), decidability
# (conversion is exact and the level algebra normalises).
{ fx, ... }:

let
  chk = fx.tc.check;
  T = fx.tc.term;
  V = fx.tc.value;
  C = fx.tc.conv;
  E = fx.tc.eval;

  inherit (chk) emptyCtx extend inferTm;

  l0 = T.mkLevelZero;
  lsuc = T.mkLevelSuc;
  lmax = T.mkLevelMax;

  # A synthesis result is rejected exactly when the level-dependence gate fires.
  rejects = r: (r ? error) && (r.msg or "") == "universe level may not depend on a term";
  admits = r: r ? type;

  # f : Unit -> Level, x : Unit; `f x` is the canonical term-dependent level.
  ctxFX = extend (extend emptyCtx "f" (V.vPi "_" V.vUnit (V.mkClosure [ ] T.mkLevel))) "x" V.vUnit;
  appFX = T.mkApp (T.mkVar 1) (T.mkVar 0);

  # k : Level, m : Level — bare (term-independent) level variables.
  ctxKM = extend (extend emptyCtx "k" V.vLevel) "m" V.vLevel;
  k = T.mkVar 1;
  m = T.mkVar 0;
  convKM = a: b: C.convLevel (E.eval ctxKM.env a) (E.eval ctxKM.env b);
  conv0 = a: b: C.convLevel (E.eval [ ] a) (E.eval [ ] b);

  # Universe formers over level variables (term-independent, must be admitted).
  polyU = T.mkPi "k" T.mkLevel (T.mkU (T.mkVar 0)); # Pi k. U(k)
  polyUsuc = T.mkPi "k" T.mkLevel (T.mkU (lsuc (T.mkVar 0))); # Pi k. U(suc k)
  polyUmax = T.mkPi "k" T.mkLevel (T.mkPi "m" T.mkLevel
    (T.mkU (lmax (T.mkVar 1) (T.mkVar 0)))); # Pi k m. U(max k m)
  polyUmaxsuc = T.mkPi "k" T.mkLevel (T.mkPi "m" T.mkLevel
    (T.mkU (lmax (lsuc (T.mkVar 1)) (lsuc (T.mkVar 0))))); # Pi k m. U(max(suc k)(suc m))

  # A non-lambda eliminator motive whose codomain universe is term-dependent:
  # a level-polymorphic universe family applied at `f x` (instantiated by the
  # ungated app rule), consumed as a `boot-sum` motive. The motive read must
  # re-gate the codomain level, else the eliminator types at `U(suc (f x))`.
  uu = T.mkBootSum T.mkUnit T.mkUnit;
  uniK = T.mkAnn
    (T.mkLam "k" T.mkLevel (T.mkU (T.mkVar 0)))
    (T.mkPi "k" T.mkLevel (T.mkU (lsuc (T.mkVar 0))));
  constU2 = T.mkAnn
    (T.mkLam "k" T.mkLevel (T.mkLam "s" uu (T.mkU (lsuc (T.mkVar 1)))))
    (T.mkPi "k" T.mkLevel (T.mkPi "s" uu (T.mkU (lsuc (lsuc (T.mkVar 1))))));
  arm = T.mkLam "s" T.mkUnit (T.mkApp uniK (T.mkApp (T.mkVar 2) (T.mkVar 1)));
  elimTermDepMotive = T.mkBootSumElim T.mkUnit T.mkUnit
    (T.mkApp constU2 appFX) arm arm
    (T.mkBootInl T.mkUnit T.mkUnit T.mkTt);
in
{
  scope = { };
  tests = {
    # Coverage: gate fires on a term-dependent level (U, descriptor, Pi codomain).
    "coverage-universe-of-applied" =
      { expr = rejects (inferTm ctxFX (T.mkU appFX)); expected = true; };
    "coverage-desc-of-applied" =
      { expr = rejects (inferTm ctxFX (T.mkDesc appFX T.mkUnit)); expected = true; };
    "coverage-pi-codomain-applied" =
      {
        expr = rejects (inferTm ctxFX
          (T.mkPi "_" T.mkUnit (T.mkU (T.mkApp (T.mkVar 2) (T.mkVar 1)))));
        expected = true;
      };
    "coverage-eliminator-motive-applied" =
      { expr = rejects (inferTm ctxFX elimTermDepMotive); expected = true; };

    # Gate-correctness: level polymorphism and closed levels are admitted.
    "admit-level-variable" = { expr = admits (inferTm emptyCtx polyU); expected = true; };
    "admit-suc-of-variable" = { expr = admits (inferTm emptyCtx polyUsuc); expected = true; };
    "admit-max-of-variables" = { expr = admits (inferTm emptyCtx polyUmax); expected = true; };
    "admit-max-of-successors" = { expr = admits (inferTm emptyCtx polyUmaxsuc); expected = true; };
    "admit-closed-level" = { expr = admits (inferTm emptyCtx (T.mkU (lsuc l0))); expected = true; };

    # Decidability: conversion is exact (non-cumulative) and the level algebra
    # normalises. `max 2 1 != 1` is what makes a strict `LiftAt l > m` unprovable.
    "conv-reflexive" = { expr = conv0 (lsuc l0) (lsuc l0); expected = true; };
    "conv-no-cumulativity-0-1" = { expr = conv0 l0 (lsuc l0); expected = false; };
    "conv-no-cumulativity-1-2" = { expr = conv0 (lsuc l0) (lsuc (lsuc l0)); expected = false; };
    "level-max-right-unit" = { expr = convKM (lmax k l0) k; expected = true; };
    "level-max-suc-distributes" =
      { expr = convKM (lmax (lsuc k) (lsuc m)) (lsuc (lmax k m)); expected = true; };
    "liftat-strict-witness-unprovable" =
      { expr = conv0 (lmax (lsuc (lsuc l0)) (lsuc l0)) (lsuc l0); expected = false; };
  };
}
