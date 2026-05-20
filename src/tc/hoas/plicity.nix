# Plicity sidecar for HOAS binders/applications. Kernel-invariant:
# `H.elab (H.implicitForall n A f) == H.elab (H.forall n A f)` — the
# elaborator's pi/lam/app dispatch ignores `_plicity`. Consumed by the
# bidirectional insertion algorithm in `tc/elaborate/`.
{ self, api, ... }:

let
  explicit = "explicit";
  implicit = "implicit";

  isPlicity = p: p == explicit || p == implicit;

  isImplicit = p: p == implicit;

  surfacePlicity = node:
    if builtins.isAttrs node && node ? _plicity
    then node._plicity
    else explicit;

  withPlicity = p: node:
    if isPlicity p then node // { _plicity = p; }
    else throw "hoas.plicity: invalid plicity ${builtins.toJSON p}";
in
{
  scope = {
    plicity = api.leaf {
      value = {
        inherit explicit implicit isPlicity isImplicit;
      };
      description = "Plicity tag namespace: explicit/implicit values + predicates.";
      signature = "{ explicit : Plicity; implicit : Plicity; isPlicity : Any -> Bool; isImplicit : Plicity -> Bool; }";
    };

    surfacePlicity = api.leaf {
      value = surfacePlicity;
      description = "Read the plicity sidecar, defaulting to explicit.";
      signature = "Any -> Plicity";
    };

    implicitForall = api.leaf {
      value = name: domain: bodyFn:
        withPlicity implicit (self.forall name domain bodyFn);
      description = "Implicit Π-binder. Same kernel Tm as `forall`, plus `_plicity` sidecar.";
      signature = "String -> Hoas -> (Hoas -> Hoas) -> Hoas";
    };

    implicitLam = api.leaf {
      value = name: domain: bodyFn:
        withPlicity implicit (self.lam name domain bodyFn);
      description = "Implicit λ-binder. Same kernel Tm as `lam`, plus `_plicity` sidecar.";
      signature = "String -> Hoas -> (Hoas -> Hoas) -> Hoas";
    };

    implicitApp = api.leaf {
      value = fn: arg:
        withPlicity implicit (self.app fn arg);
      description = "Implicit application — caller passes implicit explicitly. Same kernel Tm as `app`, plus `_plicity` sidecar.";
      signature = "Hoas -> Hoas -> Hoas";
    };
  };

  tests = {
    "plicity-default-is-explicit" = {
      expr = surfacePlicity (self.forall "A" (self.u 0) (A: A));
      expected = explicit;
    };

    "plicity-default-on-non-attrs" = {
      expr = surfacePlicity 42;
      expected = explicit;
    };

    "plicity-implicit-forall-carries-sidecar" = {
      expr = (self.implicitForall "A" (self.u 0) (A: A))._plicity;
      expected = implicit;
    };

    "plicity-implicit-lam-carries-sidecar" = {
      expr = (self.implicitLam "x" self.nat (x: x))._plicity;
      expected = implicit;
    };

    "plicity-implicit-app-carries-sidecar" = {
      expr = (self.implicitApp self.succ self.zero)._plicity;
      expected = implicit;
    };

    "plicity-surfacePlicity-reads-implicit" = {
      expr = self.surfacePlicity (self.implicitForall "A" (self.u 0) (A: A));
      expected = implicit;
    };

    "plicity-explicit-forall-unchanged" = {
      expr =
        let node = self.forall "A" (self.u 0) (A: A);
        in node._htag == "pi" && !(node ? _plicity);
      expected = true;
    };

    "plicity-implicit-forall-elaborates-with-pi-sidecar" = {
      expr =
        let tm = self.elab (self.implicitForall "A" (self.u 0) (A: A));
        in { inherit (tm) tag name; plicity = tm._plicity or null; };
      expected = { tag = "pi"; name = "A"; plicity = implicit; };
    };

    "plicity-explicit-forall-elaborates-without-sidecar" = {
      expr =
        let tm = self.elab (self.forall "A" (self.u 0) (A: A));
        in tm ? _plicity;
      expected = false;
    };

    "plicity-implicit-lam-elaborates-with-lam-sidecar" = {
      expr =
        let tm = self.elab (self.implicitLam "x" self.nat (x: x));
        in { inherit (tm) tag name; plicity = tm._plicity or null; };
      expected = { tag = "lam"; name = "x"; plicity = implicit; };
    };

    "plicity-implicit-app-elaborates-with-app-sidecar" = {
      expr =
        let
          f = self.lam "x" self.nat (x: x);
          tm = self.elab (self.implicitApp f self.zero);
        in
        { inherit (tm) tag; plicity = tm._plicity or null; };
      expected = { tag = "app"; plicity = implicit; };
    };

    "plicity-isPlicity-positive" = {
      expr = [
        (self.plicity.isPlicity explicit)
        (self.plicity.isPlicity implicit)
      ];
      expected = [ true true ];
    };

    "plicity-isPlicity-negative" = {
      expr = self.plicity.isPlicity "bogus";
      expected = false;
    };

    "plicity-isImplicit-discriminates" = {
      expr = [
        (self.plicity.isImplicit implicit)
        (self.plicity.isImplicit explicit)
      ];
      expected = [ true false ];
    };
  };

}
