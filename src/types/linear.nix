# nix-effects linear types: Structural guards for capability tokens
#
# Pure type constructors for the linear resource system. These types
# check TOKEN STRUCTURE (is this a valid capability token wrapping
# inner type T?), NOT usage semantics (how many times consumed).
# Usage enforcement is in effects/linear.nix via the graded handler.
#
# == Types and effects are separate ==
#
# Linear(T).check verifies token structure. Linearity is enforced by
# separate effect operations (acquire/consume/release). The type system
# and linear effect system compose independently:
#
#   types/linear.nix  — "is this a valid token?" (structural guard)
#   effects/linear.nix — "has it been used correctly?" (usage tracking)
#
# Because check is pure, validate stays idempotent, the typecheck
# handler works unchanged, and the adequacy invariant holds.
#
# == Token structure ==
#
# Tokens are created by effects/linear.nix's handler:
#   { _linear : true, id : Int, resource : a }
#
# The type guard checks:
#   builtins.isAttrs v ∧ v._linear == true ∧ innerType.check v.resource
#
# == Graded generalization ==
#
# Linear(T), Affine(T), and Graded(n, T) share the same structural guard.
# The grade (maxUses) lives in the handler state, not in the token. The
# type names communicate usage intent to readers:
#
#   Linear(T)       — must be consumed exactly once
#   Affine(T)       — may be consumed at most once (release allowed)
#   Graded(n, T)    — must be consumed exactly n times
#   Graded(ω, T)    — unlimited uses
#
# == Adequacy invariant ==
#
# Linear(T).check v ⟺ all typeCheck effects in Linear(T).validate v pass
# Since mkType auto-derives validate from check, this holds by construction.
# Explicit tests confirm via the all-pass handler.
#
# References:
#   Orchard et al. (2019) "Quantitative Program Reasoning with Graded Modal Types"
#   Mesquita & Toninho (2026) "Lazy Linearity" (POPL 2026)
{ fx, api, ... }:
let
  inherit (fx.types.foundation) mkType check;
  inherit (fx.trampoline) handle;
  H = fx.tc.hoas;

  # Shared token predicate — the structural core of all linear types.
  # Checks: is an attrset, has _linear == true, has resource field,
  # and the resource inhabits the given inner type.
  tokenCheck = innerType: v:
    builtins.isAttrs v
    && v ? _linear && v._linear == true
    && v ? resource
    && innerType.check v.resource;

  # ===========================================================================
  # LINEAR TYPE — exactly one consume required
  # ===========================================================================

  Linear = innerType: mkType
    {
      name = "Linear(${innerType.name})";
      kernelType = H.any;
      guard = tokenCheck innerType;
    } // {
    innerType = innerType;
  };

  LinearTests = {
    "linear-accepts-valid-token" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        check LIntT { _linear = true; id = 0; resource = 42; };
      expected = true;
    };
    "linear-rejects-bad-inner-type" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        check LIntT { _linear = true; id = 0; resource = "not-int"; };
      expected = false;
    };
    "linear-rejects-non-token" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        check LIntT 42;
      expected = false;
    };
    "linear-rejects-missing-linear-tag" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        check LIntT { id = 0; resource = 42; };
      expected = false;
    };
    "linear-has-innerType" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        LIntT.innerType.name;
      expected = "Int";
    };
    "linear-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Linear IntT).name;
      expected = "Linear(Int)";
    };
    "linear-has-validate" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Linear IntT) ? validate;
      expected = true;
    };
    "linear-validate-is-impure" = {
      # Fail-only emission: drive impurity with an invalid token
      # (missing `_linear` marker). Valid tokens return `pure v`.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
        in
        fx.comp.isPure (LIntT.validate { id = 0; resource = 42; });
      expected = false;
    };
    # Adequacy invariant: check ⟺ all-pass handler state
    "linear-adequacy-valid" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
          token = { _linear = true; id = 0; resource = 42; };
          guardResult = check LIntT token;
          validateResult = handle
            {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            }
            (LIntT.validate token);
        in
        guardResult == true && validateResult.state == true;
      expected = true;
    };
    "linear-adequacy-invalid" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          LIntT = Linear IntT;
          badToken = { _linear = true; id = 0; resource = "not-int"; };
          guardResult = check LIntT badToken;
          validateResult = handle
            {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            }
            (LIntT.validate badToken);
        in
        guardResult == false && validateResult.state == false;
      expected = true;
    };
  };

  # ===========================================================================
  # AFFINE TYPE — at most one consume (release allowed)
  # ===========================================================================

  Affine = innerType: mkType
    {
      name = "Affine(${innerType.name})";
      kernelType = H.any;
      guard = tokenCheck innerType;
    } // {
    innerType = innerType;
  };

  AffineTests = {
    "affine-accepts-valid-token" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        check (Affine IntT) { _linear = true; id = 0; resource = 42; };
      expected = true;
    };
    "affine-rejects-non-token" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        check (Affine IntT) "not-a-token";
      expected = false;
    };
    "affine-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Affine IntT).name;
      expected = "Affine(Int)";
    };
    "affine-has-innerType" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Affine IntT).innerType.name;
      expected = "Int";
    };
  };

  # ===========================================================================
  # GRADED TYPE — exactly n consumes required
  # ===========================================================================

  Graded = { maxUses, innerType }:
    let
      gradeStr = if maxUses == null then "ω" else toString maxUses;
    in
    mkType
      {
        name = "Graded(${gradeStr}, ${innerType.name})";
        kernelType = H.any;
        guard = tokenCheck innerType;
      } // {
      inherit innerType maxUses;
    };

  GradedTests = {
    "graded-1-is-linear" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          G1 = Graded { maxUses = 1; innerType = IntT; };
        in
        check G1 { _linear = true; id = 0; resource = 42; };
      expected = true;
    };
    "graded-omega-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Graded { maxUses = null; innerType = IntT; }).name;
      expected = "Graded(ω, Int)";
    };
    "graded-5-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Graded { maxUses = 5; innerType = IntT; }).name;
      expected = "Graded(5, Int)";
    };
    "graded-has-maxUses" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Graded { maxUses = 3; innerType = IntT; }).maxUses;
      expected = 3;
    };
    "graded-has-innerType" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        (Graded { maxUses = 1; innerType = IntT; }).innerType.name;
      expected = "Int";
    };
    "graded-rejects-non-token" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
        in
        check (Graded { maxUses = 1; innerType = IntT; }) 42;
      expected = false;
    };
    # Adequacy for Graded
    "graded-adequacy-valid" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          GT = Graded { maxUses = 3; innerType = IntT; };
          token = { _linear = true; id = 0; resource = 7; };
          guardResult = check GT token;
          validateResult = handle
            {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            }
            (GT.validate token);
        in
        guardResult == true && validateResult.state == true;
      expected = true;
    };
    "graded-adequacy-invalid" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          GT = Graded { maxUses = 1; innerType = IntT; };
          notToken = "just-a-string";
          guardResult = check GT notToken;
          validateResult = handle
            {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            }
            (GT.validate notToken);
        in
        guardResult == false && validateResult.state == false;
      expected = true;
    };
  };

in
api.namespace {
  description = "Linear type constructors: `Linear`/`Affine`/`Graded` — pure structural guards for capability tokens; usage enforcement lives in the linear effect handler.";
  doc = ''
    Linear type constructors: structural guards for capability tokens.

    Pure type predicates that check token structure without consuming.
    Usage enforcement is in effects/linear.nix (separate concerns).

    Linear(T)       — exactly one consume required
    Affine(T)       — at most one consume (release allowed)
    Graded(n, T)    — exactly n consumes (generalizes Linear/Affine)

    See Orchard et al. (2019) for graded modal types.
  '';
  value = {
    Linear = api.leaf {
      value = Linear;
      description = "Linear: structural type constructor for capability tokens that must be consumed exactly once; checks token shape, leaves usage tracking to the linear effect handler.";
      signature = "Linear : Type -> Type";
      doc = ''
        Linear type: capability token that must be consumed exactly once.

        Creates a type whose `check` verifies the capability token structure:

        ```nix
        { _linear = true, id = Int, resource = innerType }
        ```

        Pure structural guard — checking does not consume the token.
        `effects/linear.nix` tracks consumption separately.

        Adequacy invariant:

        ```
        Linear(T).check v ⟺ all typeCheck effects in Linear(T).validate v pass
        ```

        Holds by construction via `mkType`'s auto-derived `validate`.

        Operations:

        - `.check v` — pure guard: is v a valid linear token wrapping T?
        - `.validate v` — effectful: sends `typeCheck` for blame tracking
        - `.innerType` — the wrapped type T
      '';
      tests = LinearTests;
    };
    Affine = api.leaf {
      value = Affine;
      description = "Affine: structural type constructor for capability tokens that may be consumed at most once; identical shape to `Linear`, release is permitted.";
      signature = "Affine : Type -> Type";
      doc = ''
        Affine type: capability token that may be consumed at most once.

        Structurally identical to `Linear(T)`. The name communicates that the
        resource may be explicitly released (dropped) via `effects/linear.release`
        without consuming it — "at most once" vs Linear's "exactly once."

        The structural guard is the same: both check for a valid capability
        token with inner type T. The usage distinction (exactly-once vs
        at-most-once) is enforced by the effect handler, not the type system.

        Operations:

        - `.check v` — pure guard: is v a valid affine token wrapping T?
        - `.validate v` — effectful: sends `typeCheck` for blame tracking
        - `.innerType` — the wrapped type T
      '';
      tests = AffineTests;
    };
    Graded = api.leaf {
      value = Graded;
      description = "Graded: structural type constructor for capability tokens with declared usage multiplicity; generalises Linear/Affine via the `maxUses` parameter.";
      signature = "Graded : { maxUses : Int | null, innerType : Type } -> Type";
      doc = ''
        Graded type: capability token with usage multiplicity annotation.

        Generalizes Linear and Affine via a `maxUses` parameter:

        ```nix
        Graded { maxUses = 1; innerType = T; }    # ≡ Linear(T)
        Graded { maxUses = null; innerType = T; }  # ≡ Unlimited(T)
        Graded { maxUses = n; innerType = T; }     # ≡ Exact(n, T)
        ```

        The structural guard is the same as Linear and Affine — token
        structure with inner type check. The `maxUses` appears in the type
        name for documentation but is NOT checked by the guard (the grade
        lives in handler state, not the token).

        The name uses ω for null (unlimited):
        `Graded(1, Int)`, `Graded(5, String)`, `Graded(ω, Bool)`

        From Orchard et al. (2019) "Quantitative Program Reasoning with
        Graded Modal Types" — semiring-indexed usage annotations where
        + models branching, × models sequencing, 1 = linear, ω = unlimited.

        Operations:

        - `.check v` — pure guard: is v a valid graded token wrapping T?
        - `.validate v` — effectful: sends `typeCheck` for blame tracking
        - `.innerType` — the wrapped type T
        - `.maxUses` — the declared usage multiplicity
      '';
      tests = GradedTests;
    };

  };
}
