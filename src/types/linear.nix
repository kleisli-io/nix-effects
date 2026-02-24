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
#   Pedrot & Tabareau (2020) "Fire Triangle" — types/checking/policy separation
{ fx, api, ... }:

let
  inherit (fx.types.foundation) mkType check;
  inherit (fx.trampoline) handle;
  inherit (api) mk;
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

  Linear = mk {
    doc = ''
      Linear type: capability token that must be consumed exactly once.

      ```
      Linear : Type -> Type
      ```

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
    value = innerType: mkType {
      name = "Linear(${innerType.name})";
      kernelType = H.any;
      guard = tokenCheck innerType;
    } // {
      innerType = innerType;
    };
    tests = {
      "linear-accepts-valid-token" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in check LIntT { _linear = true; id = 0; resource = 42; };
        expected = true;
      };
      "linear-rejects-bad-inner-type" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in check LIntT { _linear = true; id = 0; resource = "not-int"; };
        expected = false;
      };
      "linear-rejects-non-token" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in check LIntT 42;
        expected = false;
      };
      "linear-rejects-missing-linear-tag" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in check LIntT { id = 0; resource = 42; };
        expected = false;
      };
      "linear-has-innerType" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in LIntT.innerType.name;
        expected = "Int";
      };
      "linear-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Linear.value IntT).name;
        expected = "Linear(Int)";
      };
      "linear-has-validate" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Linear.value IntT) ? validate;
        expected = true;
      };
      "linear-validate-is-impure" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
          in (LIntT.validate { _linear = true; id = 0; resource = 42; })._tag;
        expected = "Impure";
      };
      # Adequacy invariant: check ⟺ all-pass handler state
      "linear-adequacy-valid" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
            token = { _linear = true; id = 0; resource = 42; };
            guardResult = check LIntT token;
            validateResult = handle {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            } (LIntT.validate token);
          in guardResult == true && validateResult.state == true;
        expected = true;
      };
      "linear-adequacy-invalid" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            LIntT = Linear.value IntT;
            badToken = { _linear = true; id = 0; resource = "not-int"; };
            guardResult = check LIntT badToken;
            validateResult = handle {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            } (LIntT.validate badToken);
          in guardResult == false && validateResult.state == false;
        expected = true;
      };
    };
  };

  # ===========================================================================
  # AFFINE TYPE — at most one consume (release allowed)
  # ===========================================================================

  Affine = mk {
    doc = ''
      Affine type: capability token that may be consumed at most once.

      ```
      Affine : Type -> Type
      ```

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
    value = innerType: mkType {
      name = "Affine(${innerType.name})";
      kernelType = H.any;
      guard = tokenCheck innerType;
    } // {
      innerType = innerType;
    };
    tests = {
      "affine-accepts-valid-token" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in check (Affine.value IntT) { _linear = true; id = 0; resource = 42; };
        expected = true;
      };
      "affine-rejects-non-token" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in check (Affine.value IntT) "not-a-token";
        expected = false;
      };
      "affine-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Affine.value IntT).name;
        expected = "Affine(Int)";
      };
      "affine-has-innerType" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Affine.value IntT).innerType.name;
        expected = "Int";
      };
    };
  };

  # ===========================================================================
  # GRADED TYPE — exactly n consumes required
  # ===========================================================================

  Graded = mk {
    doc = ''
      Graded type: capability token with usage multiplicity annotation.

      ```
      Graded : { maxUses : Int | null, innerType : Type } -> Type
      ```

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
    value = { maxUses, innerType }:
      let
        gradeStr = if maxUses == null then "ω" else toString maxUses;
      in mkType {
        name = "Graded(${gradeStr}, ${innerType.name})";
        kernelType = H.any;
        guard = tokenCheck innerType;
      } // {
        inherit innerType maxUses;
      };
    tests = {
      "graded-1-is-linear" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            G1 = Graded.value { maxUses = 1; innerType = IntT; };
          in check G1 { _linear = true; id = 0; resource = 42; };
        expected = true;
      };
      "graded-omega-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Graded.value { maxUses = null; innerType = IntT; }).name;
        expected = "Graded(ω, Int)";
      };
      "graded-5-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Graded.value { maxUses = 5; innerType = IntT; }).name;
        expected = "Graded(5, Int)";
      };
      "graded-has-maxUses" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Graded.value { maxUses = 3; innerType = IntT; }).maxUses;
        expected = 3;
      };
      "graded-has-innerType" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in (Graded.value { maxUses = 1; innerType = IntT; }).innerType.name;
        expected = "Int";
      };
      "graded-rejects-non-token" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
          in check (Graded.value { maxUses = 1; innerType = IntT; }) 42;
        expected = false;
      };
      # Adequacy for Graded
      "graded-adequacy-valid" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            GT = Graded.value { maxUses = 3; innerType = IntT; };
            token = { _linear = true; id = 0; resource = 7; };
            guardResult = check GT token;
            validateResult = handle {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            } (GT.validate token);
          in guardResult == true && validateResult.state == true;
        expected = true;
      };
      "graded-adequacy-invalid" = {
        expr =
          let
            IntT = mkType { name = "Int"; kernelType = H.int_; };
            GT = Graded.value { maxUses = 1; innerType = IntT; };
            notToken = "just-a-string";
            guardResult = check GT notToken;
            validateResult = handle {
              handlers.typeCheck = { param, state }: {
                resume = param.type.check param.value;
                state = state && (param.type.check param.value);
              };
              state = true;
            } (GT.validate notToken);
          in guardResult == false && validateResult.state == false;
        expected = true;
      };
    };
  };

in mk {
  doc = ''
    Linear type constructors: structural guards for capability tokens.

    Pure type predicates that check token structure without consuming.
    Usage enforcement is in effects/linear.nix (separate concerns).

    Linear(T)       — exactly one consume required
    Affine(T)       — at most one consume (release allowed)
    Graded(n, T)    — exactly n consumes (generalizes Linear/Affine)

    See Orchard et al. (2019) for graded modal types and
    Pedrot & Tabareau (2020) "Fire Triangle" for the types/effects split.
  '';
  value = {
    inherit Linear Affine Graded;
  };
}
