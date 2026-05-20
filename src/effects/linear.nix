# nix-effects linear: Graded linear resource tracking
#
# Tracks capability tokens through the effect system with usage counting.
# Resources are wrapped in opaque tokens at acquire time; the handler
# maintains a resource map counting each consume call against a maxUses
# bound. At handler exit, a finalizer (return clause) checks that each
# resource was consumed the expected number of times.
#
# Graded(n, T) generalizes:
#   Linear     = acquire maxUses=1       — exactly one consume required
#   Affine     = acquire maxUses=1 + release — at most one (may drop)
#   Exact(n)   = acquire maxUses=n       — exactly n consumes required
#   Unlimited  = acquire maxUses=null    — any number of consumes
#
# The handler state shape { nextId, resources } is deepSeq-safe: all
# values are scalars or flat attrsets of scalars. This is required by
# trampoline.nix:76,86 which calls builtins.deepSeq on handler state.
#
# References:
#   Orchard et al. (2019) "Quantitative Program Reasoning with Graded Modal Types"
#   Mesquita & Toninho (2026) "Lazy Linearity" (POPL 2026)
#   Congard et al. (2025) "Linear Effects" (destructors)
#   Ahman & Bauer (2023) "Runners in Action" (return clause as runner model)
{ fx, lib, ... }:
let
  inherit (fx.kernel) pure bind send;
  inherit (fx.trampoline) handle;
  # ===========================================================================
  # EFFECT OPERATIONS (return Computations — suspended effects)
  # ===========================================================================

  acquire = { resource, maxUses }: send "linearAcquire" { inherit resource maxUses; };

  consume = token: send "linearConsume" { inherit token; };

  release = token: send "linearRelease" { inherit token; };

  # ===========================================================================
  # CONVENIENCE CONSTRUCTORS
  # ===========================================================================

  acquireLinear = resource: send "linearAcquire" { inherit resource; maxUses = 1; };

  acquireExact = resource: n: send "linearAcquire" { inherit resource; maxUses = n; };

  acquireUnlimited = resource: send "linearAcquire" { inherit resource; maxUses = null; };

  # ===========================================================================
  # HANDLER
  # ===========================================================================
  #
  # Handler state shape (deepSeq-safe — all scalars):
  #   { nextId : Int
  #   , resources : { <id> : { resource, maxUses, currentUses, released } }
  #   }
  #
  # Token shape (returned by linearAcquire):
  #   { _linear : true, id : Int, resource : a }

  handler = {
    linearAcquire = { param, state }:
      let
        id = state.nextId;
        token = { _linear = true; inherit id; resource = param.resource; };
      in {
        resume = token;
        state = state // {
          nextId = id + 1;
          resources = state.resources // {
            ${toString id} = {
              resource = param.resource;
              maxUses = param.maxUses;
              currentUses = 0;
              released = false;
            };
          };
        };
      };

    linearConsume = { param, state }:
      let
        id = toString param.token.id;
        entry = state.resources.${id};
        newUses = entry.currentUses + 1;
        withinBound = entry.maxUses == null || newUses <= entry.maxUses;
      in
        if entry.released then {
          abort = {
            _tag = "LinearityError";
            error = "consume-after-release";
            resource = entry.resource;
          };
          inherit state;
        }
        else if !withinBound then {
          abort = {
            _tag = "LinearityError";
            error = "exceeded-bound";
            resource = entry.resource;
            maxUses = entry.maxUses;
            attempted = newUses;
          };
          inherit state;
        }
        else {
          resume = param.token.resource;
          state = state // {
            resources = state.resources // {
              ${id} = entry // { currentUses = newUses; };
            };
          };
        };

    linearRelease = { param, state }:
      let
        id = toString param.token.id;
        entry = state.resources.${id};
      in
        if entry.released then {
          abort = {
            _tag = "LinearityError";
            error = "double-release";
            resource = entry.resource;
          };
          inherit state;
        }
        else {
          resume = null;
          state = state // {
            resources = state.resources // {
              ${id} = entry // { released = true; };
            };
          };
        };
  };

  # ===========================================================================
  # RETURN CLAUSE (FINALIZER)
  # ===========================================================================
  #
  # Runs on BOTH normal return AND abort (trampoline.nix:161 calls return
  # regardless — abort sets _comp = mkPure(abort_value), then return sees it).
  # This is a simplified runner model (Ahman & Bauer 2023).
  #
  # Checks that every non-released resource with a finite maxUses bound
  # was consumed exactly maxUses times. Violations produce a LinearityError
  # value (tagged, never throws — safe destructor per Congard et al.).

  return = value: state:
    let
      checkResource = _: r:
        r.released
        || r.maxUses == null
        || r.currentUses == r.maxUses;
      violations = lib.filterAttrs (id: r: !(checkResource id r)) state.resources;
    in
      if violations == {} then
        { inherit value state; }
      else {
        value = {
          _tag = "LinearityError";
          error = "usage-mismatch";
          details = lib.mapAttrsToList (_: r: {
            resource = r.resource;
            expected = r.maxUses;
            actual = r.currentUses;
          }) violations;
          original = value;
        };
        inherit state;
      };

  # ===========================================================================
  # INITIAL STATE & RUN CONVENIENCE
  # ===========================================================================

  initialState = { nextId = 0; resources = {}; };

  run = comp: handle {
    inherit return;
    handlers = handler;
    state = initialState;
  } comp;

in {
  inherit acquire consume release;
  inherit acquireLinear acquireExact acquireUnlimited;
  inherit handler return initialState run;

  # Per-binding documentation. Sibling to the bindings above; consumed by
  # `extractDocs`/`extractTests`, stripped by `extractValue` so it doesn't
  # appear in the public API tree.


  __docs = {
    _self = {
      description = "linear effect: graded resource discipline (linear, affine, exact n, unlimited) via acquire/consume/release with a finalizer enforcing usage bounds.";
      doc = ''
    Graded linear resource tracking: acquire/consume/release with usage enforcement.

    Each resource gets a capability token at acquire time. The graded handler
    covers linear (exactly once), affine (at most once via release), exact(n),
    and unlimited usage through a single maxUses parameter.

    Quick start:

    ```nix
    let comp = bind (linear.acquireLinear "secret") (token:
      bind (linear.consume token) (val:
        pure val));
    in linear.run comp
    ```

    For composition with other handlers, use handler/return/initialState with
    `adaptHandlers`.
  '';
    };

    acquire = {
      description = "acquire: take a graded linear resource and obtain a capability token; `maxUses` (or null) sets the linearity bound enforced by the handler.";
      signature = "acquire : { resource : a, maxUses : Int | null } -> Computation Token";
      doc = ''
        Acquire a graded linear resource. Returns a capability token.

        The token wraps the resource with an ID for tracking. The handler
        maintains a resource map in its state, counting each consume call
        against the maxUses bound.

        - `maxUses = 1` — Linear: exactly one consume required
        - `maxUses = n` — Exact: exactly n consumes required
        - `maxUses = null` — Unlimited: any number of consumes allowed

        Tokens should be consumed exactly maxUses times, or explicitly
        released. At handler exit, the return clause (finalizer) checks:
        released → always OK, `maxUses = null` → always OK,
        otherwise → `currentUses` must equal `maxUses`.
      '';
      tests = {
        "acquire-is-impure" = {
          expr = fx.comp.isPure (acquire { resource = "x"; maxUses = 1; });
          expected = false;
        };
        "acquire-effect-name" = {
          expr = (acquire { resource = "x"; maxUses = 1; }).effect.name;
          expected = "linearAcquire";
        };
        "acquire-carries-resource" = {
          expr = (acquire { resource = "db"; maxUses = 2; }).effect.param.resource;
          expected = "db";
        };
        "acquire-carries-maxUses" = {
          expr = (acquire { resource = "x"; maxUses = 3; }).effect.param.maxUses;
          expected = 3;
        };
      };
    };

    consume = {
      description = "consume: spend a use of a capability token and return the wrapped resource; aborts with `LinearityError` on use-after-release or bound-exceeded.";
      signature = "consume : Token -> Computation a";
      doc = ''
        Consume a capability token, returning the wrapped resource value.

        Increments the token's usage counter. Aborts with `LinearityError` if:
        - Token was already released (`"consume-after-release"`)
        - Usage would exceed maxUses bound (`"exceeded-bound"`)

        The returned value is the original resource passed to acquire.
      '';
      tests = {
        "consume-is-impure" = {
          expr = fx.comp.isPure (consume { _linear = true; id = 0; resource = "x"; });
          expected = false;
        };
        "consume-effect-name" = {
          expr = (consume { _linear = true; id = 0; resource = "x"; }).effect.name;
          expected = "linearConsume";
        };
        "consume-carries-token" = {
          expr = (consume { _linear = true; id = 0; resource = "x"; }).effect.param.token._linear;
          expected = true;
        };
      };
    };

    release = {
      description = "release: drop a capability token without consuming it; the finalizer then skips it (affine usage). Aborts on double-release.";
      signature = "release : Token -> Computation null";
      doc = ''
        Explicitly release a capability token without consuming it.

        Marks the resource as released. The finalizer skips released resources,
        so this allows affine usage (acquire then drop). Aborts with
        `LinearityError` on double-release.
      '';
      tests = {
        "release-is-impure" = {
          expr = fx.comp.isPure (release { _linear = true; id = 0; resource = "x"; });
          expected = false;
        };
        "release-effect-name" = {
          expr = (release { _linear = true; id = 0; resource = "x"; }).effect.name;
          expected = "linearRelease";
        };
      };
    };

    acquireLinear = {
      description = "acquireLinear: acquire a strictly linear resource (maxUses = 1); the finalizer fails unless exactly one consume happens before scope exit.";
      signature = "acquireLinear : a -> Computation Token";
      doc = ''
        Acquire a linear resource (exactly one consume required).
      '';
      tests = {
        "acquireLinear-maxUses-is-1" = {
          expr = (acquireLinear "x").effect.param.maxUses;
          expected = 1;
        };
      };
    };

    acquireExact = {
      description = "acquireExact: acquire a resource that must be consumed exactly `n` times; encodes graded linearity beyond pure linear/affine.";
      signature = "acquireExact : a -> Int -> Computation Token";
      doc = ''
        Acquire a resource that must be consumed exactly n times.
      '';
      tests = {
        "acquireExact-maxUses" = {
          expr = (acquireExact "x" 5).effect.param.maxUses;
          expected = 5;
        };
      };
    };

    acquireUnlimited = {
      description = "acquireUnlimited: acquire a resource with `maxUses = null`; the finalizer never reports usage mismatches for unlimited tokens.";
      signature = "acquireUnlimited : a -> Computation Token";
      doc = ''
        Acquire an unlimited resource (any number of consumes allowed).
      '';
      tests = {
        "acquireUnlimited-maxUses-is-null" = {
          expr = (acquireUnlimited "x").effect.param.maxUses;
          expected = null;
        };
      };
    };

    handler = {
      description = "linear.handler: interprets linearAcquire/linearConsume/linearRelease over a `{ nextId, resources }` state; emits tagged LinearityError on misuse.";
      doc = ''
        Graded linear resource handler. Interprets linearAcquire, linearConsume,
        and linearRelease effects. Tracks resource usage in handler state.

        Use with `trampoline.handle`:

        ```nix
        handle {
          handlers = linear.handler;
          return = linear.return;
          state = linear.initialState;
        } comp
        ```

        Or use the convenience: `linear.run comp`

        - `linearAcquire`: creates token, adds resource entry to state
        - `linearConsume`: increments usage counter, returns resource value
        - `linearRelease`: marks resource as released (finalizer skips it)
      '';
      tests = {
        "handler-acquire-returns-token" = {
          expr =
            let r = handler.linearAcquire {
              param = { resource = "db"; maxUses = 1; };
              state = { nextId = 0; resources = {}; };
            };
            in r.resume._linear && r.resume.id == 0 && r.resume.resource == "db";
          expected = true;
        };
        "handler-acquire-advances-nextId" = {
          expr =
            let r = handler.linearAcquire {
              param = { resource = "x"; maxUses = 1; };
              state = { nextId = 5; resources = {}; };
            };
            in r.state.nextId;
          expected = 6;
        };
        "handler-consume-returns-resource" = {
          expr =
            let r = handler.linearConsume {
              param = { token = { _linear = true; id = 0; resource = "secret"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "secret"; maxUses = 1; currentUses = 0; released = false; };
              }; };
            };
            in r.resume;
          expected = "secret";
        };
        "handler-consume-increments-counter" = {
          expr =
            let r = handler.linearConsume {
              param = { token = { _linear = true; id = 0; resource = "x"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "x"; maxUses = 3; currentUses = 1; released = false; };
              }; };
            };
            in r.state.resources."0".currentUses;
          expected = 2;
        };
        "handler-consume-aborts-on-exceeded-bound" = {
          expr =
            let r = handler.linearConsume {
              param = { token = { _linear = true; id = 0; resource = "x"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 1; released = false; };
              }; };
            };
            in r.abort._tag == "LinearityError" && r.abort.error == "exceeded-bound";
          expected = true;
        };
        "handler-consume-aborts-on-released" = {
          expr =
            let r = handler.linearConsume {
              param = { token = { _linear = true; id = 0; resource = "x"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 0; released = true; };
              }; };
            };
            in r.abort.error;
          expected = "consume-after-release";
        };
        "handler-release-marks-released" = {
          expr =
            let r = handler.linearRelease {
              param = { token = { _linear = true; id = 0; resource = "x"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 0; released = false; };
              }; };
            };
            in r.state.resources."0".released;
          expected = true;
        };
        "handler-release-aborts-on-double" = {
          expr =
            let r = handler.linearRelease {
              param = { token = { _linear = true; id = 0; resource = "x"; }; };
              state = { nextId = 1; resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 0; released = true; };
              }; };
            };
            in r.abort.error;
          expected = "double-release";
        };
      };
    };

    return = {
      description = "linear.return: finalizer checking every non-released, finite-bound resource was consumed exactly `maxUses` times; wraps mismatches in LinearityError.";
      signature = "return : a -> State -> { value : a | LinearityError, state : State }";
      doc = ''
        Finalizer return clause for the linear handler.

        Checks each resource in handler state:
        - `released` → OK (explicitly dropped)
        - `maxUses = null` → OK (unlimited)
        - otherwise → `currentUses` must equal `maxUses`

        On violation, wraps the original value in a `LinearityError` with
        details of each mismatched resource. On success, passes through
        unchanged. Runs on both normal return and abort paths.
      '';
      tests = {
        "return-passes-clean-state" = {
          expr =
            let r = return "ok" {
              nextId = 1;
              resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 1; released = false; };
              };
            };
            in r.value;
          expected = "ok";
        };
        "return-catches-underuse" = {
          expr =
            let r = return "ok" {
              nextId = 1;
              resources = {
                "0" = { resource = "leaked"; maxUses = 1; currentUses = 0; released = false; };
              };
            };
            in r.value._tag == "LinearityError" && r.value.error == "usage-mismatch";
          expected = true;
        };
        "return-skips-released" = {
          expr =
            let r = return "ok" {
              nextId = 1;
              resources = {
                "0" = { resource = "dropped"; maxUses = 1; currentUses = 0; released = true; };
              };
            };
            in r.value;
          expected = "ok";
        };
        "return-skips-unlimited" = {
          expr =
            let r = return "ok" {
              nextId = 1;
              resources = {
                "0" = { resource = "free"; maxUses = null; currentUses = 42; released = false; };
              };
            };
            in r.value;
          expected = "ok";
        };
        "return-preserves-original-on-error" = {
          expr =
            let r = return "my-result" {
              nextId = 1;
              resources = {
                "0" = { resource = "x"; maxUses = 1; currentUses = 0; released = false; };
              };
            };
            in r.value.original;
          expected = "my-result";
        };
      };
    };

    initialState = {
      description = "linear.initialState: `{ nextId = 0; resources = {}; }`; monotonic ID counter plus an empty resource map indexed by stringified ID.";
      doc = ''
        Initial handler state for the linear resource handler.

        ```nix
        { nextId = 0; resources = {}; }
        ```

        - `nextId`: monotonic counter for generating unique resource IDs.
        - `resources`: map from ID (string) to resource tracking entry.
      '';
      tests = {
        "initialState-has-nextId" = {
          expr = initialState.nextId;
          expected = 0;
        };
        "initialState-has-empty-resources" = {
          expr = initialState.resources;
          expected = {};
        };
      };
    };

    run = {
      description = "linear.run: convenience wrapper bundling handler, return, and initialState; runs a computation under the graded linear discipline.";
      signature = "run : Computation a -> { value : a | LinearityError, state : State }";
      doc = ''
        Run a computation with the graded linear handler.

        Bundles handler, return clause, and initial state into one call.
        To compose with other handlers, use handler/return/initialState
        separately with `adaptHandlers`.

        ```nix
        let
          comp = bind (acquireLinear "secret") (token:
            bind (consume token) (val:
              pure "got:''${val}"));
        in linear.run comp
        # => { value = "got:secret"; state = { nextId = 1; resources = { ... }; }; }
        ```
      '';
      tests = {
        "run-linear-happy-path" = {
          expr =
            let
              comp = bind (acquireLinear "secret") (token:
                bind (consume token) (val:
                  pure "got:${val}"));
            in (run comp).value;
          expected = "got:secret";
        };
        "run-linear-leak-detected" = {
          expr =
            let
              comp = bind (acquireLinear "leaked") (_token:
                pure "forgot");
            in (run comp).value._tag == "LinearityError"
               && (run comp).value.error == "usage-mismatch";
          expected = true;
        };
        "run-exceeded-bound-aborts" = {
          expr =
            let
              comp = bind (acquireLinear "once") (token:
                bind (consume token) (_:
                  bind (consume token) (_:
                    pure "unreachable")));
            in (run comp).value._tag == "LinearityError"
               && (run comp).value.error == "exceeded-bound";
          expected = true;
        };
        "run-affine-via-release" = {
          expr =
            let
              comp = bind (acquireLinear "optional") (token:
                bind (release token) (_:
                  pure "dropped"));
            in (run comp).value;
          expected = "dropped";
        };
        "run-graded-exact-2" = {
          expr =
            let
              comp = bind (acquireExact "two-shot" 2) (token:
                bind (consume token) (v1:
                  bind (consume token) (v2:
                    pure "${v1}+${v2}")));
            in (run comp).value;
          expected = "two-shot+two-shot";
        };
        "run-unlimited" = {
          expr =
            let
              comp = bind (acquireUnlimited "free") (token:
                builtins.foldl'
                  (acc: _: bind acc (_: consume token))
                  (pure null)
                  (lib.range 1 10));
            in (run comp).value ? _tag;
          expected = false;
        };
        "run-mixed-resources" = {
          expr =
            let
              comp =
                bind (acquireLinear "once") (t1:
                bind (acquireExact "twice" 2) (t2:
                bind (acquireUnlimited "many") (t3:
                bind (consume t1) (_:
                bind (consume t2) (_:
                bind (consume t2) (_:
                bind (consume t3) (_:
                bind (consume t3) (_:
                bind (consume t3) (_:
                  pure "all-correct")))))))));
            in (run comp).value;
          expected = "all-correct";
        };
        "run-consume-after-release-aborts" = {
          expr =
            let
              comp = bind (acquireLinear "x") (token:
                bind (release token) (_:
                  bind (consume token) (_:
                    pure "unreachable")));
            in (run comp).value.error;
          expected = "consume-after-release";
        };
        "run-deepSeq-100-pairs" = {
          expr =
            let
              mkPair = i:
                bind (acquireLinear "r-${toString i}") (token:
                  consume token);
              comp = builtins.foldl'
                (acc: i: bind acc (_: mkPair i))
                (pure null)
                (lib.range 0 99);
            in (run comp).value ? _tag;
          expected = false;
        };
      };
    };

  };
}
