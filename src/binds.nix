# nix-effects bind: Idiomatic Nix bind helpers.
#
#
# - bind.attrs: Binds effectful attributeSet values
# - bind.comp: Binds effectful function args.
# - bind.fn: Binds pure Nix function args.
#
{ fx, lib, api, ... }:
let

  inherit (fx.comp) pure isComp;
  inherit (fx.kernel) bind send;

  # Sentinel marking an attr as optional in bindAttrs: the value is probed
  # via has-handler before sending; if no handler exists, the key is omitted
  # from the resolved attrset (Nix function defaults can then kick in).
  # bindComp/bindFn translate `lib.functionArgs f`'s `true` (= has default)
  # into this marker before calling bindAttrs.
  optionalArg = { __bindAttrsOptional = true; };

  isOptionalMarker = v: builtins.isAttrs v && (v.__bindAttrsOptional or false);

  bindAttrs = attrs:
    let
      skip = n: !builtins.elem n [ "__sort" "__functor" "__functionArgs" ];
      clean = builtins.filter skip (builtins.attrNames attrs);
      sort = attrs.__sort or lib.id;
      names = sort clean;
      toComp = name:
        let value = attrs.${name}; in
        if isComp value
        then { inherit name; comp = value; optional = false; }
        else if isOptionalMarker value
        then { inherit name; comp = send name null; optional = true; }
        else { inherit name; comp = send name value; optional = false; };
    in
    builtins.foldl'
      (prev: curr:
        bind prev (acc:
          if curr.optional then
          # Optional arg: probe handler first, skip if absent (Nix default kicks in)
            bind (send "has-handler" curr.name)
              (available:
                if available then bind curr.comp (result: pure (acc // { ${curr.name} = result; }))
                else pure acc
              )
          else
            bind curr.comp (result: pure (acc // { ${curr.name} = result; }))
        ))
      (pure { })
      (map toComp names);

  bindComp = attrs: f:
    let
      # Translate lib.functionArgs's bool output into bindAttrs sentinels:
      #   true  (has default)  -> optionalArg (probe + skip if no handler)
      #   false (required)     -> false (sent literally as the param)
      # User-supplied attrs win via // override.
      fnArgs = lib.functionArgs f;
      translated = lib.mapAttrs
        (_: hasDefault:
          if hasDefault then optionalArg else false)
        fnArgs;
    in
    bind (bindAttrs (translated // attrs)) f;

  bindFn = attrs: f:
    bindComp attrs {
      __functionArgs = lib.functionArgs f;
      __functor = _: args: pure (f args);
    };

in
api.namespace {
  description = "Idiomatic Nix bind helpers: `bindAttrs`/`bindComp`/`bindFn` lift attrset/function shapes into effect chains; `optionalArg` marks attrs as handler-conditional.";
  doc = "Idiomatic Nix bind helpers: `bindAttrs`, `bindComp`, `bindFn`, plus the `optionalArg` sentinel.";
  value = {
    bindAttrs = api.leaf {
      value = bindAttrs;
      description = "bindAttrs: sequence an attrset of effectful or send-able values; non-computation values become `send name value`, `optionalArg` probes via `has-handler` first.";
      signature = "bindAttrs : { <name> = Computation a | OptionalArg | Param; __sort? = [String] -> [String] } -> Computation { <name> = a }";
      doc = ''
        Like a bind-chain but operates over named attrset of required-effects.

        ```nix
        bind.attrs { foo = 99; bar = pure 22; baz = asks (env: env.baz); }
        ```

        Values that are non-effects become send params: `send "foo" 99`.
        Pass the `optionalArg` sentinel to mark a key as optional: bindAttrs
        probes via `has-handler` first and omits the key when no handler is
        installed (so a Nix function's default value can take over).

        Result has same attr-keys with corresponding effect result.

        See also: `bind.comp`, `bind.fn` for which this is the foundation.

        # NOTE: Ordering of chained effects.

        Since an attrSet has no order, this function chains effects in
        same order as `builtins.attrNames` (alphabetical). If you need
        an special order for computations that might be order senstive,
        specify a `__sort = names => names` function.
      '';
      tests = {
        pure-passes-thru = {
          expr = (bindAttrs { foo = pure 22; }).value;
          expected.foo = 22;
        };
        impure-passes-thru = {
          expr = (bindAttrs { foo = (bind (pure 22) (x: pure (x + 1))); }).value;
          expected.foo = 23;
        };
        non-effect-is-send = {
          expr =
            let
              eff = bindAttrs { foo = 22; bar = pure 99; };
              result = fx.trampoline.run eff
                {
                  foo = { param, state }: {
                    resume = param * 2;
                    state = state;
                  };
                }
                null;
            in
            result.value;
          expected = {
            foo = 44;
            bar = 99;
          };
        };
        sorted-send = {
          expr =
            let
              eff = bindAttrs { foo = null; bar = null; __sort = _: [ "bar" "foo" ]; };
              result = fx.trampoline.run eff
                {
                  foo = { param, state }: {
                    resume = param;
                    state = state * 2;
                  };
                  bar = { param, state }: {
                    resume = param;
                    state = state + 1;
                  };
                } 11;
            in
            result.state;
          expected = 24;
        };
        # Plain `true` is a value, not an optionality marker. bindAttrs sends
        # it as the param: handlers receive the literal true. With no handler,
        # the effect is unhandled and the trampoline throws — same as any
        # other required send.
        true-is-send-param-not-optional = {
          expr =
            let
              eff = bindAttrs { x = true; };
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = param; inherit state; };
                }
                null;
            in
            result.value.x;
          expected = true;
        };
        true-throws-when-handler-missing = {
          expr =
            let
              eff = bindAttrs { x = true; };
            in
            (builtins.tryEval (fx.trampoline.run eff { } null).value).success;
          expected = false;
        };
        # Optionality is requested explicitly via the optionalArg sentinel.
        # No handler → key is omitted from the result.
        optionalArg-omitted-when-handler-missing = {
          expr =
            let
              eff = bindAttrs { x = optionalArg; };
              caught = builtins.tryEval (fx.trampoline.run eff { } null).value;
            in
            caught.success && caught.value == { };
          expected = true;
        };
        optionalArg-resolved-when-handler-exists = {
          expr =
            let
              eff = bindAttrs { x = optionalArg; };
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = 42; inherit state; };
                }
                null;
            in
            result.value.x;
          expected = 42;
        };
      };
    };

    bindComp = api.leaf {
      value = bindComp;
      description = "bindComp: turn an effectful function into an effect chain via `bindAttrs`; required args become required sends, optional args (with Nix defaults) probe via `has-handler`.";
      signature = "bindComp : { <name> = Computation a | Param } -> ({ <args> }: Computation b) -> Computation b";
      doc = ''
        Turns a Nix effectful function into an effect chain via bindAttrs.

        ```nix
        bindComp { bar = pure 22; } ({ foo, bar }: pure (foo * bar))
        ```

        The function sees bar as the result of `pure 22` and `foo` as the
        result of `send "foo" false` -- false comes directly from using
        `lib.functionArgs f`, the handler can know if "foo" is optional in f.

        Optional args (those with defaults in the Nix function) are probed
        via has-handler before sending. If no handler exists, the arg is
        skipped and the Nix default kicks in.

        This works by using `bindAttrs` on the intersection of function args
        and attrs.
      '';
      tests = {
        arg-in-attrs = {
          expr = (bindComp { x = pure 22; } ({ x }: pure (x * 2))).value;
          expected = 44;
        };
        arg-not-in-attrs-is-send = {
          expr =
            let
              eff = bindComp { } ({ foo }: pure (foo * 2));
              result = fx.trampoline.run eff
                {
                  foo = { param, state }: {
                    resume = 11;
                    state = state;
                  };
                }
                null;
            in
            result.value;
          expected = 22;
        };
        optional-arg-skipped-when-no-handler = {
          expr =
            let
              eff = bindComp { } ({ x, y ? 99 }: pure (x + y));
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = 1; inherit state; };
                  # no handler for y — optional, so Nix default (99) is used
                }
                null;
            in
            result.value;
          expected = 100;
        };
        optional-arg-resolved-when-handler-exists = {
          expr =
            let
              eff = bindComp { } ({ x, y ? 99 }: pure (x + y));
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = 1; inherit state; };
                  y = { param, state }: { resume = 2; inherit state; };
                }
                null;
            in
            result.value;
          expected = 3;
        };
      };
    };

    bindFn = api.leaf {
      value = bindFn;
      description = "bindFn: like `bindComp` but for pure Nix functions; lifts the function's result into `pure` while still resolving its arguments through the effect system.";
      signature = "bindFn : { <name> = Computation a | Param } -> ({ <args> }: b) -> Computation b";
      doc = ''
        Like bindComp but works on normal Nix functions and turns
        its result into a pure-effect.

        ```nix
        bindFn { bar = pure 22; } ({ foo, bar }: foo * bar)
        ```

      '';
      tests = {
        arg-in-attrs = {
          expr = (bindFn { x = pure 22; } ({ x }: x * 2)).value;
          expected = 44;
        };
        arg-not-in-attrs-is-send = {
          expr =
            let
              eff = bindFn { } ({ foo }: foo * 2);
              result = fx.trampoline.run eff
                {
                  foo = { param, state }: {
                    resume = 11;
                    state = state;
                  };
                }
                null;
            in
            result.value;
          expected = 22;
        };
        optional-arg-skipped-when-no-handler = {
          expr =
            let
              eff = bindFn { } ({ x, y ? 99 }: x + y);
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = 1; inherit state; };
                }
                null;
            in
            result.value;
          expected = 100;
        };
        optional-arg-resolved-when-handler-exists = {
          expr =
            let
              eff = bindFn { } ({ x, y ? 99 }: x + y);
              result = fx.trampoline.run eff
                {
                  x = { param, state }: { resume = 1; inherit state; };
                  y = { param, state }: { resume = 2; inherit state; };
                }
                null;
            in
            result.value;
          expected = 3;
        };
      };
    };

    optionalArg = api.leaf {
      value = optionalArg;
      description = "optionalArg: sentinel for `bindAttrs`/`bindComp` optional effect arguments; absent handlers omit the attr so Nix defaults can apply.";
      signature = "optionalArg : OptionalArg";
      doc = "Sentinel value marking an attr as handler-conditional in `bindAttrs`.";
    };
  };
}
