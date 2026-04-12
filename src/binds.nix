# nix-effects bind: Idiomatic Nix bind helpers.
#
#
# - bind.attrs: Binds effectful attributeSet values
# - bind.comp: Binds effectful function args.
# - bind.fn: Binds pure Nix function args.
#
{ fx, api, lib, ... }:
let

  inherit (fx.comp) pure isComp;
  inherit (fx.kernel) bind send;
  inherit (api) mk;

  bindAttrs' = attrs:
    let
      skip = n: !builtins.elem n [ "__sort" "__functor" "__functionArgs" ];
      clean = builtins.filter skip (builtins.attrNames attrs);
      sort = attrs.__sort or lib.id;
      names = sort clean;
      toComp = name:
        let value = attrs.${name}; in
        if isComp value
        then { inherit name value; }
        else { inherit name; value = send name value; };
    in
    builtins.foldl'
    (prev: curr: bind prev (acc: bind curr.value (result: pure (acc // { ${curr.name} = result; }))))
    (pure {})
    (map toComp names);

  bindAttrs = mk {
    doc = ''
    Like a bind-chain but operates over named attrset of required-effects.

    ```nix
    bind.attrs { foo = 99; bar = pure 22; baz = asks (env: env.baz); }
    ```

    Values that are non-effects become send params: `send "foo" 99`.

    Result has same attr-keys with corresponding effect result.

    See also: `bind.comp`, `bind.fn` for which this is the foundation.

    # NOTE: Ordering of chained effects.

    Since an attrSet has no order, this function chains effects in
    same order as `builtins.attrNames` (alphabetical). If you need
    an special order for computations that might be order senstive,
    specify a `__sort = names => names` function.
    '';
    value = bindAttrs';
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
        expr = let
          eff = bindAttrs { foo = 22; bar = pure 99; };
          result = fx.trampoline.run eff {
            foo = { param, state }: {
              resume = param * 2;
              state = state;
            };
          } null;
        in result.value;
        expected = {
          foo = 44;
          bar = 99;
        };
      };
      sorted-send = {
        expr = let
          eff = bindAttrs { foo = null; bar = null; __sort = _: [ "bar" "foo" ]; };
          result = fx.trampoline.run eff {
            foo = { param, state }: {
              resume = param;
              state = state * 2;
            };
            bar = { param, state }: {
              resume = param;
              state = state + 1;
            };
          } 11;
        in result.state;
        expected = 24;
      };
    };
  };

  bindComp = mk {
    doc = ''
    Turns a Nix effectful function into an effect chain via bindAttrs.

    ```nix
    bindComp { bar = pure 22; } ({ foo, bar }: pure (foo * bar))
    ```

    The function sees bar as the result of `pure 22` and `foo` as the
    result of `send "foo" false` -- false comes directly from using 
    `lib.functionArgs f`, the handler can know if "foo" is optional in f.

    This works by using `bindAttrs` on the intersection of function args
    and attrs.
    '';
    value = attrs: f:
      bind (bindAttrs ((lib.functionArgs f) // attrs)) f;
    tests = {
      arg-in-attrs = {
        expr = (bindComp { x = pure 22; } ({ x }: pure (x * 2))).value;
        expected = 44;
      };
      arg-not-in-attrs-is-send = {
        expr = let
         eff = bindComp { } ({ foo }: pure (foo * 2));
         result = fx.trampoline.run eff {
          foo = { param, state }: {
            resume = 11;
            state = state;
          };
         } null;
        in result.value;
        expected = 22;
      };
    };
  };

  bindFn = mk {
    doc = ''
    Like bindComp but works on normal Nix functions and turns
    its result into a pure-effect.

    ```nix
    bindFn { bar = pure 22; } ({ foo, bar }: foo * bar)
    ```

    '';
    value = attrs: f: 
      bindComp attrs {
        __functionArgs = lib.functionArgs f;
        __functor = _: args: pure (f args);
      };
    tests = {
      arg-in-attrs = {
        expr = (bindFn { x = pure 22; } ({ x }: x * 2)).value;
        expected = 44;
      };
      arg-not-in-attrs-is-send = {
        expr = let
         eff = bindFn { } ({ foo }: foo * 2);
         result = fx.trampoline.run eff {
          foo = { param, state }: {
            resume = 11;
            state = state;
          };
         } null;
        in result.value;
        expected = 22;
      };
    };
  };

in mk {
  doc = "Idiomatic Nix bind helpers";
  value = {
    inherit bindAttrs bindComp bindFn;
  };
}
