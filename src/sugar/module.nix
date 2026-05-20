# Opt-in syntax-livability layer. Nothing in the kernel imports this.
{ self, partTests, partDocs, api, ... }:

api.mkModule {
  inherit partDocs;
  doc = ''
    Opt-in syntax-livability layer for nix-effects.

    - `fx.sugar.do` / `fx.sugar.letM` — combinator forms
    - `fx.sugar.operators.__div` — `/` as reverse-apply (bind)
    - re-exports of `pure bind run handle map seq pipe kleisli`

    See `book/src/sugar.md` for the opt-in matrix and caveats.
  '';
  value = self;
  tests = partTests;
}
