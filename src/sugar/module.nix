# Opt-in syntax-livability layer. Nothing in the kernel imports this.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.sugar: opt-in syntax layer for the effect substrate — do, /, steps, letM, with, wrap — that compiles down to plain bind/pure/send.";
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
