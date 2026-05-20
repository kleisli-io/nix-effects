{ self, api, ... }:

api.mk {
  description = "fx.experimental.desc-interp: FreeFx as a μ-tree on HOAS descriptions — `kernel` provides pure/send/bind, `trampoline` runs programs via genericClosure.";
  doc = ''
    `desc.nix` encodes FreeFx as `plus pureSummand impureSummand`;
    continuations live in an FTCQueue value (Kiselyov & Ishii) rather
    than meta-level Nix functions. `kernel.nix` mirrors `fx.kernel`'s
    `pure`/`send`/`bind`; `bind` snocs into the Impure summand's
    queue without recursing on the μ-tree. `trampoline.nix` drives
    programs via `builtins.genericClosure` at O(1) host stack depth.

    ## Handler shortcut layering

    Each canonical handler op admits a partial-evaluation residual
    that bypasses kernel `vApp` per Impure step. Soundness splits:

    - **kernel-side** (`effects/*-shortcut-laws.nix`): `H.refl` lemma
      `handle_X op s ≡_kernel mkResumeAt … r s` (resp. `mkAbortAt`)
      certifying the per-op rewrite under ι+β.
    - **emitter-side** (`extract.nix`): per-primitive Val-conv test
      `eval (HOAS witness) ≡_Val extract (Primitive …)`. Sugars
      (`Resume`/`Abort`/`PairRaw`) fold into primitives.
    - **composed-side** (`compose.nix` + `composed-shortcut.nix` +
      `composed-shortcut-laws.nix`): `composeHandlers` over UniRet
      closes the algebra under `+`. Six lemmas chain
      `composeHandlersInl/InrLemma` with per-effect uniform-shortcut
      lemmas; `composedHandlerShortcut` mirrors the kernel-composed
      path by direct Val construction.

    ## Adding a new effect with a handler shortcut

    Recipe — apply in order:

    1. **Identify canonical RHS shapes.** Reduce `handle_X op s` per
       constructor via ι+β. Each canonical op should normalise to
       `mkResumeAt … r s` or `mkAbortAt … v s` (or a bare `H.pair _
       _` outside the UniRet shape).

    2. **Extend `extract.nix` only if needed.** Existing sugars cover
       the UniRet and bare-pair shapes; primitives (`DescCon`,
       `BootInl`, `BootInr`, `Pair`, `Tt`, `BootRefl`) suffice for
       anything else. Add a sugar only when a non-trivial shape
       repeats across multiple effects.

    3. **Write `effects/x-shortcut-laws.nix`.** One `H.refl` lemma per
       canonical op asserting `handle_X op s ≡_kernel mkXAt …`.
       Mirror `effects/state-shortcut-laws.nix`'s `withPrefix`/
       `lamPrefix` helper layout. If `uniformOf_X` differs from
       `handle_X` (error's three strategies), add
       `effects/x-uniform-shortcut-laws.nix` too.

    4. **Wire `handlerShortcut` in `atType`.** Pre-compute metadata
       Vals (`leftSig`, `rightSig`, `sumDescVal`) once per
       instantiation; in `handlerShortcut op stateVal`, dispatch on
       `op._opTag` and return `extract (Resume …)` /
       `extract (Abort …)` / `extract (PairRaw …)`. Smart
       constructors tag canonical ops via `_opTag = "<effect>-<op>"`.
       If `uniformOf_X` is needed for composition, expose
       `uniformOfShort` (or `uniformOfShortAt A` if A varies
       post-`atType`).

    5. **Add parity tests in `trampoline.nix`.** For each canonical
       op, compare `runX { handler; dispatch; }` vs
       `runX { handler; dispatch; handlerShortcut; }` via
       `fx.tc.conv.conv 0` on both `.value` and `.state`. For ops
       that abort with a Nix throw (strict-style), force `.state.tag`
       under `builtins.tryEval` and assert both paths trip the throw.

    Composition with another effect via `composeHandlers` reuses the
    per-effect `uniformOfShort` plus `composedHandlerShortcut H_short_A
    H_short_B metaFor`; soundness is anchored kernel-side by
    `composed-shortcut-laws.nix` without any per-effect-pair work.
  '';
  value = {
    inherit (self) compat compose desc extract kernel trampoline;
    "compose-laws" = self."compose-laws";
    "composed-shortcut" = self."composed-shortcut";
    "composed-shortcut-laws" = self."composed-shortcut-laws";
    "descind-laws" = self."descind-laws";
    effects = self.effects;
  };
}
