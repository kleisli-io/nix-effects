# Elaboration core: type elaboration, value elaboration, validation, and
# decision procedures.
#
# Bridges `fx.types` to the kernel term representation (de Bruijn `Tm`) via
# the HOAS surface combinator layer. `elaborateType` maps an `fx.types`
# descriptor to an HOAS type tree; `elaborateValue` is the strict-handler
# bridge over `fx.tc.generic.check.deriveElaborate`; `validateValue` is the
# collecting-handler bridge over `fx.tc.generic.check.deriveCheck`;
# `decide`/`decideType` package the pipeline as a Bool;
# `extract`/`verifyAndExtract` close the reverse direction through
# `self.extractInner`.
#
# `elaborateValue` and `validateValue` are not separate dispatchers — they are
# the same polymorphic fold (`deriveGo` in `fx.tc.generic.check`) instantiated
# at two carriers (Hoas and Unit respectively) and threaded through two
# handler choices (strict and collecting). The canonical functor lives in
# `tc/generic/check.nix`; the modules here are thin handler-bridges.
#
# elaborateType dispatches on:
#   1. `_kernel` field (types built via `mkType` with `kernelType`)
#   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
#   3. Name convention (Bool, Nat, Unit, Null, String, Int, Float, ...)
#
# extract threads the kernel type value through every recursion site,
# computing dependent codomain/snd via closure instantiation rather than
# sentinel tests.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  V = fx.tc.value;

  # -- Detection predicates for fx.types structural dispatch --

  # Pi types carry domain, codomain, checkAt from dependent.nix
  isPi = type:
    builtins.isAttrs type
    && type ? domain && type ? codomain && type ? checkAt;

  # Sigma types carry fstType, sndFamily, proj1 from dependent.nix
  isSigma = type:
    builtins.isAttrs type
    && type ? fstType && type ? sndFamily && type ? proj1;

  # Non-dependence test: call the family with two sentinels.
  # If result type names match, the family is constant.
  # LIMITATION: builtins.tryEval only catches `throw` and `assert false`.
  # A type family that triggers boolean coercion errors, cross-type comparison
  # errors, or missing attribute access on sentinels will crash Nix rather than
  # returning false from isConstantFamily. This is an inherent limitation of
  # Nix's error model — there is no general-purpose exception catching.
  _s1 = { _tag = "Type"; name = "__elab_sentinel_1__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  _s2 = { _tag = "Type"; name = "__elab_sentinel_2__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  isConstantFamily = fn:
    let
      r1 = builtins.tryEval (fn _s1);
      r2 = builtins.tryEval (fn _s2);
    in
    r1.success && r2.success && r1.value.name == r2.value.name;
in
{
  scope = {
    elaborateType = api.leaf {
      value = type:
        if !(builtins.isAttrs type) then
          throw "elaborateType: expected a type attrset"
        else if type ? prove then type._kernel
        else if isPi type then
          if isConstantFamily type.codomain
          then H.forall "x" (self.elaborateType type.domain) (_: self.elaborateType (type.codomain _s1))
          else throw "elaborateType: dependent Pi requires _kernel annotation"
        else if isSigma type then
          if isConstantFamily type.sndFamily
          then H.sigma "x" (self.elaborateType type.fstType) (_: self.elaborateType (type.sndFamily _s1))
          else throw "elaborateType: dependent Sigma requires _kernel annotation"
        else if type.name == "Bool" then H.bool
        else if type.name == "Nat" then H.nat
        else if type.name == "Unit" || type.name == "Null" then H.unit
        else if type.name == "String" then H.string
        else if type.name == "Int" then H.int_
        else if type.name == "Float" then H.float_
        else if type.name == "Attrs" then H.attrs
        else if type.name == "Path" then H.path
        else if type.name == "Function" then H.function_
        else if type.name == "Any" then H.any
        else throw "elaborateType: cannot elaborate '${type.name}' (add _kernel annotation)";
      description = "elaborateType: convert an `fx.types` type descriptor to an HOAS type tree — dispatches on `_kernel` annotation, structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily), then name convention (Bool, Nat, Unit, ...). Dependent Pi/Sigma require explicit `_kernel`.";
      signature = "elaborateType : FxType -> Hoas";
      doc = ''
        Three dispatch tiers, tried in order:

        1. `_kernel` annotation: returned directly. This is the
           authoritative path for types built via `mkType` with an
           explicit `kernelType` (covers refinement, dependent, linear,
           levitated descriptions).
        2. Structural fields: `Pi { domain, codomain, checkAt }` →
           `H.forall`; `Sigma { fstType, sndFamily, proj1 }` →
           `H.sigma`. Only non-dependent families (constant-codomain /
           constant-sndFamily) are accepted at this tier — dependent
           families throw and demand the `_kernel` path.
        3. Name convention: primitives (`Bool`, `Nat`, `Unit`, `Null`,
           `String`, `Int`, `Float`, `Attrs`, `Path`, `Function`,
           `Any`) map to their HOAS prelude entries.

        Unknown types throw with a message directing the author to
        add `_kernel`. Cross-ref: `elaborateValue` for the dual on
        values, `decideType` for the boolean pipeline.
      '';
    };

    elaborateValue = api.leaf {
      value = hoasTy: value:
        (fx.trampoline.handle
          {
            handlers = fx.effects.typecheck.strict;
            state = null;
          }
          (fx.tc.generic.check.deriveElaborate hoasTy fx.tc.generic.path.empty value)).value;
      description = "elaborateValue: strict-handler bridge over `fx.tc.generic.check.deriveElaborate` — produces the HOAS term that witnesses the value's typing, throwing on the first shape mismatch (catchable by `tryEval`).";
      signature = "elaborateValue : Hoas -> NixVal -> Hoas";
      doc = ''
        Composes the canonical structural walker
        `fx.tc.generic.check.deriveElaborate` with the strict handler
        from `fx.effects.typecheck.strict`. The walker is the same fold
        as `validateValue` instantiated at carrier `Hoas`; the strict
        handler throws on the first emitted typeCheck failure.

        Per-tag construction is owned by the hoasAlg algebra inside
        `tc/generic/check.nix`: `Bool` → `true_`/`false_`; `Nat` →
        `natLit`; `String`/`Int`/`Float` → primitive literals; `List` →
        cons chain via an O(1)-per-step continuation accumulator; `Sum`
        → `inl`/`inr`; `Sigma` → `pair`; constructor records →
        prev-threaded `H.app` chain via `D.fieldType` (typeFn-aware for
        dependent fields).

        Fails fast on the first shape mismatch via `builtins.throw`.
        Soundness invariant: `validateValue [] hoasTy v` is `[]` iff
        `elaborateValue hoasTy v` does not throw on the same input.
      '';
    };

    validateValue = api.leaf {
      value = path: hoasTy: value:
        (fx.trampoline.handle
          {
            handlers = fx.effects.typecheck.collecting;
            state = [ ];
          }
          (fx.tc.generic.check.deriveCheck hoasTy path value)).state;
      description = "validateValue: collecting-handler bridge over `fx.tc.generic.check.deriveCheck` — accumulates every `typeCheck` effect emission produced by the canonical structural validator.";
      signature = "validateValue : Path -> Hoas -> NixVal -> [{ type; context; value; path; reason; }]";
      doc = ''
        Composes the canonical structural validator
        `fx.tc.generic.check.deriveCheck` with the collecting handler
        from `fx.effects.typecheck.collecting` to accumulate every typed
        failure across the value tree.

        The path argument is a structured Position list from
        `fx.tc.generic.path` (alias of `fx.diag.positions`); each
        emitted error record carries the descent path to its failure
        site under `reason ∈ { shape-mismatch, missing-field,
        predicate-failed, deferred-pi }`.

        Returns `[]` iff `elaborateValue` would not throw on the same
        input. Use for upfront validation in build-time gates and
        structural diagnostics; use `elaborateValue` directly when only
        the elaborated value is needed.
      '';
    };

    extract = api.leaf {
      value = hoasTy: val:
        let tyVal = E.eval [ ] (H.elab hoasTy);
        in self.extractInner hoasTy tyVal val;
      description = "extract: kernel-value to Nix-value extraction — reverse of `elaborateValue`; computes the kernel type from the HOAS type once, then delegates to `extractInner` for the recursive walk with kernel type-value threading.";
      signature = "extract : Hoas -> Val -> NixValue";
    };

    # Val→HOAS lift via two-level-TT splice. `H.litVal` reflects the
    # carried closed Val into HOAS in O(1); the elaborator emits
    # `T.mkLitVal`, eval returns the Val verbatim. Replaces the prior
    # `H.embedTm (quote 0 val)` composition, whose `quote` walk was
    # O(size val) and caused quadratic blow-up in iterative bridge use.
    embedVal = api.leaf {
      value = val: H.litVal val;
      description = "embedVal: Val-to-HOAS lift — `embedVal v` reflects a closed kernel `Val` into HOAS via `H.litVal`; the elaborator emits `T.mkLitVal` and eval returns the value verbatim. O(1) regardless of value depth.";
      signature = "embedVal : Val -> Hoas";
      doc = ''
        Use when a kernel value needs to flow into a surrounding HOAS
        expression that will be re-elaborated and re-evaluated. The
        canonical example is an effect handler's response handed to a
        user continuation: the continuation receives a Val but wants to
        build further HOAS like `H.app H.succ response` for the next
        program fragment. Without the lift, `H.elab` recurses into the
        Val (which lacks `_htag`) and throws.

        Soundness: the splice rule `eval ρ (LitVal v) = v` discards the
        environment, so v must be closed (no free de Bruijn levels).
        The bridge guarantees this — values reaching the embed site
        are evaluation results of closed handler programs.

        Cost: O(1). The prior `H.embedTm (quote 0 v)` composition walked
        v structurally each call, producing quadratic blow-up in
        iterative bridge use (a chain of N `bind get (n: …embedVal n…)`
        steps quoted progressively deeper state Vals).

        Reference: two-level type theory splice (Kovács, "Staged
        Compilation with Two-Level Type Theory", POPL 2024;
        Annenkov–Capriotti–Kraus–Sattler 2019).
      '';
    };

    verifyAndExtract = api.leaf {
      value = hoasTy: hoasImpl:
        let
          checked = H.checkHoas hoasTy hoasImpl;
        in
        if checked ? error
        then throw "verifyAndExtract: type check failed"
        else
          let
            val = E.eval [ ] checked;
            tyVal = E.eval [ ] (H.elab hoasTy);
          in
          self.extractInner hoasTy tyVal val;
      description = "verifyAndExtract: full type-check + evaluate + extract pipeline — given an HOAS type and an HOAS implementation, type-check the impl against the type, evaluate to a kernel value, and extract to a Nix value; throws on type error.";
      signature = "verifyAndExtract : Hoas -> Hoas -> NixValue";
      doc = ''
        The canonical entry point for closing a verified-impl pipeline
        back to ordinary Nix data. Evaluates the term returned by
        `checkHoas` — not a fresh elaboration of the impl — so the
        extracted value is the one that was verified, with all metas
        (e.g. a polymorphic list's element type, solved only by
        checking against the expected type) already pinned. The kernel
        type value is the direct elaboration of `hoasTy`; `extractInner`
        reads descriptions through `descView`, which treats primitive
        and encoded shapes uniformly, so the type's representation need
        not match the checked term's.

        On type-check failure throws `"verifyAndExtract: type check
        failed"` — callers needing structured diagnostics should split
        the pipeline: `H.checkHoas` for the error attrset, then
        `extract`/`extractInner` only on success.
      '';
    };

    decide = api.leaf {
      value = hoasTy: value:
        let
          result = builtins.tryEval (
            let
              hoasVal = self.elaborateValue hoasTy value;
              checked = H.checkHoas hoasTy hoasVal;
            in
              !(checked ? error)
          );
        in
        result.success && result.value;
      description = "decide: boolean decision procedure — returns `true` iff `elaborateValue` succeeds and the kernel type-checker accepts the resulting HOAS value; `tryEval` catches all elaboration throws.";
      signature = "decide : Hoas -> NixVal -> Bool";
    };

    decideType = api.leaf {
      value = type: value:
        self.decide (self.elaborateType type) value;
      description = "decideType: `decide` lifted to `fx.types` descriptors — runs `elaborateType` then `decide`. Convenience for users working with `fx.types` rather than raw HOAS types.";
      signature = "decideType : FxType -> NixVal -> Bool";
    };
  };

  tests =
    let
      FP = fx.types.primitives;
      FC = fx.types.constructors;
      FD = fx.types.dependent;
      BoolT = FP.Bool;
      IntT = FP.Int;
      UnitT = FP.Unit;
      Arrow = domType: codType:
        FD.Pi {
          domain = domType;
          codomain = _: codType;
          universe =
            let a = domType.universe; b = codType.universe;
            in if a >= b then a else b;
        };
      Product = fstType: sndType:
        FD.Sigma {
          fst = fstType;
          snd = _: sndType;
          universe =
            let a = fstType.universe; b = sndType.universe;
            in if a >= b then a else b;
        };
      inherit (self) elaborateType elaborateValue validateValue
        extract reifyType verifyAndExtract embedVal decide decideType;
    in
    {
      # -- Type elaboration: _kernel dispatch --

      "elab-type-bool" = {
        expr = (elaborateType BoolT)._htag;
        expected = "mu";
      };
      "elab-type-int" = {
        expr = (elaborateType IntT)._htag;
        expected = "int";
      };
      "elab-type-unit" = {
        expr = (elaborateType UnitT)._htag;
        expected = "unit";
      };
      # `H.listOf` and `H.sum` elaborate to app-spines of the macro's
      # polymorphic `T`. The app form preserves `_dtypeMeta` on the
      # polyField head and the parameter HOAS as literal args, which
      # `elaborateValue`/`validateValue`/`extractInner` consume directly
      # via their "app" branches. At the value level the application
      # reduces to `VMu (listDesc A)` / `VMu (sumDesc A B)`; the Tm-level
      # shape is "app".
      "elab-type-list-int" = {
        expr = (elaborateType (FC.ListOf IntT))._htag;
        expected = "app";
      };
      "elab-type-list-bool" = {
        expr = (elaborateType (FC.ListOf BoolT))._htag;
        expected = "app";
      };
      "elab-type-either" = {
        # Either elaborates to the first-class variant form:
        # `{ _htag = "variant"; branches = [Left; Right]; }`.
        expr = (elaborateType (FC.Either IntT BoolT))._htag;
        expected = "variant";
      };
      "elab-type-arrow" = {
        expr = (elaborateType (Arrow IntT BoolT))._htag;
        expected = "pi";
      };
      "elab-type-product" = {
        expr = (elaborateType (Product IntT BoolT))._htag;
        expected = "sigma";
      };
      "elab-type-u0" = {
        expr = (elaborateType (fx.types.universe.typeAt 0))._htag;
        expected = "U";
      };

      # -- Type elaboration: structural auto-detection --

      # Structural: non-dependent Pi auto-detected
      "elab-type-auto-pi" = {
        expr =
          let
            piT = FD.Pi { domain = BoolT; codomain = _: IntT; universe = 0; };
          in
          (elaborateType piT)._htag;
        expected = "pi";
      };

      # Structural: non-dependent Sigma auto-detected
      "elab-type-auto-sigma" = {
        expr =
          let
            sigT = FD.Sigma { fst = BoolT; snd = _: IntT; universe = 0; };
          in
          (elaborateType sigT)._htag;
        expected = "sigma";
      };

      # Dependent Pi (codomain uses argument) REJECTED without _kernel
      "reject-elab-dependent-pi" = {
        expr =
          let
            depPi = FD.Pi { domain = BoolT; codomain = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
          in
          (builtins.tryEval (elaborateType depPi)).success;
        expected = false;
      };

      # Dependent Sigma (snd uses argument) REJECTED without _kernel
      "reject-elab-dependent-sigma" = {
        expr =
          let
            depSig = FD.Sigma { fst = BoolT; snd = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
          in
          (builtins.tryEval (elaborateType depSig)).success;
        expected = false;
      };

      # -- Value elaboration --

      "elab-val-true" = {
        expr = (H.elab (elaborateValue H.bool true)).tag;
        expected = "desc-con";
      };
      "elab-val-false" = {
        expr = (H.elab (elaborateValue H.bool false)).tag;
        expected = "desc-con";
      };
      "elab-val-zero" = {
        expr = let e = H.elab (elaborateValue H.nat 0); in "${e.tag}/${e.d.tag}";
        expected = "desc-con/boot-inl";
      };
      "elab-val-nat-3" = {
        expr = let e = H.elab (elaborateValue H.nat 3); in "${e.tag}/${e.d.tag}";
        expected = "desc-con/boot-inr";
      };
      "elab-val-unit" = {
        expr = (H.elab (elaborateValue H.unit null)).tag;
        expected = "tt";
      };
      "elab-val-nil" = {
        expr = let t = H.elab (elaborateValue (H.listOf H.nat) [ ]); in "${t.tag}/${t.d.tag}";
        expected = "desc-con/boot-inl";
      };
      "elab-val-cons" = {
        expr = let t = H.elab (elaborateValue (H.listOf H.nat) [ 0 1 ]); in "${t.tag}/${t.d.tag}";
        expected = "desc-con/boot-inr";
      };
      "elab-val-inl" = {
        expr = let t = H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 0; }); in
          "${t.tag}/${t.d.tag}";
        expected = "desc-con/boot-inl";
      };
      "elab-val-inr" = {
        expr = let t = H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; }); in
          "${t.tag}/${t.d.tag}";
        expected = "desc-con/boot-inr";
      };
      "elab-val-pair" = {
        expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; })).term.tag;
        expected = "pair";
      };

      "elab-val-sigma-pi-snd" = {
        expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool))) { fst = 0; snd = _: true; })).term.tag;
        expected = "pair";
      };

      # -- Decision procedure: positive --

      "decide-bool-true" = {
        expr = decide H.bool true;
        expected = true;
      };
      "decide-bool-false" = {
        expr = decide H.bool false;
        expected = true;
      };
      "decide-nat-0" = {
        expr = decide H.nat 0;
        expected = true;
      };
      "decide-nat-5" = {
        expr = decide H.nat 5;
        expected = true;
      };
      "decide-unit" = {
        expr = decide H.unit null;
        expected = true;
      };
      "decide-list-empty" = {
        expr = decide (H.listOf H.nat) [ ];
        expected = true;
      };
      "decide-list-nat" = {
        expr = decide (H.listOf H.nat) [ 0 1 2 ];
        expected = true;
      };
      "decide-sum-left" = {
        expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = 0; };
        expected = true;
      };
      "decide-sum-right" = {
        expr = decide (H.sum H.nat H.bool) { _tag = "Right"; value = true; };
        expected = true;
      };
      "decide-product" = {
        expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; };
        expected = true;
      };

      # -- Decision procedure: negative --

      "decide-bool-rejects-int" = {
        expr = decide H.bool 42;
        expected = false;
      };
      "decide-nat-rejects-neg" = {
        expr = decide H.nat (-1);
        expected = false;
      };
      "decide-nat-rejects-string" = {
        expr = decide H.nat "hello";
        expected = false;
      };
      "decide-list-rejects-wrong-elem" = {
        expr = decide (H.listOf H.nat) [ true ];
        expected = false;
      };
      "decide-sum-rejects-wrong-val" = {
        expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = true; };
        expected = false;
      };
      "decide-product-rejects-wrong-fst" = {
        expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = true; snd = true; };
        expected = false;
      };

      # -- Decision procedure: record totality --

      "decide-record-rejects-missing-field" = {
        expr = decide (H.record [{ name = "n"; type = H.int_; }]) { x = 1; };
        expected = false;
      };
      "decide-record-rejects-non-attrset" = {
        expr = decide (H.record [{ name = "n"; type = H.int_; }]) 42;
        expected = false;
      };
      "decide-record-rejects-partial-fields" = {
        expr = decide (H.record [{ name = "a"; type = H.int_; } { name = "b"; type = H.bool; }]) { a = 1; };
        expected = false;
      };
      "decide-record-accepts-complete" = {
        expr = decide (H.record [{ name = "a"; type = H.int_; } { name = "b"; type = H.bool; }]) { a = 1; b = true; };
        expected = true;
      };

      # Stack safety: full pipeline (elaborate → eval → check) trampolined for cons.
      # Elements are all `0` (Peano depth 1) to isolate the cons-chain stressor —
      # matches the convention of the four sibling "5000" stress tests in
      # hoas/check/conv/quote. Under μnatDesc, `natLit k` is O(k) Peano depth by
      # design, so varying-magnitude elements would conflate two orthogonal
      # stressors. See `decide-nat-1000` below for the dedicated Peano-depth test.
      "decide-list-5000" = {
        expr = decide (H.listOf H.nat) (builtins.genList (_: 0) 5000);
        expected = true;
      };

      # Names the shared-D fast path on the desc-con trampoline: H.cons
      # emits a single dTm at elab time, so node.D == tm.D is structural-
      # equal across layers and the peel short-circuits before reaching
      # the conv-equality fallback.
      "decide-list-5000-shared-d" = {
        expr = decide (H.listOf H.nat) (builtins.genList (_: 0) 5000);
        expected = true;
      };

      # Stack safety: full pipeline on a deep Peano literal. Under μnatDesc
      # representation `natLit N` is an N-deep desc-con chain; this test exercises
      # the desc-con trampolines in elaborate/check/eval end-to-end. Bound chosen
      # so the test stays well under a second on commodity hardware — higher
      # bounds are meaningful but dominated by memory allocation, not correctness.
      "decide-nat-1000" = {
        expr = decide H.nat 1000;
        expected = true;
      };

      # 5000-element list via the macro-generated ListDT.cons rather than
      # H.cons. Each layer is a β-redex reducing to `desc-con D payload` at
      # eval time; the desc-con trampoline identifies shared D across layers
      # via conv-equality when structural == doesn't hold, and decomposes
      # each layer's payload using linearProfile on the cons-branch
      # description (Just [A], one head and a rec tail).
      "decide-list-5000-macro" = {
        expr =
          let
            L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
              let A = builtins.elemAt ps 0; in [
                (H.con "nil" [ ])
                (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
              ]);
            nilA = H.app L.nil H.nat;
            consA = h: t: H.app (H.app (H.app L.cons H.nat) h) t;
            build = builtins.foldl' (acc: _: consA H.zero acc)
              nilA
              (builtins.genList (x: x) 5000);
            hoasTy = H.app L.T H.nat;
            result = H.checkHoas hoasTy build;
          in
            !(result ? error);
        expected = true;
      };

      # 1000-deep Peano chain via the macro-generated NatDT.succ rather
      # than H.succ. Each constructor cascade β-reduces at eval time; the
      # desc-con trampoline peels via linearProfile at Just [] (0 data
      # fields, rec tail), matching the succ-branch description shape.
      "decide-nat-1000-macro" = {
        expr =
          let
            N = H.datatype "Nat" [
              (H.con "zero" [ ])
              (H.con "succ" [ (H.recField "pred") ])
            ];
            build = builtins.foldl' (acc: _: H.app N.succ acc)
              N.zero
              (builtins.genList (x: x) 1000);
            result = H.checkHoas N.T build;
          in
            !(result ? error);
        expected = true;
      };


      # Dependent sigma: body produces "eq" which elaborateValue can't handle
      "decide-dep-sigma-rejected" = {
        expr = decide (H.sigma "x" H.nat (x: H.eq H.nat x H.zero)) { fst = 0; snd = null; };
        expected = false;
      };

      # -- HOAS substitution: dependent Sigma via body(fstHoas) --

      # Non-dependent Sigma: HOAS substitution produces same result as before
      "elab-dep-sigma-non-dep-baseline" = {
        expr =
          let
            ty = H.sigma "x" H.nat (_: H.bool);
            val = { fst = 0; snd = true; };
          in
          (H.elab (elaborateValue ty val)).term.tag;
        expected = "pair";
      };

      # Dependent Sigma whose body produces an elaboratable type
      "elab-dep-sigma-snd-type-correct" = {
        expr =
          let
            # Sigma(x: Bool). if x then Nat else Bool
            # body(true_) = Nat, so snd = 42 should elaborate as Nat
            ty = H.sigma "x" H.bool (x:
              let t = (H.elab x).tag; in
              if t == "true" then H.nat
              else if t == "false" then H.bool
              else H.nat);
            val = { fst = true; snd = 42; };
          in
          (H.elab (elaborateValue ty val)).term.tag;
        expected = "pair";
      };

      # Dependent Sigma kernel-checks: elaborated pair passes checkHoas
      "elab-dep-sigma-kernel-checks" = {
        expr =
          let
            ty = H.sigma "x" H.bool (x:
              let t = (H.elab x).tag; in
              if t == "true" then H.nat
              else if t == "false" then H.bool
              else H.nat);
            val = { fst = true; snd = 42; };
            hoasVal = elaborateValue ty val;
            checked = H.checkHoas ty hoasVal;
          in
            !(checked ? error);
        expected = true;
      };

      # Dependent Sigma roundtrip: elaborate -> check -> eval -> extract = original
      "elab-dep-sigma-roundtrip" = {
        expr =
          let
            ty = H.sigma "x" H.nat (_: H.bool);
            val = { fst = 5; snd = true; };
          in
          extract ty (E.eval [ ] (H.elab (elaborateValue ty val)));
        expected = { fst = 5; snd = true; };
      };

      # Dependent Sigma: wrong snd type rejected via substituted body
      "elab-dep-sigma-snd-mismatch" = {
        expr =
          let
            ty = H.sigma "x" H.bool (x:
              let
                e = H.elab x;
                dt = if e.tag == "desc-con" && e ? d then e.d.tag else null;
              in
              if dt == "boot-inl" then H.nat
              else H.bool);
            # fst=true means snd should be Nat, but we pass a bool
            val = { fst = true; snd = false; };
          in
          decide ty val;
        expected = false;
      };

      # validateValue: dependent Sigma validates correctly
      "validate-dep-sigma-valid" = {
        expr =
          let
            ty = H.sigma "x" H.bool (x:
              let
                e = H.elab x;
                dt = if e.tag == "desc-con" && e ? d then e.d.tag else null;
              in
              if dt == "boot-inl" then H.nat
              else H.bool);
            val = { fst = true; snd = 42; };
          in
          validateValue [ ] ty val;
        expected = [ ];
      };

      # validateValue: dependent Sigma reports snd errors
      "validate-dep-sigma-snd-error" = {
        expr =
          let
            ty = H.sigma "x" H.bool (x:
              let
                e = H.elab x;
                dt = if e.tag == "desc-con" && e ? d then e.d.tag else null;
              in
              if dt == "boot-inl" then H.nat
              else H.bool);
            # fst=true → snd should be Nat, but we pass a string
            val = { fst = true; snd = "wrong"; };
            errors = validateValue [ ] ty val;
          in
          builtins.length errors > 0;
        expected = true;
      };

      # -- Pi opaque elaboration: function values at Pi types --

      # Raw Nix function at Pi type → opaque lambda
      "elab-pi-opaque-lambda" = {
        expr =
          let
            ty = H.forall "x" H.nat (_: H.bool);
            hoasVal = elaborateValue ty (x: x > 0);
          in
          (H.elab hoasVal).tag;
        expected = "opaque-lam";
      };

      # Verified value with _hoasImpl → uses HOAS term directly
      "elab-pi-verified-uses-hoasImpl" = {
        expr =
          let
            ty = H.forall "x" H.nat (_: H.nat);
            verified = { _hoasImpl = H.lam "x" H.nat (x: x); __functor = self: x: x; };
            hoasVal = elaborateValue ty verified;
          in
          (H.elab hoasVal).tag;
        expected = "lam";
      };

      # Opaque lambda at Pi type → kernel check passes (domain matches)
      "elab-pi-domain-check" = {
        expr =
          let
            ty = H.forall "x" H.nat (_: H.bool);
            hoasVal = elaborateValue ty (x: x > 0);
            checked = H.checkHoas ty hoasVal;
          in
            !(checked ? error);
        expected = true;
      };

      # Function at wrong Pi domain → kernel check fails
      "elab-pi-domain-mismatch" = {
        expr =
          let
            ty = H.forall "x" H.nat (_: H.bool);
            wrongTy = H.forall "x" H.bool (_: H.bool);
            hoasVal = elaborateValue wrongTy (x: x);
            # Check against nat-domain Pi, but elaborated against bool-domain Pi
            checked = H.checkHoas ty hoasVal;
          in
          checked ? error;
        expected = true;
      };

      # Non-function value at Pi type → throws
      "elab-pi-non-function-rejects" = {
        expr = (builtins.tryEval (elaborateValue (H.forall "x" H.nat (_: H.nat)) 42)).success;
        expected = false;
      };

      # Opaque Pi roundtrip: elaborate → eval → extract = original function
      "extract-opaque-pi-roundtrip" = {
        expr =
          let
            ty = H.forall "x" H.nat (_: H.nat);
            f = x: x + 1;
            hoasVal = elaborateValue ty f;
            val = E.eval [ ] (H.elab hoasVal);
            extracted = extract ty val;
          in
          extracted 5;
        expected = 6;
      };

      # decide returns true for valid Pi function
      "decide-pi-with-kernel-accepts" = {
        expr = decide (H.forall "x" H.nat (_: H.bool)) (x: x > 0);
        expected = true;
      };

      # decide rejects non-function at Pi type
      "decide-pi-rejects-non-function" = {
        expr = decide (H.forall "x" H.nat (_: H.nat)) 42;
        expected = false;
      };

      # validateValue: Pi accepts function
      "validate-pi-accepts-function" = {
        expr = validateValue [ ] (H.forall "x" H.nat (_: H.nat)) (x: x + 1);
        expected = [ ];
      };

      # validateValue: Pi rejects non-function
      "validate-pi-rejects-non-function" = {
        expr = builtins.length (validateValue [ ] (H.forall "x" H.nat (_: H.nat)) 42) > 0;
        expected = true;
      };

      # -- Regression: decide(T,v) == T.check(v) --

      "regression-bool-true" = {
        expr = (decideType BoolT true) == (BoolT.check true);
        expected = true;
      };
      "regression-bool-rejects-int" = {
        expr = (decideType BoolT 42) == (BoolT.check 42);
        expected = true;
      };
      "regression-int-42" = {
        expr = (decideType IntT 42) == (IntT.check 42);
        expected = true;
      };
      "regression-int-rejects-string" = {
        expr = (decideType IntT "x") == (IntT.check "x");
        expected = true;
      };
      "regression-unit-null" = {
        expr = (decideType UnitT null) == (UnitT.check null);
        expected = true;
      };
      "regression-unit-rejects-42" = {
        expr = (decideType UnitT 42) == (UnitT.check 42);
        expected = true;
      };
      "regression-list-int-valid" = {
        expr = let lt = FC.ListOf IntT; in (decideType lt [ 0 1 2 ]) == (lt.check [ 0 1 2 ]);
        expected = true;
      };
      "regression-list-int-empty" = {
        expr = let lt = FC.ListOf IntT; in (decideType lt [ ]) == (lt.check [ ]);
        expected = true;
      };
      "regression-list-int-rejects-bad" = {
        expr = let lt = FC.ListOf IntT; in (decideType lt [ true ]) == (lt.check [ true ]);
        expected = true;
      };
      "regression-either-left-valid" = {
        expr =
          let et = FC.Either IntT BoolT; v = { _tag = "Left"; value = 0; };
          in (decideType et v) == (et.check v);
        expected = true;
      };
      "regression-either-right-bad" = {
        expr =
          let et = FC.Either IntT BoolT; v = { _tag = "Right"; value = 42; };
          in (decideType et v) == (et.check v);
        expected = true;
      };
      "regression-product-valid" = {
        expr =
          let pt = Product IntT BoolT; v = { fst = 0; snd = true; };
          in (decideType pt v) == (pt.check v);
        expected = true;
      };
      "regression-product-bad-fst" = {
        expr =
          let pt = Product IntT BoolT; v = { fst = true; snd = true; };
          in (decideType pt v) == (pt.check v);
        expected = true;
      };

      # -- Primitive type elaboration: name-based auto-detection --

      "elab-type-auto-string" = {
        expr = (elaborateType FP.String)._htag;
        expected = "string";
      };
      "elab-type-auto-int" = {
        expr = (elaborateType FP.Int)._htag;
        expected = "int";
      };
      "elab-type-auto-float" = {
        expr = (elaborateType FP.Float)._htag;
        expected = "float";
      };
      "elab-type-auto-attrs" = {
        expr = (elaborateType FP.Attrs)._htag;
        expected = "attrs";
      };
      "elab-type-auto-path" = {
        expr = (elaborateType FP.Path)._htag;
        expected = "path";
      };
      "elab-type-auto-function" = {
        expr = (elaborateType FP.Function)._htag;
        expected = "function";
      };
      "elab-type-auto-any" = {
        expr = (elaborateType FP.Any)._htag;
        expected = "any";
      };

      # -- Value elaboration: primitives --

      "elab-val-string" = {
        expr = (H.elab (elaborateValue H.string "hello")).tag;
        expected = "string-lit";
      };
      "elab-val-string-value" = {
        expr = (H.elab (elaborateValue H.string "hello")).value;
        expected = "hello";
      };
      "elab-val-int" = {
        expr = (H.elab (elaborateValue H.int_ 42)).tag;
        expected = "int-lit";
      };
      "elab-val-float" = {
        expr = (H.elab (elaborateValue H.float_ 3.14)).tag;
        expected = "float-lit";
      };
      "elab-val-attrs" = {
        expr = (H.elab (elaborateValue H.attrs { x = 1; })).tag;
        expected = "attrs-lit";
      };
      "elab-val-fn" = {
        expr = (H.elab (elaborateValue H.function_ (x: x))).tag;
        expected = "fn-lit";
      };
      "elab-val-any-string" = {
        expr = (H.elab (elaborateValue H.any "anything")).tag;
        expected = "any-lit";
      };
      "elab-val-any-int" = {
        expr = (H.elab (elaborateValue H.any 42)).tag;
        expected = "any-lit";
      };

      # -- Decision procedure: primitive positives --

      "decide-string-hello" = {
        expr = decide H.string "hello";
        expected = true;
      };
      "decide-string-empty" = {
        expr = decide H.string "";
        expected = true;
      };
      "decide-int-42" = {
        expr = decide H.int_ 42;
        expected = true;
      };
      "decide-int-neg" = {
        expr = decide H.int_ (-10);
        expected = true;
      };
      "decide-float-pi" = {
        expr = decide H.float_ 3.14;
        expected = true;
      };
      "decide-attrs-set" = {
        expr = decide H.attrs { x = 1; y = 2; };
        expected = true;
      };
      "decide-fn-id" = {
        expr = decide H.function_ (x: x);
        expected = true;
      };
      "decide-any-string" = {
        expr = decide H.any "anything";
        expected = true;
      };
      "decide-any-int" = {
        expr = decide H.any 42;
        expected = true;
      };
      "decide-any-null" = {
        expr = decide H.any null;
        expected = true;
      };

      # -- Decision procedure: primitive negatives --

      "decide-string-rejects-int" = {
        expr = decide H.string 42;
        expected = false;
      };
      "decide-int-rejects-string" = {
        expr = decide H.int_ "hello";
        expected = false;
      };
      "decide-float-rejects-int" = {
        expr = decide H.float_ 42;
        expected = false;
      };
      "decide-attrs-rejects-list" = {
        expr = decide H.attrs [ 1 2 ];
        expected = false;
      };
      "decide-fn-rejects-string" = {
        expr = decide H.function_ "hello";
        expected = false;
      };

      # -- Attrset value walker: tag dispatch, η-rule, _tag alias --

      "walker-eta-mono-record" = {
        # Single-constructor datatype accepts a raw attrset (η-rule).
        expr =
          let
            Box = H.datatype "Box" [
              (H.con "mk" [ (H.field "x" H.nat) (H.field "y" H.bool) ])
            ];
          in
          decide Box.T { x = 5; y = true; };
        expected = true;
      };

      "walker-multi-con-explicit-con-tag" = {
        expr =
          let
            MaybeNat = H.datatype "MaybeNat" [
              (H.con "Some" [ (H.field "v" H.nat) ])
              (H.con "None" [ ])
            ];
          in
          decide MaybeNat.T { _con = "Some"; v = 7; };
        expected = true;
      };

      "walker-multi-con-no-tag-rejected" = {
        # Multi-constructor datatype rejects ambiguous raw attrset (no
        # `_con` or `_tag` to disambiguate the constructor).
        expr =
          let
            MaybeNat = H.datatype "MaybeNat" [
              (H.con "Some" [ (H.field "v" H.nat) ])
              (H.con "None" [ ])
            ];
          in
          decide MaybeNat.T { v = 7; };
        expected = false;
      };

      "walker-sum-tag-alias" = {
        # Sum surface `{_tag; value;}` resolves the constructor via the
        # `_tag` alias for `_con`.
        expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = 3; };
        expected = true;
      };

      # -- Extraction: roundtrip tests --
      # Roundtrip: extract(T, eval(elab(elaborateValue(T, v)))) == v

      "extract-nat-0" = {
        expr = extract H.nat (E.eval [ ] (H.elab (elaborateValue H.nat 0)));
        expected = 0;
      };
      "extract-nat-5" = {
        expr = extract H.nat (E.eval [ ] (H.elab (elaborateValue H.nat 5)));
        expected = 5;
      };
      "extract-bool-true" = {
        expr = extract H.bool (E.eval [ ] (H.elab (elaborateValue H.bool true)));
        expected = true;
      };
      "extract-bool-false" = {
        expr = extract H.bool (E.eval [ ] (H.elab (elaborateValue H.bool false)));
        expected = false;
      };
      "extract-unit" = {
        expr = extract H.unit (E.eval [ ] (H.elab (elaborateValue H.unit null)));
        expected = null;
      };
      "extract-string" = {
        expr = extract H.string (E.eval [ ] (H.elab (elaborateValue H.string "hello")));
        expected = "hello";
      };
      "extract-int" = {
        expr = extract H.int_ (E.eval [ ] (H.elab (elaborateValue H.int_ 42)));
        expected = 42;
      };
      "extract-float" = {
        expr = extract H.float_ (E.eval [ ] (H.elab (elaborateValue H.float_ 3.14)));
        expected = 3.14;
      };
      "extract-list-empty" = {
        expr = extract (H.listOf H.nat) (E.eval [ ] (H.elab (elaborateValue (H.listOf H.nat) [ ])));
        expected = [ ];
      };
      "extract-list-nat" = {
        expr = extract (H.listOf H.nat) (E.eval [ ] (H.elab (elaborateValue (H.listOf H.nat) [ 1 2 3 ])));
        expected = [ 1 2 3 ];
      };
      "extract-sum-left" = {
        expr = extract (H.sum H.nat H.bool) (E.eval [ ] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 42; })));
        expected = { _tag = "Left"; value = 42; };
      };
      "extract-sum-right" = {
        expr = extract (H.sum H.nat H.bool) (E.eval [ ] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; })));
        expected = { _tag = "Right"; value = true; };
      };
      "extract-sigma" = {
        expr = let ty = H.sigma "x" H.nat (_: H.bool); in
          extract ty (E.eval [ ] (H.elab (elaborateValue ty { fst = 5; snd = true; })));
        expected = { fst = 5; snd = true; };
      };

      "extract-sigma-pi-snd" = {
        expr =
          let
            ty = H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool));
            hoasVal = H.pair (H.ann H.zero H.nat) (H.lam "y" H.nat (_: H.true_));
            val = E.eval [ ] (H.elab hoasVal);
            result = extract ty val;
          in
          (result.snd 0);
        expected = true;
      };

      # -- Extraction: Pi (verified function) --

      "extract-pi-identity" = {
        # Identity function: λ(x:Nat).x → extract → call with 5
        expr =
          let
            fnTy = H.forall "x" H.nat (_: H.nat);
            idFn = H.lam "x" H.nat (x: x);
            val = E.eval [ ] (H.elab idFn);
            nixFn = extract fnTy val;
          in
          nixFn 5;
        expected = 5;
      };
      "extract-pi-const" = {
        # Constant function: λ(x:Bool).0 → extract → call with true
        expr =
          let
            fnTy = H.forall "x" H.bool (_: H.nat);
            constFn = H.lam "x" H.bool (_: H.zero);
            val = E.eval [ ] (H.elab constFn);
            nixFn = extract fnTy val;
          in
          nixFn true;
        expected = 0;
      };

      # -- verifyAndExtract pipeline --

      "verify-extract-nat" = {
        expr = verifyAndExtract H.nat (H.natLit 7);
        expected = 7;
      };
      "verify-extract-bool" = {
        expr = verifyAndExtract H.bool H.true_;
        expected = true;
      };
      "verify-extract-fn" = {
        # Full pipeline: write function in HOAS → verify → extract → call
        expr =
          let
            fnTy = H.forall "x" H.nat (_: H.nat);
            fnImpl = H.lam "x" H.nat (x: x);
            nixFn = verifyAndExtract fnTy fnImpl;
          in
          nixFn 10;
        expected = 10;
      };
      "verify-extract-type-error" = {
        # Type error: Bool term against Nat type → throws
        expr = (builtins.tryEval (verifyAndExtract H.nat H.true_)).success;
        expected = false;
      };

      # -- embedVal: Val→HOAS lift round-trip --

      "embed-val-nat" = {
        # Read a Nat Val back to HOAS, re-elaborate, re-evaluate, extract.
        # The round-trip preserves the value.
        expr =
          let
            original = E.eval [ ] (H.elab (H.natLit 5));
            embedded = embedVal original;
            recovered = E.eval [ ] (H.elab embedded);
          in
          extract H.nat recovered;
        expected = 5;
      };
      "embed-val-bool" = {
        expr =
          let
            original = E.eval [ ] (H.elab H.true_);
            recovered = E.eval [ ] (H.elab (embedVal original));
          in
          extract H.bool recovered;
        expected = true;
      };
      "embed-val-composes-with-app" = {
        # A Val flowing into an HOAS app position. Without embedVal, the
        # term throws at elaborate because the Val lacks `_htag`. With
        # embedVal, the term elaborates and `succ` applies to it.
        # `H.succ` is itself a Nix wrapper for `H.app NatDT.succ`, so
        # write `H.succ x` not `H.app H.succ x`.
        expr =
          let
            original = E.eval [ ] (H.elab (H.natLit 2));
            composed = H.succ (embedVal original);
            v = E.eval [ ] (H.elab composed);
          in
          extract H.nat v;
        expected = 3;
      };
      "embed-val-under-binder" = {
        # Embedded Tm is closed, so safe to place under a binder.
        # `λ(_:Nat). succ embeddedTwo` applied to 99 returns 3.
        expr =
          let
            embeddedTwo = embedVal (E.eval [ ] (H.elab (H.natLit 2)));
            fn = H.lam "_" H.nat (_: H.succ embeddedTwo);
            nixFn = verifyAndExtract (H.forall "_" H.nat (_: H.nat)) fn;
          in
          nixFn 99;
        expected = 3;
      };
      "lit-val-elaborates-to-lit-val-tag" = {
        # H.litVal reflects a closed Val into HOAS; elaborate emits the
        # `lit-val` Tm tag.
        expr = (H.elab (H.litVal (E.eval [ ] (H.elab (H.natLit 3))))).tag;
        expected = "lit-val";
      };
      "lit-val-eval-is-identity" = {
        # `eval ρ (lit-val v) = v` independent of ρ. The Val that comes
        # back is the same VDescCon (succ-encoded 3), not a fresh Val.
        expr =
          let
            original = E.eval [ ] (H.elab (H.natLit 3));
            recovered = E.eval [ ] (H.elab (H.litVal original));
          in
          extract H.nat recovered;
        expected = 3;
      };

      # -- Extraction: stack safety --

      "extract-list-5000" = {
        # Stack safety: extract a 5000-element list (booleans for O(1) per element)
        expr = builtins.length (
          extract (H.listOf H.bool)
            (E.eval [ ] (H.elab (elaborateValue (H.listOf H.bool)
              (builtins.genList (_: true) 5000))))
        );
        expected = 5000;
      };

      # -- Extraction: opaque types throw --

      "extract-attrs-throws" = {
        expr = (builtins.tryEval (extract H.attrs (E.eval [ ] (H.elab (elaborateValue H.attrs { x = 1; }))))).success;
        expected = false;
      };
      "extract-fn-throws" = {
        expr = (builtins.tryEval (extract H.function_ (E.eval [ ] (H.elab (elaborateValue H.function_ (x: x)))))).success;
        expected = false;
      };

      # -- Extraction: macro-generated datatypes (mu-branch + app-branch) --
      # Macro-generated datatypes elaborate to HOAS types whose surface tag
      # is "mu" (monomorphic) or "app" (polymorphic instantiation). The
      # extractInner mu-branch detects prelude-equivalent shapes and routes
      # to the same Nix output as the nat/list/sum/bool/unit branches; other
      # shapes decompose generically into a constructor record `{ _con =
      # "<name>"; <field> = ...; }` using `_dtypeMeta` attached to the
      # macro's `T`. The app-branch peels the spine to the macro head,
      # recovers `_dtypeMeta`, and reduces the type via reifyType.

      "extract-mu-unit-tt" = {
        expr =
          let
            U = H.datatype "Unit" [ (H.con "tt" [ ]) ];
          in
          extract U.T (E.eval [ ] (H.elab U.tt));
        expected = null;
      };
      "extract-mu-bool-true" = {
        expr =
          let
            B = H.datatype "Bool" [ (H.con "true" [ ]) (H.con "false" [ ]) ];
          in
          extract B.T (E.eval [ ] (H.elab (builtins.getAttr "true" B)));
        expected = true;
      };
      "extract-mu-bool-false" = {
        expr =
          let
            B = H.datatype "Bool" [ (H.con "true" [ ]) (H.con "false" [ ]) ];
          in
          extract B.T (E.eval [ ] (H.elab (builtins.getAttr "false" B)));
        expected = false;
      };
      "extract-mu-nat-zero" = {
        expr =
          let
            N = H.datatype "Nat" [
              (H.con "zero" [ ])
              (H.con "succ" [ (H.recField "pred") ])
            ];
          in
          extract N.T (E.eval [ ] (H.elab N.zero));
        expected = 0;
      };
      "extract-mu-nat-3" = {
        expr =
          let
            N = H.datatype "Nat" [
              (H.con "zero" [ ])
              (H.con "succ" [ (H.recField "pred") ])
            ];
            three = H.app N.succ (H.app N.succ (H.app N.succ N.zero));
          in
          extract N.T (E.eval [ ] (H.elab three));
        expected = 3;
      };

      # Polymorphic via app: extract on `app (app ListDT.T nat)` peels the
      # app spine, recovers `_dtypeMeta` from the polyField head, and
      # delegates to the mu-branch with the reduced VMu kernel type.
      "extract-app-list-empty" = {
        expr =
          let
            L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
              let A = builtins.elemAt ps 0; in [
                (H.con "nil" [ ])
                (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
              ]);
            Tnat = H.app L.T H.nat;
            nilNat = H.app L.nil H.nat;
          in
          extract Tnat (E.eval [ ] (H.elab nilNat));
        expected = [ ];
      };
      "extract-app-list-3" = {
        expr =
          let
            L = H.datatypeP "List" [{ name = "A"; kind = H.u 0; }] (ps:
              let A = builtins.elemAt ps 0; in [
                (H.con "nil" [ ])
                (H.con "cons" [ (H.field "head" A) (H.recField "tail") ])
              ]);
            Tnat = H.app L.T H.nat;
            nilNat = H.app L.nil H.nat;
            consNat = h: t: H.app (H.app (H.app L.cons H.nat) h) t;
            l = consNat H.zero (consNat (H.succ H.zero) (consNat (H.succ (H.succ H.zero)) nilNat));
          in
          extract Tnat (E.eval [ ] (H.elab l));
        expected = [ 0 1 2 ];
      };
      "extract-app-sum-left" = {
        expr =
          let
            S = H.datatypeP "Sum"
              [{ name = "A"; kind = H.u 0; } { name = "B"; kind = H.u 0; }]
              (ps:
                let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                  (H.con "inl" [ (H.field "value" A) ])
                  (H.con "inr" [ (H.field "value" B) ])
                ]);
            Tnb = H.app (H.app S.T H.nat) H.bool;
            v = H.app (H.app (H.app S.inl H.nat) H.bool) H.zero;
          in
          extract Tnb (E.eval [ ] (H.elab v));
        expected = { _tag = "Left"; value = 0; };
      };
      "extract-app-sum-right" = {
        expr =
          let
            S = H.datatypeP "Sum"
              [{ name = "A"; kind = H.u 0; } { name = "B"; kind = H.u 0; }]
              (ps:
                let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
                  (H.con "inl" [ (H.field "value" A) ])
                  (H.con "inr" [ (H.field "value" B) ])
                ]);
            Tnb = H.app (H.app S.T H.nat) H.bool;
            v = H.app (H.app (H.app S.inr H.nat) H.bool) H.true_;
          in
          extract Tnb (E.eval [ ] (H.elab v));
        expected = { _tag = "Right"; value = true; };
      };

      # Generic decomposition for non-prelude shapes (TreeDT). Returns a
      # constructor record carrying the macro-supplied constructor and field
      # names from `_dtypeMeta`. Recursive fields recurse into the same outer
      # hoasTy; data fields recurse via reifyType on the kernel field type.
      "extract-mu-tree-leaf" = {
        expr =
          let
            Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
              let A = builtins.elemAt ps 0; in [
                (H.con "leaf" [ (H.field "value" A) ])
                (H.con "node" [ (H.recField "left") (H.recField "right") ])
              ]);
            Tnat = H.app Tree.T H.nat;
            v = H.app (H.app Tree.leaf H.nat) (H.succ H.zero);
          in
          extract Tnat (E.eval [ ] (H.elab v));
        expected = { _con = "leaf"; value = 1; };
      };
      "extract-mu-tree-node" = {
        expr =
          let
            Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
              let A = builtins.elemAt ps 0; in [
                (H.con "leaf" [ (H.field "value" A) ])
                (H.con "node" [ (H.recField "left") (H.recField "right") ])
              ]);
            Tnat = H.app Tree.T H.nat;
            leafZero = H.app (H.app Tree.leaf H.nat) H.zero;
            leafOne = H.app (H.app Tree.leaf H.nat) (H.succ H.zero);
            v = H.app (H.app (H.app Tree.node H.nat) leafZero) leafOne;
          in
          extract Tnat (E.eval [ ] (H.elab v));
        expected = {
          _con = "node";
          left = { _con = "leaf"; value = 0; };
          right = { _con = "leaf"; value = 1; };
        };
      };

      # verifyAndExtract evaluates the checked term, so a polymorphic list
      # built from bare `cons`/`nil` — whose element-type meta is solved only
      # by checking against the expected type — extracts to the list.
      # Elaborating the impl without the expected type leaves that meta
      # unsolved.
      "verify-extract-poly-list" = {
        expr = verifyAndExtract (H.listOf H.nat)
          (H.cons H.zero (H.cons (H.succ H.zero) (H.cons (H.succ (H.succ H.zero)) H.nil)));
        expected = [ 0 1 2 ];
      };
      # Dependent Sigma through verifyAndExtract: the fst value flows into the
      # instantiated snd type. The checked term's encoded payload decodes
      # against the kernel type value, which extractInner reads through the
      # representation-agnostic descView.
      "verify-extract-dependent-sigma" = {
        expr = verifyAndExtract
          (H.sigma "n" H.nat (n: H.eq H.nat n n))
          (H.pair (H.succ H.zero) (H.reflDT H.nat (H.succ H.zero)));
        expected = { fst = 1; snd = null; };
      };

      # reifyType for non-prelude VMu shapes: returns an `H.mu D'` form
      # rather than throwing. Exercises the description-driven fallback —
      # no metadata recovery from kernel D alone, so the result is anonymous;
      # extractInner's "mu" branch handles the decomposition downstream when
      # callers attach `_dtypeMeta` to the surface hoasTy.
      "reify-mu-unit-shape" = {
        expr =
          let
            U = H.datatype "Unit" [ (H.con "tt" [ ]) ];
            tyVal = E.eval [ ] (H.elab U.T);
          in
          (reifyType tyVal)._htag;
        expected = "mu";
      };
      "reify-mu-bool-shape" = {
        expr =
          let
            B = H.datatype "Bool" [ (H.con "true" [ ]) (H.con "false" [ ]) ];
            tyVal = E.eval [ ] (H.elab B.T);
          in
          (reifyType tyVal)._htag;
        expected = "mu";
      };

      # -- Cross-cutting integration tests --
      # Compound types mixing polarity, refinement, and dependent fields.
      # Each verifies that conjunction (kernelDecide ∧ guard) runs both paths.

      # Record(Pi, Sigma(refined)): mixed polarity compound type
      "integration-record-pi-sigma-refined" = {
        expr =
          let
            refined = fx.types.refinement.refined;
            PosInt = refined "PosInt" IntT (x: builtins.isInt x && x > 0);
            schema = {
              transform = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
              pair = FD.Sigma { fst = PosInt; snd = _: BoolT; universe = 0; };
            };
            RT = FC.Record schema;
            good = { transform = x: x + 1; pair = { fst = 5; snd = true; }; };
            badPair = { transform = x: x + 1; pair = { fst = -1; snd = true; }; };
            badFn = { transform = 42; pair = { fst = 5; snd = true; }; };
          in
          RT.check good && !(RT.check badPair) && !(RT.check badFn);
        expected = true;
      };

      # Record(Pi, Sigma(refined)): diagnose shows conjunction
      "integration-record-pi-sigma-diagnose" = {
        expr =
          let
            refined = fx.types.refinement.refined;
            PosInt = refined "PosInt" IntT (x: builtins.isInt x && x > 0);
            schema = {
              transform = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
              pair = FD.Sigma { fst = PosInt; snd = _: BoolT; universe = 0; };
            };
            RT = FC.Record schema;
            d = RT.diagnose { transform = x: x + 1; pair = { fst = 5; snd = true; }; };
          in
          d.kernel && d.agreement;
        expected = true;
      };

      # Maybe(DepRecord(dependent ListOf)): nested dependent conjunction
      "integration-maybe-deprecord-listof" = {
        expr =
          let
            mkType = fx.types.foundation.mkType;
            SizedList = FD.DepRecord [
              { name = "n"; type = IntT; }
              {
                name = "items";
                type = self:
                  mkType {
                    name = "List[n=${toString self.n}]";
                    kernelType = H.any;
                    guard = v: builtins.isList v && builtins.length v == self.n;
                  };
              }
            ];
            MT = FC.Maybe SizedList;
          in
          MT.check null
          && MT.check { fst = 3; snd = [ 1 2 3 ]; }
          && !(MT.check { fst = 3; snd = [ 1 2 ]; })
          && !(MT.check "not-a-pair");
        expected = true;
      };

      # ListOf(Pi): list of opaque Pi functions, kernel checks domain
      "integration-listof-pi" = {
        expr =
          let
            FnType = FD.Pi { domain = IntT; codomain = _: BoolT; universe = 0; };
            LT = FC.ListOf FnType;
            good = [ (x: x > 0) (x: x == 0) ];
            bad = [ (x: x > 0) 42 ];
          in
          LT.check good && !(LT.check bad) && LT.check [ ];
        expected = true;
      };

      # ListOf(Pi): kernel rejects non-function in list
      "integration-listof-pi-rejects-non-fn" = {
        expr =
          let
            FnType = FD.Pi { domain = IntT; codomain = _: BoolT; universe = 0; };
            LT = FC.ListOf FnType;
            d = LT.diagnose [ 42 ];
          in
          d.kernel == false;
        expected = true;
      };

      # Either(Sigma, Pi): sum of positive and negative types
      "integration-either-sigma-pi" = {
        expr =
          let
            SigT = FD.Sigma { fst = IntT; snd = _: BoolT; universe = 0; };
            PiT = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
            ET = FC.Either SigT PiT;
            goodLeft = { _tag = "Left"; value = { fst = 42; snd = true; }; };
            goodRight = { _tag = "Right"; value = x: x + 1; };
            badLeft = { _tag = "Left"; value = { fst = "bad"; snd = true; }; };
            badRight = { _tag = "Right"; value = 42; };
          in
          ET.check goodLeft && ET.check goodRight
          && !(ET.check badLeft) && !(ET.check badRight);
        expected = true;
      };

      # Either(Sigma, Pi): diagnose shows conjunction on both branches
      "integration-either-sigma-pi-diagnose" = {
        expr =
          let
            SigT = FD.Sigma { fst = IntT; snd = _: BoolT; universe = 0; };
            PiT = FD.Pi { domain = IntT; codomain = _: IntT; universe = 0; };
            ET = FC.Either SigT PiT;
            dLeft = ET.diagnose { _tag = "Left"; value = { fst = 42; snd = true; }; };
            dRight = ET.diagnose { _tag = "Right"; value = x: x + 1; };
          in
          dLeft.kernel && dLeft.agreement && dRight.kernel && dRight.agreement;
        expected = true;
      };
    };
}
