# HOAS → SourceMap walker.
#
# `sourceMapOf : HoasTree → SourceMap` produces a structural back-map
# whose subs are keyed by the `src/diag/positions` alphabet — the same
# keys the kernel's `bindP` attaches to failure-Error `children`
# descent chains. Composing the two lets `shell.runCheckD` resolve a
# blame chain to the HOAS subtree that produced the offending sub-Tm.
#
# Walker discipline. Every branch constructs an attrset whose values
# are `sourceMapOf <subtree>` calls. Attrset values are unevaluated
# thunks; sub-SourceMaps materialise only when the caller descends
# into them. Eager work is O(1) per call — one attrset allocation
# plus the mk-wrapping. A 5000-deep binding chain therefore costs O(1)
# at elab time and O(n) only under actual descent, where
# `SM.descendChain`'s `foldl'` keeps cumulative stack flat.
#
# Positions. Each HOAS tag maps its descendable fields to the Position
# variant whose `positionKey` (source_map.nix) matches the key written
# here. Kernel-structural positions (PiDom, DArgSort, DPlusL, …) are
# preferred where the alphabet fits; `Field`/`Case`/`Tag` are used for
# HOAS-specific surfaces (record fields, constructor arms, variant
# tags) without a dedicated nullary entry.
#
# `elab2 : HoasTree → { tm; sm; }` pairs the Tm produced by
# `elaborate 0 h` with `sourceMapOf h`. The existing single-Tm
# `elaborate` and `elab` remain the primitives used by the datatype
# macro and chain-flatten paths, which never need the SM.
{ self, fx, lib, ... }:

let
  SM = fx.tc.check.diag.sourceMap;

  # Tags whose HOAS surface is atomic — zero descendable children.
  # `U` is intentionally absent: its `level` field is a descend point
  # whose check emits `P.ULevel`, so the walker needs a branch (below).
  atomic = [
    "nat" "unit" "string" "int" "float" "attrs" "path" "derivation" "derivation-thunk" "function"
    "any" "tt" "refl" "boot-refl" "funext" "zero"
    "string-lit" "int-lit" "float-lit"
    "attrs-lit" "path-lit" "derivation-lit" "derivation-thunk-lit" "fn-lit" "any-lit"
  ];

  # Depth passed to HOAS binding bodies. SourceMap is depth-agnostic:
  # only elaborate needs real depth for de-Bruijn conversion. Any
  # marker produces the same structural subtree.
  bodyMarker = self.mkMarker 0;

  sourceMapOf = h:
    if !(builtins.isAttrs h) || !(h ? _htag) then SM.leaf h
    else if self.isMarker h then SM.leaf h
    else let t = h._htag; in

    if lib.elem t atomic then SM.leaf h

    # -- Compound-type sugar --
    else if t == "list" then
      SM.node h { "Field:elem" = sourceMapOf h.elem; }
    else if t == "sum" then
      SM.node h {
        "Field:left"  = sourceMapOf h.left;
        "Field:right" = sourceMapOf h.right;
      }
    else if t == "maybe" then
      SM.node h { "Field:inner" = sourceMapOf h.inner; }
    else if t == "record" then
      SM.node h (builtins.listToAttrs
        (map (f: { name = "Field:${f.name}"; value = sourceMapOf f.type; })
             h.fields))
    else if t == "variant" then
      SM.node h (builtins.listToAttrs
        (map (b: { name = "Tag:${b.tag}"; value = sourceMapOf b.type; })
             h.branches))

    # -- Bootstrap coproduct for descPlus --
    else if t == "boot-sum" then
      SM.node h {
        "DPlusL" = sourceMapOf h.L;
        "DPlusR" = sourceMapOf h.R;
      }
    else if t == "boot-inl" || t == "boot-inr" then
      SM.node h {
        "DPlusL" = sourceMapOf h.L;
        "DPlusR" = sourceMapOf h.R;
        "Field:term" = sourceMapOf h.term;
      }
    else if t == "boot-sum-elim" then
      SM.node h {
        "DPlusL" = sourceMapOf h.left;
        "DPlusR" = sourceMapOf h.right;
        "Motive" = sourceMapOf h.motive;
        "Case:onLeft"  = sourceMapOf h.onLeft;
        "Case:onRight" = sourceMapOf h.onRight;
        "Scrut"  = sourceMapOf h.scrut;
      }

    # -- Bootstrap Eq type --
    else if t == "boot-eq" then
      SM.node h {
        "JType" = sourceMapOf h.type;
        "JLhs"  = sourceMapOf h.lhs;
        "JRhs"  = sourceMapOf h.rhs;
      }

    # -- Universe and levels. `U k` checks its level argument under
    #    `P.ULevel`; `level-suc` under `P.LevelSucPred`; `level-max`
    #    under `P.LevelMaxLhs` / `P.LevelMaxRhs`. The walker mirrors
    #    those keys exactly so a back-mapped error resolves to the
    #    HOAS subtree that supplied the offending level. --
    else if t == "U" then
      SM.node h { "ULevel" = sourceMapOf h.level; }
    else if t == "level-suc" then
      SM.node h { "LevelSucPred" = sourceMapOf h.pred; }
    else if t == "level-max" then
      SM.node h {
        "LevelMaxLhs" = sourceMapOf h.lhs;
        "LevelMaxRhs" = sourceMapOf h.rhs;
      }

    # -- Binding forms. Bodies are Nix lambdas; apply a fresh marker
    #    to fetch the body subtree. Lazy attrset values keep each
    #    binding layer at O(1) eager cost. --
    else if t == "pi" then
      SM.node h {
        "PiDom" = sourceMapOf h.domain;
        "PiCod" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "sigma" then
      SM.node h {
        "SigmaFst" = sourceMapOf h.fst;
        "SigmaSnd" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "lam" then
      SM.node h {
        "PiDom"   = sourceMapOf h.domain;
        "LamBody" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "let" then
      SM.node h {
        "AnnType"   = sourceMapOf h.type;
        "Field:val" = sourceMapOf h.val;
        "LetBody"   = sourceMapOf (h.body bodyMarker);
      }

    # -- Non-binding terms --
    else if t == "succ" then
      SM.node h { "Case:pred" = sourceMapOf h.pred; }
    else if t == "nil" then
      SM.node h { "Field:elem" = sourceMapOf h.elem; }
    else if t == "cons" then
      SM.node h {
        "Field:elem" = sourceMapOf h.elem;
        "Case:head" = sourceMapOf h.head;
        "Case:tail" = sourceMapOf h.tail;
      }
    else if t == "pair" then
      SM.node h {
        "SigmaFst" = sourceMapOf h.fst;
        "SigmaSnd" = sourceMapOf h.snd;
      }
    else if t == "inl" || t == "inr" then
      SM.node h {
        "DPlusL" = sourceMapOf h.left;
        "DPlusR" = sourceMapOf h.right;
        "Field:term" = sourceMapOf h.term;
      }
    else if t == "opaque-lam" then
      SM.node h { "OpaqueType" = sourceMapOf h.piHoas; }
    else if t == "str-eq" then
      SM.node h {
        "JLhs" = sourceMapOf h.lhs;
        "JRhs" = sourceMapOf h.rhs;
      }
    else if t == "ann" then
      SM.node h {
        "AnnTerm" = sourceMapOf h.term;
        "AnnType" = sourceMapOf h.type;
      }
    else if t == "app" then
      SM.node h {
        "AppHead" = sourceMapOf h.fn;
        "AppArg"  = sourceMapOf h.arg;
      }
    else if t == "fst" || t == "snd" then
      SM.node h { "Scrut" = sourceMapOf h.pair; }

    # -- Descriptions --
    else if t == "desc" then
      SM.node h { "Field:I" = sourceMapOf h.I; }
    else if t == "desc-ret-enc" then
      SM.node h { "DRetIndex" = sourceMapOf h.j; }
    else if t == "desc-arg-enc" then
      SM.node h {
        "DArgSort" = sourceMapOf h.S;
        "DArgBody" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "desc-rec-enc" then
      SM.node h {
        "DRecIndex" = sourceMapOf h.j;
        "DRecTail"  = sourceMapOf h.D;
      }
    else if t == "desc-pi-enc" then
      SM.node h {
        "DPiSort" = sourceMapOf h.S;
        "DPiFn"   = sourceMapOf h.f;
        "DPiBody" = sourceMapOf h.D;
      }
    else if t == "desc-plus-enc" then
      SM.node h {
        "DPlusL" = sourceMapOf h.A;
        "DPlusR" = sourceMapOf h.B;
      }
    else if t == "mu" then
      SM.node h {
        "Field:I" = sourceMapOf h.I;
        "MuDesc"  = sourceMapOf h.D;
        "MuIndex" = sourceMapOf h.i;
      }
    else if t == "desc-con" then
      # Trampoline-aware back-map. The kernel rule at
      # `tc/check/check.nix:489-541` emits a flat blame chain
      # `[DConLayer k, MuIndex | Elem j | MuPayload]` quotienting the
      # otherwise O(k × nFields) structural prefix of a homogeneous
      # μ-unfolding. The walker mirrors that quotient by detecting the
      # pair-chain shape tag-driven (no `h.D` plus-structure inspection)
      # and surfacing `DConLayer:0 .. DConLayer:n` siblings of the legacy
      # `MuDesc | MuIndex | MuPayload` keys at the top-level node.
      #
      # Per-layer slot map (matches kernel emission table in plan §Phase 3):
      #   0 ≤ k < n  :  { MuIndex; Elem:0 .. Elem:(nFields-1) }
      #   k = n      :  { MuIndex; MuPayload }
      # The asymmetry mirrors the kernel exactly: non-base layers reach
      # their payload only via per-field descent (Elem j over the pair-
      # chain heads); the base layer's `d` is consumed wholesale under
      # `MuPayload`.
      #
      # Non-trampoline shape (top `peelLayer` returns null): legacy three
      # keys only, no DConLayer enumeration — preserves the existing
      # behaviour for standalone or non-linear desc-con HOAS.
      let
        isRetLeaf = p:
          builtins.isAttrs p && p ? _htag
          && (p._htag == "refl"
              || p._htag == "boot-refl"
              || (p._htag == "lift-intro"
                  && p ? a
                  && builtins.isAttrs p.a
                  && (p.a._htag or "") == "boot-refl"));

        # Strip one level of sum-injection. Kernel-side, the trampoline's
        # `sumPayloadTmView` (`tc/eval/desc.nix:209-221`) handles a single
        # `boot-inl` / `boot-inr` wrap; `classify` admits only the
        # single-recursive-side case so nested injections fall through to
        # the per-layer fast path. Walker mirrors that.
        stripInj = p:
          if !(builtins.isAttrs p) || !(p ? _htag) then null
          else if (p._htag == "boot-inl" || p._htag == "boot-inr"
                   || p._htag == "inl"      || p._htag == "inr")
                  && p ? term
          then p.term
          else null;

        # Walk a pair-chain accumulating `.fst` heads. Terminate when the
        # current pair's `.fst` is a `desc-con` (the REC position) and
        # `.snd` is a refl-leaf. Returns `{ heads; tail; }` on success or
        # null on a shape mismatch.
        collectPairs = inner:
          let
            go = acc: p:
              if !(builtins.isAttrs p) || (p._htag or "") != "pair" then null
              else if builtins.isAttrs p.fst
                   && (p.fst._htag or "") == "desc-con"
                   && isRetLeaf p.snd
              then { heads = acc; tail = p.fst; }
              else go (acc ++ [p.fst]) p.snd;
          in go [] inner;

        peelLayer = node:
          if !(builtins.isAttrs node) || (node._htag or "") != "desc-con"
          then null
          else
            let inner = stripInj node.d;
            in if inner == null then null else collectPairs inner;

        topPeel = peelLayer h;
      in
      if topPeel == null then
        SM.node h {
          "MuDesc"    = sourceMapOf h.D;
          "MuIndex"   = sourceMapOf h.i;
          "MuPayload" = sourceMapOf h.d;
        }
      else
        let
          # Enumerate the homogeneous μ-unfolding chain. `genericClosure`
          # keeps the walk flat; cost is O(n) at SourceMap construction —
          # lock-stepped with the kernel's check-time walk at
          # `check.nix:477-484`. Per-layer sub-map values are thunked
          # attrset entries so only forced layers materialise their
          # sourceMapOf descent.
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = h; peeled = topPeel; }];
            operator = item:
              if item.peeled == null then []
              else [{
                key = item.key + 1;
                val = item.peeled.tail;
                peeled = peelLayer item.peeled.tail;
              }];
          };
          nLayers = builtins.length chain;
          n = nLayers - 1;

          layerSubMap = k:
            let
              item   = builtins.elemAt chain k;
              layer  = item.val;
              peeled = item.peeled;
            in
            if k == n then
              SM.node layer {
                "MuIndex"   = sourceMapOf layer.i;
                "MuPayload" = sourceMapOf layer.d;
              }
            else
              SM.node layer (
                { "MuIndex" = sourceMapOf layer.i; }
                // builtins.listToAttrs (builtins.genList (j: {
                     name = "Elem:${toString j}";
                     value = sourceMapOf (builtins.elemAt peeled.heads j);
                   }) (builtins.length peeled.heads))
              );

          layerKeys = builtins.listToAttrs (builtins.genList (k: {
            name = "DConLayer:${toString k}";
            value = layerSubMap k;
          }) nLayers);
        in SM.node h ({
          "MuDesc"    = sourceMapOf h.D;
          "MuIndex"   = sourceMapOf h.i;
          "MuPayload" = sourceMapOf h.d;
        } // layerKeys)
    else if t == "desc-ind" then
      SM.node h {
        "MuDesc"    = sourceMapOf h.D;
        "Motive"    = sourceMapOf h.motive;
        "Case:step" = sourceMapOf h.step;
        "MuIndex"   = sourceMapOf h.i;
        "Scrut"     = sourceMapOf h.scrut;
      }
    # Macro-constructor surfaces — elaborate descends into `.fallback`
    # for the non-chain path. Mirror that so a failure in the desugared
    # lam-cascade can still back-map through Case:fallback.
    else if t == "dt-ctor-mono" || t == "dt-ctor-poly" then
      SM.node h { "Case:fallback" = sourceMapOf h.fallback; }

    # -- Lift family. The INFER rules at `infer.nix:324-394` tag
    #    `l`/`m`/`A`/`eq` (and `a` for intro / `x` for elim) via
    #    `bindP`; the walker keys mirror those `positionKey` outputs.
    #    The `eq` field is optional in the HOAS surface (omitted when
    #    the constructor was the level-equal idempotent shape); guard
    #    descent with `?` so the walker remains structural.
    else if t == "lift" then
      SM.node h ({
        "LevelMaxLhs" = sourceMapOf h.l;
        "LevelMaxRhs" = sourceMapOf h.m;
        "AnnType"     = sourceMapOf h.A;
      } // (if h ? eq then { "JEq" = sourceMapOf h.eq; } else {}))
    else if t == "lift-intro" then
      SM.node h ({
        "LevelMaxLhs" = sourceMapOf h.l;
        "LevelMaxRhs" = sourceMapOf h.m;
        "AnnType"     = sourceMapOf h.A;
        "AnnTerm"     = sourceMapOf h.a;
      } // (if h ? eq then { "JEq" = sourceMapOf h.eq; } else {}))
    else if t == "lift-elim" then
      SM.node h ({
        "LevelMaxLhs" = sourceMapOf h.l;
        "LevelMaxRhs" = sourceMapOf h.m;
        "AnnType"     = sourceMapOf h.A;
        "Scrut"       = sourceMapOf h.x;
      } // (if h ? eq then { "JEq" = sourceMapOf h.eq; } else {}))

    # -- Kernel-primitive description operations. The kernel rules
    #    (infer.nix:561-688) emit positions per slot via `bindP`. The
    #    walker keys mirror those `positionKey` outputs so the chain
    #    resolves to the HOAS subtree that produced the offending
    #    sub-term.
    #
    #    Note (DElimLevel collision). `all-d` and `everywhere-d` each
    #    have two level slots (`tm.K` and `tm.level`) and the kernel
    #    rule emits `P.DElimLevel` at both bindP sites. Within a single
    #    HOAS node the walker's attrset can only hold one entry per
    #    key; the convention here maps `DElimLevel` to `h.level` (the
    #    outer slot, source level of the recursion). A `tm.K`-side
    #    failure back-maps to the `h.level` HOAS subtree — imprecise
    #    by one slot but in the right family. Distinguishing positions
    #    would require kernel-side changes (out of scope here). --
    else if t == "interp-d" then
      SM.node h {
        "DElimLevel" = sourceMapOf h.level;
        "AnnType"    = sourceMapOf h.I;
        "MuDesc"     = sourceMapOf h.D;
        "Motive"     = sourceMapOf h.X;
        "MuIndex"    = sourceMapOf h.i;
      }
    else if t == "all-d" then
      SM.node h {
        "DElimLevel" = sourceMapOf h.level;
        "AnnType"    = sourceMapOf h.I;
        "MuDesc"     = sourceMapOf h.D;
        "Case:X"     = sourceMapOf h.X;
        "Motive"     = sourceMapOf h.M;
        "MuIndex"    = sourceMapOf h.i;
        "Scrut"      = sourceMapOf h.d;
      }
    else if t == "everywhere-d" then
      SM.node h {
        "DElimLevel" = sourceMapOf h.level;
        "AnnType"    = sourceMapOf h.I;
        "MuDesc"     = sourceMapOf h.D;
        "Case:X"     = sourceMapOf h.X;
        "Case:M"     = sourceMapOf h.M;
        "Case:ih"    = sourceMapOf h.ih;
        "MuIndex"    = sourceMapOf h.i;
        "Scrut"      = sourceMapOf h.d;
      }
    else if t == "desc-elim-enc" then
      SM.node h {
        "DElimLevel"   = sourceMapOf h.L;
        "AnnType"      = sourceMapOf h.I;
        "Motive"       = sourceMapOf h.motive;
        "Case:onRet"   = sourceMapOf h.onRet;
        "Case:onArg"   = sourceMapOf h.onArg;
        "Case:onRec"   = sourceMapOf h.onRec;
        "Case:onPi"    = sourceMapOf h.onPi;
        "Case:onPlus"  = sourceMapOf h.onPlus;
        "Scrut"        = sourceMapOf h.scrut;
      }
    else if t == "desc-desc-app" then
      SM.node h {
        "AnnType"    = sourceMapOf h.I;
        "DElimLevel" = sourceMapOf h.L;
      }
    else if t == "canon-app" then
      SM.node h (
        { "CanonBody" = sourceMapOf h.body; }
        // builtins.listToAttrs (builtins.genList (i: {
             name = "CanonParam:${toString i}";
             value = sourceMapOf (builtins.elemAt h.params i);
           }) (builtins.length h.params))
      )

    else if t == "j" || t == "boot-j" then
      SM.node h {
        "JType"     = sourceMapOf h.type;
        "JLhs"      = sourceMapOf h.lhs;
        "Motive"    = sourceMapOf h.motive;
        "Case:base" = sourceMapOf h.base;
        "JRhs"      = sourceMapOf h.rhs;
        "JEq"       = sourceMapOf h.eq;
      }

    # Unknown tag — be permissive; emit a leaf carrying the raw node
    # so new HOAS tags do not crash SourceMap construction before the
    # walker catches up.
    else SM.leaf h;

  elab2 = h: { tm = self.elaborate 0 h; sm = sourceMapOf h; };

in {
  scope = {
    inherit sourceMapOf elab2;
  };
  tests =
    let
      P  = fx.diag.positions;
      SMf = fx.tc.check.diag.sourceMap;
      D  = fx.diag.error;
      H  = self;

      smNat  = sourceMapOf H.natDesc;
      smList = sourceMapOf (H.listDesc H.unit);
      smSum  = sourceMapOf (H.sumDesc H.string H.unit);
    in {
      # -- Atomic leaves --
      "atomic-unit-is-leaf" = {
        expr = (sourceMapOf H.unit).subs;
        expected = {};
      };
      "atomic-carries-hoas" = {
        expr = (sourceMapOf H.unit).hoas._htag;
        expected = "unit";
      };

      # -- natDesc = NatDT.D --
      "natDesc-root-is-ann" = {
        expr = smNat.hoas._htag;
        expected = "ann";
      };
      "natDesc-AnnTerm-is-desc-plus" = {
        expr = (SMf.descendChain [ P.AnnTerm ] smNat).hoas._htag;
        expected = "desc-plus-enc";
      };
      "natDesc-DPlusL-is-desc-ret" = {
        expr = (SMf.descendChain [ P.AnnTerm P.DPlusL ] smNat).hoas._htag;
        expected = "desc-ret-enc";
      };
      "natDesc-DPlusR-is-desc-rec" = {
        expr = (SMf.descendChain [ P.AnnTerm P.DPlusR ] smNat).hoas._htag;
        expected = "desc-rec-enc";
      };
      "natDesc-DPlusR-DRecTail-is-desc-ret" = {
        expr = (SMf.descendChain [ P.AnnTerm P.DPlusR P.DRecTail ] smNat).hoas._htag;
        expected = "desc-ret-enc";
      };
      "natDesc-DPlusL-DRecTail-is-null" = {
        expr = SMf.descendChain [ P.AnnTerm P.DPlusL P.DRecTail ] smNat;
        expected = null;
      };

      # -- listDesc unit = ListDT.D unit --
      "listDesc-root-is-app" = {
        expr = smList.hoas._htag;
        expected = "app";
      };
      "listDesc-AppArg-is-elem-type" = {
        expr = (SMf.descendChain [ P.AppArg ] smList).hoas._htag;
        expected = "unit";
      };
      "listDesc-body-is-desc-plus" = {
        expr = (SMf.descendChain
          [ P.AppHead P.AnnTerm P.LamBody P.AnnTerm ] smList).hoas._htag;
        expected = "desc-plus-enc";
      };
      "listDesc-body-DPlusL-is-desc-ret" = {
        expr = (SMf.descendChain
          [ P.AppHead P.AnnTerm P.LamBody P.AnnTerm P.DPlusL ] smList).hoas._htag;
        expected = "desc-ret-enc";
      };
      "listDesc-body-DPlusR-DArgBody-is-desc-rec" = {
        expr = (SMf.descendChain
          [ P.AppHead P.AnnTerm P.LamBody P.AnnTerm P.DPlusR P.DArgBody ] smList).hoas._htag;
        expected = "desc-rec-enc";
      };

      # -- sumDesc string unit = SumDT.D levelZero string unit --
      "sumDesc-root-is-app" = {
        expr = smSum.hoas._htag;
        expected = "app";
      };
      "sumDesc-AppArg-is-right-type" = {
        expr = (SMf.descendChain [ P.AppArg ] smSum).hoas._htag;
        expected = "unit";
      };
      "sumDesc-AppHead-AppArg-is-left-type" = {
        expr = (SMf.descendChain [ P.AppHead P.AppArg ] smSum).hoas._htag;
        expected = "string";
      };
      "sumDesc-body-is-desc-plus" = {
        expr = (SMf.descendChain [
          P.AppHead P.AppHead P.AppHead P.AnnTerm
          P.LamBody P.LamBody P.LamBody P.AnnTerm
        ] smSum).hoas._htag;
        expected = "desc-plus-enc";
      };
      "sumDesc-body-DPlusL-DArgBody-is-desc-ret" = {
        expr = (SMf.descendChain [
          P.AppHead P.AppHead P.AppHead P.AnnTerm
          P.LamBody P.LamBody P.LamBody P.AnnTerm
          P.DPlusL P.DArgBody
        ] smSum).hoas._htag;
        expected = "desc-ret-enc";
      };

      "indexed-pi-desc-DPiFn-is-branch-function" = {
        expr =
          let
            IndexedPi = H.datatypeI "SourceMapIndexedPi" H.bool [
              (H.conI "mk"
                [ (H.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) ]
                (_: H.true_))
            ];
            sm = sourceMapOf IndexedPi.D;
          in (SMf.descendChain [ P.AnnTerm P.DPiFn ] sm).hoas._htag;
        expected = "ann";
      };

      # -- Back-map: Error chain threaded through nestUnder resolves
      #    through the SourceMap to the expected surface HOAS node. --
      "natDesc-error-under-DPlusR-DRecTail-resolves-to-desc-ret" = {
        expr =
          let
            leafErr = D.mkKernelError {
              rule = "check"; msg = "type mismatch";
            };
            err = D.nestUnder P.AnnTerm
              (D.nestUnder P.DPlusR (D.nestUnder P.DRecTail leafErr));
            hoas = SMf.hoasAtError err smNat;
          in hoas._htag;
        expected = "desc-ret-enc";
      };

      # -- Binding form: pi "x" unit (_: string) --
      "pi-PiDom-is-domain" = {
        expr =
          let sm = sourceMapOf (H.forall "x" H.unit (_: H.string));
          in (SMf.descendChain [ P.PiDom ] sm).hoas._htag;
        expected = "unit";
      };
      "pi-PiCod-is-body" = {
        expr =
          let sm = sourceMapOf (H.forall "x" H.unit (_: H.string));
          in (SMf.descendChain [ P.PiCod ] sm).hoas._htag;
        expected = "string";
      };

      # -- Universe and level walker branches --
      "U-ULevel-is-level" = {
        expr =
          let sm = sourceMapOf (H.u H.levelZero);
          in (SMf.descendChain [ P.ULevel ] sm).hoas._htag;
        expected = "level-zero";
      };
      "U-is-not-leaf" = {
        expr =
          let sm = sourceMapOf (H.u H.levelZero);
          in sm.subs ? "ULevel";
        expected = true;
      };
      "levelSuc-LevelSucPred-is-pred" = {
        expr =
          let sm = sourceMapOf (H.levelSuc H.levelZero);
          in (SMf.descendChain [ P.LevelSucPred ] sm).hoas._htag;
        expected = "level-zero";
      };
      "levelMax-LevelMaxLhs-is-lhs" = {
        expr =
          let sm = sourceMapOf (H.levelMax H.levelZero (H.levelSuc H.levelZero));
          in (SMf.descendChain [ P.LevelMaxLhs ] sm).hoas._htag;
        expected = "level-zero";
      };
      "levelMax-LevelMaxRhs-is-rhs" = {
        expr =
          let sm = sourceMapOf (H.levelMax H.levelZero (H.levelSuc H.levelZero));
          in (SMf.descendChain [ P.LevelMaxRhs ] sm).hoas._htag;
        expected = "level-suc";
      };
      "U-nested-level-back-maps" = {
        expr =
          let
            sm = sourceMapOf (H.u (H.levelSuc H.levelZero));
            leafErr = D.mkKernelError { rule = "check"; msg = "bad level"; };
            err = D.nestUnder P.ULevel (D.nestUnder P.LevelSucPred leafErr);
          in (SMf.hoasAtError err sm)._htag;
        expected = "level-zero";
      };

      # -- Kernel-primitive description ops --
      "interpD-DElimLevel-is-level" = {
        expr =
          let sm = sourceMapOf (H.interpD H.levelZero H.unit H.string H.int_ H.tt);
          in (SMf.descendChain [ P.DElimLevel ] sm).hoas._htag;
        expected = "level-zero";
      };
      "interpD-AnnType-is-I" = {
        expr =
          let sm = sourceMapOf (H.interpD H.levelZero H.unit H.string H.int_ H.tt);
          in (SMf.descendChain [ P.AnnType ] sm).hoas._htag;
        expected = "unit";
      };
      "interpD-MuDesc-is-D" = {
        expr =
          let sm = sourceMapOf (H.interpD H.levelZero H.unit H.string H.int_ H.tt);
          in (SMf.descendChain [ P.MuDesc ] sm).hoas._htag;
        expected = "string";
      };
      "interpD-Motive-is-X" = {
        expr =
          let sm = sourceMapOf (H.interpD H.levelZero H.unit H.string H.int_ H.tt);
          in (SMf.descendChain [ P.Motive ] sm).hoas._htag;
        expected = "int";
      };
      "interpD-MuIndex-is-i" = {
        expr =
          let sm = sourceMapOf (H.interpD H.levelZero H.unit H.string H.int_ H.tt);
          in (SMf.descendChain [ P.MuIndex ] sm).hoas._htag;
        expected = "tt";
      };
      "allD-DElimLevel-maps-to-outer-level" = {
        expr =
          let sm = sourceMapOf
            (H.allD H.levelZero H.unit H.string H.levelZero H.int_ H.float_ H.tt H.attrsLit);
          in (SMf.descendChain [ P.DElimLevel ] sm).hoas._htag;
        expected = "level-zero";
      };
      "allD-Scrut-is-d" = {
        expr =
          let sm = sourceMapOf
            (H.allD H.levelZero H.unit H.string H.levelZero H.int_ H.float_ H.tt H.attrsLit);
          in (SMf.descendChain [ P.Scrut ] sm).hoas._htag;
        expected = "attrs-lit";
      };

      # -- desc-elim-enc walker --
      "descElim-DElimLevel-is-L" = {
        expr =
          let sm = sourceMapOf
            (H.descElim H.unit H.levelZero H.levelZero
              H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
          in (SMf.descendChain [ P.DElimLevel ] sm).hoas._htag;
        expected = "level-zero";
      };
      "descElim-AnnType-is-I" = {
        expr =
          let sm = sourceMapOf
            (H.descElim H.unit H.levelZero H.levelZero
              H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
          in (SMf.descendChain [ P.AnnType ] sm).hoas._htag;
        expected = "unit";
      };
      "descElim-Case-onArg-is-onArg" = {
        expr =
          let sm = sourceMapOf
            (H.descElim H.unit H.levelZero H.levelZero
              H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
          in (SMf.descendChain [ (P.Case "onArg") ] sm).hoas._htag;
        expected = "float";
      };
      "descElim-Scrut-is-scrut" = {
        expr =
          let sm = sourceMapOf
            (H.descElim H.unit H.levelZero H.levelZero
              H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
          in (SMf.descendChain [ P.Scrut ] sm).hoas._htag;
        expected = "tt";
      };
      "descElim-Motive-is-motive" = {
        expr =
          let sm = sourceMapOf
            (H.descElim H.unit H.levelZero H.levelZero
              H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
          in (SMf.descendChain [ P.Motive ] sm).hoas._htag;
        expected = "string";
      };

      # -- Back-mapping: an error chain through a nested level expression
      #    resolves through the walker to the originating HOAS subtree. --
      "descElim-error-under-DElimLevel-resolves-to-L" = {
        expr =
          let
            sm = sourceMapOf
              (H.descElim H.unit H.levelZero (H.levelSuc H.levelZero)
                H.string H.int_ H.float_ H.attrs H.path H.derivation H.tt);
            leafErr = D.mkKernelError { rule = "check"; msg = "level mismatch"; };
            err = D.nestUnder P.DElimLevel (D.nestUnder P.LevelSucPred leafErr);
          in (SMf.hoasAtError err sm)._htag;
        expected = "level-zero";
      };

      # -- DConLayer walker resolution. The kernel's `desc-con`
      #    trampoline (`check.nix:489-541`) emits a flat blame chain
      #    `[DConLayer k, MuIndex | Elem j | MuPayload]`. The walker
      #    surfaces `DConLayer:k` keys at the top-level desc-con HOAS
      #    by structurally peeling the homogeneous pair-chain — no
      #    `h.D` plus-structure inspection. Tests cover (a) per-layer
      #    slot resolution at non-base and base layers, (b) asymmetric
      #    slot maps (non-base has no MuPayload; base has no Elem j),
      #    (c) null propagation on out-of-range layer indices and
      #    non-trampolined shapes, (d) end-to-end back-map of an
      #    Error chain to the originating HOAS subtree at 5000 deep. --
      "descCon-nontrampoline-no-DConLayer-keys" = {
        expr =
          let
            standalone = H.descCon H.unit H.int_ H.bootRefl;
            sm = sourceMapOf standalone;
          in sm.subs ? "DConLayer:0";
        expected = false;
      };
      "descCon-nontrampoline-legacy-MuPayload-still-resolves" = {
        expr =
          let
            standalone = H.descCon H.unit H.int_ H.bootRefl;
            sm = sourceMapOf standalone;
          in (SMf.descendChain [ P.MuPayload ] sm).hoas._htag;
        expected = "boot-refl";
      };
      "descCon-trampoline-natChain-DConLayer-0-MuIndex" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 0) P.MuIndex ] sm).hoas._htag;
        expected = "string";
      };
      "descCon-trampoline-natChain-DConLayer-1-MuIndex" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 1) P.MuIndex ] sm).hoas._htag;
        expected = "path";
      };
      "descCon-trampoline-natChain-DConLayer-base-MuIndex" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 2) P.MuIndex ] sm).hoas._htag;
        expected = "attrs";
      };
      "descCon-trampoline-natChain-DConLayer-base-MuPayload" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 2) P.MuPayload ] sm).hoas._htag;
        expected = "boot-inl";
      };
      "descCon-trampoline-natChain-nonbase-has-no-MuPayload" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in SMf.descendChain [ (P.DConLayer 0) P.MuPayload ] sm;
        expected = null;
      };
      "descCon-trampoline-natChain-out-of-range-is-null" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.attrs (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair base H.bootRefl));
            layer0 = H.descCon D_ H.string
                       (H.bootInr D_ D_ (H.pair layer1 H.bootRefl));
            sm = sourceMapOf layer0;
          in SMf.descendChain [ (P.DConLayer 99999) P.MuIndex ] sm;
        expected = null;
      };
      "descCon-trampoline-consChain-DConLayer-0-Elem-0" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.float_ (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair H.attrs (H.pair base H.bootRefl)));
            layer0 = H.descCon D_ H.derivation
                       (H.bootInr D_ D_ (H.pair H.string (H.pair layer1 H.bootRefl)));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 0) (P.Elem 0) ] sm).hoas._htag;
        expected = "string";
      };
      "descCon-trampoline-consChain-DConLayer-1-Elem-0" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.float_ (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair H.attrs (H.pair base H.bootRefl)));
            layer0 = H.descCon D_ H.derivation
                       (H.bootInr D_ D_ (H.pair H.string (H.pair layer1 H.bootRefl)));
            sm = sourceMapOf layer0;
          in (SMf.descendChain [ (P.DConLayer 1) (P.Elem 0) ] sm).hoas._htag;
        expected = "attrs";
      };
      "descCon-trampoline-error-DConLayer-1-Elem-0-back-maps" = {
        expr =
          let
            D_ = H.unit;
            base   = H.descCon D_ H.float_ (H.bootInl D_ D_ H.bootRefl);
            layer1 = H.descCon D_ H.path
                       (H.bootInr D_ D_ (H.pair H.attrs (H.pair base H.bootRefl)));
            layer0 = H.descCon D_ H.derivation
                       (H.bootInr D_ D_ (H.pair H.string (H.pair layer1 H.bootRefl)));
            sm = sourceMapOf layer0;
            leafErr = D.mkKernelError { rule = "check"; msg = "type mismatch"; };
            err = D.nestUnder (P.DConLayer 1) (D.nestUnder (P.Elem 0) leafErr);
          in (SMf.hoasAtError err sm)._htag;
        expected = "attrs";
      };
      # -- Stack-safety + DConLayer quotient at 5000 depth. Mirrors the
      #    manual spot-check in the previous handoff: a kernel-emitted
      #    `[DConLayer 4000, Elem 0]` chain (the trampoline's failing
      #    layer at construction step 1000 in a 5000-list) resolves
      #    through the walker to the layer-4000 head HOAS. --
      "descCon-trampoline-5000-deep-DConLayer-4000-Elem-0-back-maps" = {
        expr =
          let
            D_ = H.unit;
            base = H.descCon D_ H.int_ (H.bootInl D_ D_ H.bootRefl);
            wrap = inner:
              H.descCon D_ H.int_
                (H.bootInr D_ D_ (H.pair H.string (H.pair inner H.bootRefl)));
            deepChain = builtins.foldl' (acc: _: wrap acc) base (lib.range 1 5000);
            sm = sourceMapOf deepChain;
            leafErr = D.mkKernelError { rule = "check"; msg = "layer-4000 mismatch"; };
            err = D.nestUnder (P.DConLayer 4000) (D.nestUnder (P.Elem 0) leafErr);
          in (SMf.hoasAtError err sm)._htag;
        expected = "string";
      };

      # -- elab2 produces both tm and sm --
      "elab2-has-tm-and-sm" = {
        expr =
          let p = elab2 H.unit;
          in p ? tm && p ? sm && SMf.isSourceMap p.sm;
        expected = true;
      };
      "elab2-tm-matches-elaborate" = {
        expr =
          let
            h = H.forall "x" H.unit (_: H.string);
            p = elab2 h;
          in p.tm == self.elaborate 0 h;
        expected = true;
      };
    };
  __docs = {
    elab2 = {
      description = "elab2: pair-producing elaborator — runs `elab` and `sourceMapOf` together, returning `{ tm, sourceMap }`; used by the diagnostic shell which consumes both outputs.";
      signature = "elab2 : Hoas -> { tm : Tm, sourceMap : SourceMap }";
    };
    sourceMapOf = {
      description = "sourceMapOf: HOAS surface → SourceMap walker — produces a structural map from the HOAS term's positions to source-form metadata; consumed by the diagnostic shell to associate errors with source positions.";
      signature = "sourceMapOf : Hoas -> SourceMap";
    };
  };
}
