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
  atomic = [
    "nat" "unit" "string" "int" "float" "attrs" "path" "function"
    "any" "U" "tt" "refl" "funext" "zero"
    "string-lit" "int-lit" "float-lit"
    "attrs-lit" "path-lit" "fn-lit" "any-lit"
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

    # -- Kernel coproduct primitive --
    else if t == "sum-prim" then
      SM.node h {
        "DPlusL" = sourceMapOf h.L;
        "DPlusR" = sourceMapOf h.R;
      }
    else if t == "inl-prim" || t == "inr-prim" then
      SM.node h {
        "DPlusL" = sourceMapOf h.L;
        "DPlusR" = sourceMapOf h.R;
        "Field:term" = sourceMapOf h.term;
      }
    else if t == "sum-elim-prim" then
      SM.node h {
        "DPlusL" = sourceMapOf h.left;
        "DPlusR" = sourceMapOf h.right;
        "Motive" = sourceMapOf h.motive;
        "Case:onLeft"  = sourceMapOf h.onLeft;
        "Case:onRight" = sourceMapOf h.onRight;
        "Scrut"  = sourceMapOf h.scrut;
      }

    # -- Eq type --
    else if t == "eq" then
      SM.node h {
        "JType" = sourceMapOf h.type;
        "JLhs"  = sourceMapOf h.lhs;
        "JRhs"  = sourceMapOf h.rhs;
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
        "PiDom" = sourceMapOf h.domain;
        "Case:body" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "let" then
      SM.node h {
        "AnnType" = sourceMapOf h.type;
        "Field:val" = sourceMapOf h.val;
        "Case:body" = sourceMapOf (h.body bodyMarker);
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
    else if t == "desc-ret" then
      SM.node h { "DRetIndex" = sourceMapOf h.j; }
    else if t == "desc-arg" then
      SM.node h {
        "DArgSort" = sourceMapOf h.S;
        "DArgBody" = sourceMapOf (h.body bodyMarker);
      }
    else if t == "desc-rec" then
      SM.node h {
        "DRecIndex" = sourceMapOf h.j;
        "DRecTail"  = sourceMapOf h.D;
      }
    else if t == "desc-pi" then
      SM.node h {
        "DPiSort" = sourceMapOf h.S;
        "DPiFn"   = sourceMapOf h.f;
        "DPiBody" = sourceMapOf h.D;
      }
    else if t == "desc-plus" then
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
      SM.node h {
        "MuDesc"    = sourceMapOf h.D;
        "MuIndex"   = sourceMapOf h.i;
        "MuPayload" = sourceMapOf h.d;
      }
    else if t == "desc-ind" then
      SM.node h {
        "MuDesc"    = sourceMapOf h.D;
        "Motive"    = sourceMapOf h.motive;
        "Case:step" = sourceMapOf h.step;
        "MuIndex"   = sourceMapOf h.i;
        "Scrut"     = sourceMapOf h.scrut;
      }
    else if t == "desc-elim" then
      SM.node h {
        "Motive"      = sourceMapOf h.motive;
        "Case:onRet"  = sourceMapOf h.onRet;
        "Case:onArg"  = sourceMapOf h.onArg;
        "Case:onRec"  = sourceMapOf h.onRec;
        "Case:onPi"   = sourceMapOf h.onPi;
        "Case:onPlus" = sourceMapOf h.onPlus;
        "Scrut"       = sourceMapOf h.scrut;
      }

    # Macro-constructor surfaces — elaborate descends into `.fallback`
    # for the non-chain path. Mirror that so a failure in the desugared
    # lam-cascade can still back-map through Case:fallback.
    else if t == "dt-ctor-mono" || t == "dt-ctor-poly" then
      SM.node h { "Case:fallback" = sourceMapOf h.fallback; }

    else if t == "j" then
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

      # -- natDesc = plus descRet (descRec descRet) --
      "natDesc-root-is-desc-plus" = {
        expr = smNat.hoas._htag;
        expected = "desc-plus";
      };
      "natDesc-DPlusL-is-desc-ret" = {
        expr = (SMf.descendChain [ P.DPlusL ] smNat).hoas._htag;
        expected = "desc-ret";
      };
      "natDesc-DPlusR-is-desc-rec" = {
        expr = (SMf.descendChain [ P.DPlusR ] smNat).hoas._htag;
        expected = "desc-rec";
      };
      "natDesc-DPlusR-DRecTail-is-desc-ret" = {
        expr = (SMf.descendChain [ P.DPlusR P.DRecTail ] smNat).hoas._htag;
        expected = "desc-ret";
      };
      "natDesc-DPlusL-DRecTail-is-null" = {
        expr = SMf.descendChain [ P.DPlusL P.DRecTail ] smNat;
        expected = null;
      };

      # -- listDesc unit = plus descRet (descArg unit (_: descRec descRet)) --
      "listDesc-DPlusL-is-desc-ret" = {
        expr = (SMf.descendChain [ P.DPlusL ] smList).hoas._htag;
        expected = "desc-ret";
      };
      "listDesc-DPlusR-DArgSort-is-elem-type" = {
        expr = (SMf.descendChain [ P.DPlusR P.DArgSort ] smList).hoas._htag;
        expected = "unit";
      };
      "listDesc-DPlusR-DArgBody-is-desc-rec" = {
        expr = (SMf.descendChain [ P.DPlusR P.DArgBody ] smList).hoas._htag;
        expected = "desc-rec";
      };

      # -- sumDesc string unit = plus (descArg string (_: descRet))
      #                              (descArg unit   (_: descRet)) --
      "sumDesc-DPlusL-DArgSort-is-left-type" = {
        expr = (SMf.descendChain [ P.DPlusL P.DArgSort ] smSum).hoas._htag;
        expected = "string";
      };
      "sumDesc-DPlusR-DArgSort-is-right-type" = {
        expr = (SMf.descendChain [ P.DPlusR P.DArgSort ] smSum).hoas._htag;
        expected = "unit";
      };
      "sumDesc-DPlusL-DArgBody-is-desc-ret" = {
        expr = (SMf.descendChain [ P.DPlusL P.DArgBody ] smSum).hoas._htag;
        expected = "desc-ret";
      };

      # -- Back-map: Error chain threaded through nestUnder resolves
      #    through the SourceMap to the expected surface HOAS node. --
      "natDesc-error-under-DPlusR-DRecTail-resolves-to-desc-ret" = {
        expr =
          let
            leafErr = D.mkKernelError {
              rule = "check"; msg = "type mismatch";
            };
            err = D.nestUnder P.DPlusR (D.nestUnder P.DRecTail leafErr);
            hoas = SMf.hoasAtError err smNat;
          in hoas._htag;
        expected = "desc-ret";
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
}
