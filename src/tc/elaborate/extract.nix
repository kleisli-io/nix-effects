# Elaboration: kernel → Nix value extraction.
#
# `extractInner` is the reverse direction of `elaborateValue`: given an HOAS
# type, a kernel type value, and a kernel value, produce a Nix value.
# `reifyType` converts a kernel type value back to an HOAS type (used as
# fallback when the HOAS body cannot be recovered — dependent-type
# instantiation, polymorphic app-spine reduction). `reifyDesc` is the
# description-side counterpart consumed by `reifyType`'s VMu fallback.
#
# The Pi branch of `extractInner` wraps a Nix argument via
# `self.elaborateValue` before feeding it back into the kernel; the
# mutual recursion closes through `self`.
{ self, fx, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  V = fx.tc.value;

  # View-backed description inspection. Encoded descriptions project
  # through the private `DView*` shape instead of public constructors.
  descViewOf = d:
    let view = E.descView d; in
    if view == null then throw "extract: malformed description tag '${d.tag}'"
    else view;
  tagOfView = view:
    if view.idx == 0 then "DViewRet"
    else if view.idx == 1 then "DViewArg"
    else if view.idx == 2 then "DViewRec"
    else if view.idx == 3 then "DViewPi"
    else if view.idx == 4 then "DViewPlus"
    else throw "extract: unknown desc view idx ${toString view.idx}";
  tagOfDesc = v:
    let view = E.descView v; in
    if view == null then v.tag else tagOfView view;
  plusAOf = d:
    let view = descViewOf d; in
    if view.idx == 4 then view.A
    else throw "extract: plusAOf on ${tagOfView view}";
  plusBOf = d:
    let view = descViewOf d; in
    if view.idx == 4 then view.B
    else throw "extract: plusBOf on ${tagOfView view}";
  argSOf = d:
    let view = descViewOf d; in
    if view.idx == 1 then view.sTy
    else throw "extract: argSOf on ${tagOfView view}";
  recDOf = d:
    let view = descViewOf d; in
    if view.idx == 2 then view.sub
    else throw "extract: recDOf on ${tagOfView view}";
  retJOf = d:
    let view = descViewOf d; in
    if view.idx == 0 then view.j
    else throw "extract: retJOf on ${tagOfView view}";
  applyArgT = d: arg:
    let view = descViewOf d; in
    if view.idx == 1 then E.vApp view.tFn arg
    else throw "extract: applyArgT on ${tagOfView view}";
  sumPayloadOf = ctx: v:
    let view = E.sumPayloadValView v; in
    if view == null then throw "extract: ${ctx} expected sum payload, got ${v.tag}"
    else view;
in {
  scope = {
    # reifyDesc : Val → HoasTree
    # Rebuild a kernel description value as an HOAS description term.
    # Anonymous — the kernel D alone carries no constructor/field names;
    # callers attach `_dtypeMeta` externally when named decomposition is
    # wanted.
    reifyDesc = dVal:
      let
        view = descViewOf dVal;
        k = if dVal ? k then H.reifyLevel dVal.k else 0;
        valOfHoasArg = x:
          if builtins.isAttrs x && x ? _hoas && x ? level
          then V.freshVar x.level
          else E.eval [] (H.elab x);
      in
      if view.idx == 0 then H.descRet
      else if view.idx == 1 then
        H.descArg H.unitPrim k (self.reifyType view.sTy)
          (x: self.reifyDesc (E.vApp view.tFn (valOfHoasArg x)))
      else if view.idx == 2 then H.descRec (self.reifyDesc view.sub)
      else if view.idx == 3 then
        H.descPi k (self.reifyType view.sTy) (self.reifyDesc view.sub)
      else if view.idx == 4 then
        H.plus (self.reifyDesc view.A) (self.reifyDesc view.B)
      else throw "reifyDesc: unsupported desc view idx ${toString view.idx}";

    # reifyType : Val → HoasTree
    # Convert a kernel type value back to an HOAS type for extract dispatch.
    # Used as fallback when the HOAS body cannot be applied (dependent types)
    # and as the polymorphic-instantiation reducer for extractInner's "app"
    # branch. Loses sugar (VSigma → H.sigma, not H.record) — HOAS body is
    # preferred when available since it preserves record/variant/maybe
    # structure.
    #
    # Generated nat/list/sum shapes reify to raw-tag HOAS attrsets rather
    # than the module-level `H.nat`/`H.listOf`/`H.sum` combinators. Those
    # public combinators carry app-spines or `_dtypeMeta`; raw tags dispatch
    # directly to `extractInner`'s decoders and avoid re-entering type reify.
    reifyType = tyVal:
      let
        t = tyVal.tag;
        rawNat = { _htag = "nat"; };
        rawList = elem: { _htag = "list"; inherit elem; };
        rawSum = left: right: { _htag = "sum"; inherit left right; };
      in
      if t == "VString" then H.string
      else if t == "VUnit" then H.unit
      else if t == "VInt" then H.int_
      else if t == "VFloat" then H.float_
      else if t == "VAttrs" then H.attrs
      else if t == "VPath" then H.path
      else if t == "VFunction" then H.function_
      else if t == "VAny" then H.any
      else if t == "VBootSum" then rawSum (self.reifyType tyVal.left) (self.reifyType tyVal.right)
      else if t == "VSigma" then
        H.sigma tyVal.name (self.reifyType tyVal.fst)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VPi" then
        H.forall tyVal.name (self.reifyType tyVal.domain)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VU" then
        # Universe level is a Level value. `H.reifyLevel` round-trips
        # any Level Val (concrete `vLevelSuc^n vLevelZero` chain,
        # `vLevelMax`, or `vNe` for a bound Level variable) into a HOAS
        # Level node, which `u`'s `elaborateLevel` accepts uniformly.
        H.u (H.reifyLevel tyVal.level)
      # VMu D — description-based fixpoints. Three sugar shapes are detected
      # first and reified to their named HOAS forms (preserves printed names
      # in error messages). Under the plus-coproduct encoding:
      #   natDesc:     D = plus descRet (descRec descRet)
      #   listDesc e:  D = plus descRet (descArg e (_: descRec descRet))
      #   sumDesc l r: D = plus (descArg l (_: descRet)) (descArg r (_: descRet))
      # The DViewArg bodies closed over `_` are instantiated at VTt
      # (placeholder; the body ignores the bound value).
      # Anything else routes to the description-driven fallback `H.mu
      # (reifyDesc D)` — the resulting form is anonymous (no constructor /
      # field names) and is consumed by extractInner's "mu" branch which
      # optionally merges `_dtypeMeta` supplied by the caller for named
      # decomposition.
      else if t == "VMu" then
        let
          D = tyVal.D;
          fallback = H.mu (self.reifyDesc D) H.tt;
        in
          if tagOfDesc D != "DViewPlus" then fallback
          else
            let A = plusAOf D; B = plusBOf D; in
            if tagOfDesc A == "DViewRet" && (retJOf A).tag == "VTt"
               && tagOfDesc B == "DViewRet" && (retJOf B).tag == "VTt"
            then H.bool
            else if tagOfDesc A == "DViewRet" && tagOfDesc B == "DViewRec"
                 && tagOfDesc (recDOf B) == "DViewRet"
            then rawNat
            else if tagOfDesc A == "DViewRet" && tagOfDesc B == "DViewArg"
                 && (let body = applyArgT B V.vTt; in
                     tagOfDesc body == "DViewRec" && tagOfDesc (recDOf body) == "DViewRet")
            then rawList (self.reifyType (argSOf B))
            else if tagOfDesc A == "DViewArg" && tagOfDesc B == "DViewArg"
                 && (let bA = applyArgT A V.vTt;
                         bB = applyArgT B V.vTt; in
                     tagOfDesc bA == "DViewRet" && tagOfDesc bB == "DViewRet")
            then rawSum (self.reifyType (argSOf A)) (self.reifyType (argSOf B))
            else fallback
      else throw "reifyType: unsupported value tag '${t}'";

    # extractInner : HoasTree → Val → Val → NixValue
    # Three-argument extraction: HOAS type (for dispatch and sugar), kernel type
    # value (for dependent codomain/snd computation), and kernel value to extract.
    # Uses closure instantiation instead of sentinel tests for dependent types.
    extractInner = hoasTy: tyVal: val:
      let t = hoasTy._htag or (throw "extract: not an HOAS type"); in

      # Nat: base → 0, succ^n(base) → n. H.nat elaborates to μnatDesc, so every
      # value of type Nat arrives as a VDescCon chain. Under the plus-based
      # natDesc = plus descRet (descRec descRet):
      #   zero:   VDescCon natDesc (VBootInl _ _ VBootRefl)
      #   succ p: VDescCon natDesc (VBootInr _ _ (VPair p VBootRefl))
      # Trampolined via genericClosure for stack safety on large nats. The
      # operator does O(1) field projection on a concrete value; no deferred
      # continuation work accumulates, so the integer key suffices for dedup
      # and deepSeq-in-key would add O(N²) cost.
      if t == "nat" then
        let
          succPayload = v:
            if v.tag != "VDescCon" then null
            else
              let sv = E.sumPayloadValView v.d; in
              if sv != null && sv.side == "inr" && sv.value.tag == "VPair"
              then sv.value
              else null;
          isDescZero = v:
            if v.tag != "VDescCon" then false
            else
              let sv = E.sumPayloadValView v.d; in
              sv != null && sv.side == "inl";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              let payload = succPayload item.val; in
              if payload != null
              then [{ key = item.key + 1; val = payload.fst; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
        in
          if isDescZero last.val
          then builtins.length chain - 1
          else throw "extract: Nat value is not a numeral (stuck at ${last.val.tag})"

      else if t == "unit" then
        if val.tag == "VTt" then null
        else throw "extract: Unit value is not tt (got ${val.tag})"

      else if t == "string" then
        if val.tag == "VStringLit" then val.value
        else throw "extract: String value is not a string literal (got ${val.tag})"

      else if t == "int" then
        if val.tag == "VIntLit" then val.value
        else throw "extract: Int value is not an int literal (got ${val.tag})"

      else if t == "float" then
        if val.tag == "VFloatLit" then val.value
        else throw "extract: Float value is not a float literal (got ${val.tag})"

      else if t == "attrs" then
        throw "extract: Attrs is opaque — kernel does not store attrset contents"

      else if t == "path" then
        throw "extract: Path is opaque — kernel does not store path value"

      else if t == "function" then
        throw "extract: Function is opaque — kernel does not store closure"

      else if t == "any" then
        throw "extract: Any is opaque — kernel does not store original value"

      else if t == "list" then
        # H.listOf elem elaborates to μ(listDesc elem), so every value of type
        # List arrives as a VDescCon chain. Under the plus-based
        # listDesc elem = plus descRet (descArg elem (_: descRec descRet)):
        #   nil:       VDescCon D (VBootInl _ _ VBootRefl)
        #   cons h t:  VDescCon D (VBootInr _ _ (VPair h (VPair t VBootRefl)))
        # elemTyVal is recovered from the outer description: D = DViewPlus A B,
        # B = DViewArg elem (_: descRec descRet), whose .S is elem.
        # Trampolined via genericClosure for stack safety.
        let
          elemTy = hoasTy.elem;
          consPayload = v:
            if v.tag != "VDescCon" then null
            else
              let sv = E.sumPayloadValView v.d; in
              if sv != null && sv.side == "inr"
                 && sv.value.tag == "VPair"
                 && sv.value.snd.tag == "VPair"
              then sv.value
              else null;
          isDescNil = v:
            if v.tag != "VDescCon" then false
            else
              let sv = E.sumPayloadValView v.d; in
              sv != null && sv.side == "inl";
          elemTyVal =
            if tyVal.tag == "VMu" && tagOfDesc tyVal.D == "DViewPlus"
               && tagOfDesc (plusBOf tyVal.D) == "DViewArg"
            then argSOf (plusBOf tyVal.D)
            else throw "extract: list tyVal must be VMu(plus _ (descArg _ _)), got ${tyVal.tag}";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              let payload = consPayload item.val; in
              if payload != null
              then [{ key = item.key + 1; val = payload.snd.fst; }]
              else [];
          };
          n = builtins.length chain;
          last = builtins.elemAt chain (n - 1);
        in
          if !(isDescNil last.val)
          then throw "extract: List is not a proper cons/nil chain (stuck at ${last.val.tag})"
          else builtins.genList (i:
            let payload = consPayload (builtins.elemAt chain i).val; in
            self.extractInner elemTy elemTyVal payload.fst
          ) (n - 1)

      else if t == "sum" then
        # H.sum l r elaborates to μ(sumDesc l r), so every value of type Sum
        # arrives as a single-layer VDescCon. Under the plus-based
        # sumDesc l r = plus (descArg l (_: descRet)) (descArg r (_: descRet)):
        #   inl a: VDescCon D (VBootInl _ _ (VPair a VBootRefl))
        #   inr b: VDescCon D (VBootInr _ _ (VPair b VBootRefl))
        # Branch element type is recovered from D = DViewPlus A B, where
        # A = DViewArg l (_: descRet), B = DViewArg r (_: descRet).
        let
          sv = sumPayloadOf "Sum value" val;
          armTy = side:
            if tyVal.tag == "VBootSum" then
              if side == "L" then tyVal.left else tyVal.right
            else if tyVal.tag == "VMu" && tagOfDesc tyVal.D == "DViewPlus" then
              let sub = if side == "L" then plusAOf tyVal.D else plusBOf tyVal.D; in
              if tagOfDesc sub == "DViewArg" then argSOf sub
              else throw "extract: sum tyVal has non-sum description (sub-${side}=${tagOfDesc sub})"
            else throw "extract: sum tyVal must be VMu(plus _ _) or VBootSum, got ${tyVal.tag}";
        in
        if sv.side == "inl" then
          { _tag = "Left"; value = self.extractInner hoasTy.left (armTy "L") sv.value; }
        else
          { _tag = "Right"; value = self.extractInner hoasTy.right (armTy "R") sv.value; }

      else if t == "sigma" then
        let
          fstNix = self.extractInner hoasTy.fst tyVal.fst val.fst;
          sndTyVal = E.instantiate tyVal.closure val.fst;
          r = builtins.tryEval (hoasTy.body { _htag = "unit"; });
          sndHoas = if r.success then r.value else self.reifyType sndTyVal;
        in { fst = fstNix; snd = self.extractInner sndHoas sndTyVal val.snd; }

      # -- Compound types (record, maybe, variant) --

      else if t == "record" then
        let
          fields = hoasTy.fields;
          n = builtins.length fields;
        in
          if n == 0 then {}
          else if n == 1 then
            { ${(builtins.head fields).name} = self.extractInner (builtins.head fields).type tyVal val; }
          else
            let
              extractFields = remaining: tyV: v:
                if builtins.length remaining == 1 then
                  { ${(builtins.head remaining).name} = self.extractInner (builtins.head remaining).type tyV v; }
                else
                  let
                    f = builtins.head remaining;
                    rest = builtins.tail remaining;
                    sndTyVal = E.instantiate tyV.closure v.fst;
                  in
                  { ${f.name} = self.extractInner f.type tyV.fst v.fst; }
                  // extractFields rest sndTyVal v.snd;
            in extractFields fields tyVal val

      else if t == "maybe" then
        let
          result = self.extractInner {
            _htag = "sum";
            left = hoasTy.inner;
            right = H.unit;
          } tyVal val;
        in
          if result._tag == "Left" then result.value else null

      else if t == "variant" then
        let
          branches = hoasTy.branches;
          extractBranch = bs: tyV: v:
            let n = builtins.length bs; in
            if n == 1 then
              { _tag = (builtins.head bs).tag; value = self.extractInner (builtins.head bs).type tyV v; }
            else
              let
                b1 = builtins.head bs;
                rest = builtins.tail bs;
                restTy = { _htag = "variant"; branches = rest; };
                result = self.extractInner {
                  _htag = "sum";
                  left = b1.type;
                  right = restTy;
                } tyV v;
              in
                if result._tag == "Left"
                then { _tag = b1.tag; value = result.value; }
                else result.value;
        in extractBranch branches tyVal val

      else if t == "pi" then
        # Opaque lambda: return the original Nix function directly.
        # No kernel extraction needed — the function was carried opaquely.
        if val.tag == "VOpaqueLam" then val.nixFn
        # Verified lambda: extract via kernel pipeline.
        # Returns a Nix function that:
        #   1. Elaborates its argument to HOAS → kernel value
        #   2. Applies the VLam closure
        #   3. Extracts the result back to a Nix value
        # Codomain type is computed per-invocation from the type's closure,
        # supporting both dependent and non-dependent Pi.
        else let domainTy = hoasTy.domain; in
          nixArg:
            let
              hoasArg = self.elaborateValue domainTy nixArg;
              kernelArg = E.eval [] (H.elab hoasArg);
              resultVal = E.instantiate val.closure kernelArg;
              codomainTyVal = E.instantiate tyVal.closure kernelArg;
              r = builtins.tryEval (hoasTy.body hoasArg);
              codomainHoas = if r.success then r.value else self.reifyType codomainTyVal;
            in self.extractInner codomainHoas codomainTyVal resultVal

      # Description-based fixpoints. Detect prelude-equivalent shapes by
      # structure and delegate to the nat/list/sum branches to preserve
      # the same Nix output for shape-equivalent values. Bool-shape and
      # Unit-shape values (no dedicated "bool"/"unit" branch handles their
      # VDescCon wrapping) decode inline to Nix bool / null. Other shapes
      # decompose generically into a constructor record using `_dtypeMeta`
      # for naming; without metadata, names are positional ("con0" /
      # "_field0").
      else if t == "mu" then
        let
          # Shape dispatch reads descriptions through `descView`, so the
          # same code handles primitive, encoded, and private-view nodes.
          descTyVal = tyVal.D;
          meta = hoasTy._dtypeMeta or null;

          # Description-shape predicates under the plus-coproduct encoding.
          # All accept either primitive `VDescX` or encoded `VDescCon` shapes
          # via the module-level `tagOfDesc` / `plusAOf` / `plusBOf` /
          # `applyArgT` / `argSOf` / `recDOf` / `retJOf` helpers.
          # NatPlus: A=descRet, B=descRec descRet.
          isNatPlusDesc = d:
            tagOfDesc d == "DViewPlus"
            && tagOfDesc (plusAOf d) == "DViewRet"
            && tagOfDesc (plusBOf d) == "DViewRec"
            && tagOfDesc (recDOf (plusBOf d)) == "DViewRet";
          # ListPlus(elem): A=descRet, B=descArg elem (_: descRec descRet).
          # The inner body is instantiated at VTt (placeholder; the closure
          # ignores its argument for listDesc).
          isListPlusDesc = d:
            tagOfDesc d == "DViewPlus"
            && tagOfDesc (plusAOf d) == "DViewRet"
            && tagOfDesc (plusBOf d) == "DViewArg"
            && (let body = applyArgT (plusBOf d) V.vTt; in
                tagOfDesc body == "DViewRec" && tagOfDesc (recDOf body) == "DViewRet");
          # SumPlus(l,r): A=descArg l (_: descRet), B=descArg r (_: descRet).
          isSumPlusDesc = d:
            tagOfDesc d == "DViewPlus"
            && tagOfDesc (plusAOf d) == "DViewArg"
            && tagOfDesc (plusBOf d) == "DViewArg"
            && (let bA = applyArgT (plusAOf d) V.vTt;
                    bB = applyArgT (plusBOf d) V.vTt; in
                tagOfDesc bA == "DViewRet" && tagOfDesc bB == "DViewRet");
          # BoolPlus shape: D = DViewPlus (DViewRet VTt) (DViewRet VTt).
          # Each summand is a non-recursive retI leaf; val.d is VBootInl/VBootInr
          # from plus's kernel-Sum interpretation. Covers both the
          # prelude `boolDesc` and the datatype-macro-generated n=2 spine
          # where both ctors are fieldless.
          isBoolPlusShape = d:
            tagOfDesc d == "DViewPlus"
            && tagOfDesc (plusAOf d) == "DViewRet" && (retJOf (plusAOf d)).tag == "VTt"
            && tagOfDesc (plusBOf d) == "DViewRet" && (retJOf (plusBOf d)).tag == "VTt";
          # UnitDT shape: bare descRet (n=1).
          isUnitDTShape = d:
            tagOfDesc d == "DViewRet";

          # Generic decomposition for non-prelude shapes. Walks the plus
          # spine to determine the constructor index, then walks the per-arm
          # data spine to extract fields.
          pickArm = idx: dTy: pl:
            let view = E.descView dTy; in
            if view != null && view.idx == 4 then
              let sv = sumPayloadOf "mu plus-tag" pl; in
              if sv.side == "inl" then pickArm idx view.A sv.value
              else pickArm (idx + 1) view.B sv.value
            else { ctorIdx = idx; armDesc = dTy; armPayload = pl; };
          extractFields = dTy: pl:
            let view = descViewOf dTy; in
            if view.idx == 0 then []
            else if view.idx == 1 then
              let fieldVal = pl.fst;
                  rest = pl.snd;
                  fieldHoas = self.reifyType view.sTy;
                  fieldNix = self.extractInner fieldHoas view.sTy fieldVal;
                  subDesc = E.vApp view.tFn fieldVal;
              in [ fieldNix ] ++ extractFields subDesc rest
            else if view.idx == 2 then
              let recVal = pl.fst;
                  rest = pl.snd;
                  recNix = self.extractInner hoasTy tyVal recVal;
              in [ recNix ] ++ extractFields view.sub rest
            else if view.idx == 3 then
              # Opaque lambda field: return the kernel VLam wrapped as a
              # Nix function via the existing pi-extract discipline. Domain
              # is reified; codomain is the outer mu's hoasTy (rec under Pi).
              let lamVal = pl.fst;
                  rest = pl.snd;
                  domainHoas = self.reifyType view.sTy;
                  piHoas = H.forall "_" domainHoas (_: hoasTy);
                  piTyVal = V.vPi "_" view.sTy (V.mkClosure [] (H.elab hoasTy));
                  lamNix = self.extractInner piHoas piTyVal lamVal;
              in [ lamNix ] ++ extractFields view.sub rest
            else throw "extract: plus desc reached extractFields";

        in
        if val.tag != "VDescCon"
        then throw "extract: mu value is not a VDescCon (got ${val.tag})"
        else if isUnitDTShape descTyVal then null
        else if isBoolPlusShape descTyVal then
          let sv = sumPayloadOf "BoolPlus-shape value" val.d; in
          if sv.side == "inl" then true else false
        else if isNatPlusDesc descTyVal
        then self.extractInner { _htag = "nat"; } tyVal val
        else if isListPlusDesc descTyVal then
          let elemTyVal = argSOf (plusBOf descTyVal);
          in self.extractInner { _htag = "list"; elem = self.reifyType elemTyVal; } tyVal val
        else if isSumPlusDesc descTyVal then
          let leftTyVal = argSOf (plusAOf descTyVal);
              rightTyVal = argSOf (plusBOf descTyVal);
          in self.extractInner {
            _htag = "sum";
            left = self.reifyType leftTyVal;
            right = self.reifyType rightTyVal;
          } tyVal val
        else
          let
            arm = pickArm 0 descTyVal val.d;
            fieldVals = extractFields arm.armDesc arm.armPayload;
            conName =
              if meta != null
              then (builtins.elemAt meta.cons arm.ctorIdx).name
              else "con${toString arm.ctorIdx}";
            fieldNames =
              if meta != null
              then map (f: f.name) (builtins.elemAt meta.cons arm.ctorIdx).fields
              else builtins.genList (i: "_field${toString i}") (builtins.length fieldVals);
          in
            { _con = conName; }
            // builtins.listToAttrs (builtins.genList (i: {
                 name = builtins.elemAt fieldNames i;
                 value = builtins.elemAt fieldVals i;
               }) (builtins.length fieldVals))

      # Polymorphic-instantiation surface: hoasTy is `app^k head A1 ... Ak`
      # where `head` is the macro's `polyField "T"` carrying `_dtypeMeta`.
      # tyVal is the kernel value computed by extract (`E.eval [] (H.elab
      # hoasTy)`), already β-reduced past the application — typically a VMu.
      # Reify the type to obtain a tag-dispatchable HOAS form, propagate
      # `_dtypeMeta` from the head if present (so the mu-branch generic
      # decomposition can name constructors), and recurse.
      else if t == "app" then
        let
          peelHead = node:
            if (builtins.isAttrs node) && (node._htag or null) == "app"
            then peelHead node.fn
            else node;
          head = peelHead hoasTy;
          headMeta = head._dtypeMeta or null;
          base = self.reifyType tyVal;
          hoasTy' =
            if headMeta != null && (base._htag or null) == "mu"
            then base // { _dtypeMeta = headMeta; }
            else base;
        in self.extractInner hoasTy' tyVal val

      else throw "extract: unsupported type '${t}'";
  };

  tests = let
    encodedBoolDesc = E.eval [] (H.elab (H.plus H.descRet H.descRet));
    encodedNonPreludeDesc = E.eval [] (H.elab
      (H.plus H.descRet (H.descRec (H.descRec H.descRet))));
  in {
    "reifyDesc-encoded-plus-elaborates" = {
      expr = (E.descView (E.eval [] (H.elab (self.reifyDesc encodedBoolDesc)))).idx;
      expected = 4;
    };
    "reifyType-encoded-non-prelude-mu-fallback" = {
      expr = let
        h = self.reifyType (V.vMu V.vUnit encodedNonPreludeDesc V.vTt);
      in "${encodedNonPreludeDesc.tag}/${h._htag}/${h.D._htag}";
      expected = "VDescCon/mu/desc-plus-enc";
    };
  };
}
