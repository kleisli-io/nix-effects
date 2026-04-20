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
in {
  scope = {
    # reifyDesc : Val → HoasTree
    # Rebuild a kernel description value as an HOAS description term.
    # Anonymous — the kernel D alone carries no constructor/field names;
    # callers attach `_dtypeMeta` externally when named decomposition is
    # wanted.
    reifyDesc = dVal:
      let dt = dVal.tag; in
      if dt == "VDescRet" then H.descRet
      else if dt == "VDescRec" then H.descRec (self.reifyDesc dVal.D)
      else if dt == "VDescPi" then H.descPi (self.reifyType dVal.S) (self.reifyDesc dVal.D)
      else if dt == "VDescArg" then
        H.descArg (self.reifyType dVal.S)
          (x: self.reifyDesc (E.instantiate dVal.T (E.eval [] (H.elab x))))
      else throw "reifyDesc: unsupported VDesc tag '${dt}'";

    # reifyType : Val → HoasTree
    # Convert a kernel type value back to an HOAS type for extract dispatch.
    # Used as fallback when the HOAS body cannot be applied (dependent types)
    # and as the polymorphic-instantiation reducer for extractInner's "app"
    # branch. Loses sugar (VSigma → H.sigma, not H.record) — HOAS body is
    # preferred when available since it preserves record/variant/maybe
    # structure.
    #
    # The nat/list/sum reifications produce raw-tag HOAS attrsets rather
    # than the module-level `H.nat`/`H.listOf`/`H.sum` combinators. The
    # module-level combinators are app-spines (listOf/sum) or mu-forms
    # with `_dtypeMeta` (nat); feeding them back into `extractInner` would
    # re-enter the higher-level branches that reifyType is supposed to
    # terminate. The raw tags dispatch directly to the `"nat"`/`"list"`/
    # `"sum"` decoders in both `hoas.elaborate` and `extractInner`.
    reifyType = tyVal:
      let
        t = tyVal.tag;
        rawNat = { _htag = "nat"; };
        rawList = elem: { _htag = "list"; inherit elem; };
        rawSum = left: right: { _htag = "sum"; inherit left right; };
      in
      if t == "VNat" then rawNat
      else if t == "VBool" then H.bool
      else if t == "VString" then H.string
      else if t == "VUnit" then H.unit
      else if t == "VVoid" then H.void
      else if t == "VInt" then H.int_
      else if t == "VFloat" then H.float_
      else if t == "VAttrs" then H.attrs
      else if t == "VPath" then H.path
      else if t == "VFunction" then H.function_
      else if t == "VAny" then H.any
      else if t == "VList" then rawList (self.reifyType tyVal.elem)
      else if t == "VSum" then rawSum (self.reifyType tyVal.left) (self.reifyType tyVal.right)
      else if t == "VSigma" then
        H.sigma tyVal.name (self.reifyType tyVal.fst)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VPi" then
        H.forall tyVal.name (self.reifyType tyVal.domain)
          (x: self.reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
      else if t == "VU" then H.u tyVal.level
      # VMu D — description-based fixpoints. Three sugar shapes are detected
      # first and reified to their named HOAS forms (preserves printed names
      # in error messages). Under the plus-coproduct encoding:
      #   natDesc:     D = plus descRet (descRec descRet)
      #   listDesc e:  D = plus descRet (descArg e (_: descRec descRet))
      #   sumDesc l r: D = plus (descArg l (_: descRet)) (descArg r (_: descRet))
      # The VDescArg bodies closed over `_` are instantiated at VTt
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
          if D.tag != "VDescPlus" then fallback
          else
            let A = D.A; B = D.B; in
            if A.tag == "VDescRet" && B.tag == "VDescRec"
               && B.D.tag == "VDescRet"
            then rawNat
            else if A.tag == "VDescRet" && B.tag == "VDescArg"
                 && (let body = E.instantiate B.T V.vTt; in
                     body.tag == "VDescRec" && body.D.tag == "VDescRet")
            then rawList (self.reifyType B.S)
            else if A.tag == "VDescArg" && B.tag == "VDescArg"
                 && (let bA = E.instantiate A.T V.vTt;
                         bB = E.instantiate B.T V.vTt; in
                     bA.tag == "VDescRet" && bB.tag == "VDescRet")
            then rawSum (self.reifyType A.S) (self.reifyType B.S)
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
      #   zero:   VDescCon natDesc (VInl _ _ VRefl)
      #   succ p: VDescCon natDesc (VInr _ _ (VPair p VRefl))
      # Trampolined via genericClosure for stack safety on large nats. The
      # operator does O(1) field projection on a concrete value; no deferred
      # continuation work accumulates, so the integer key suffices for dedup
      # and deepSeq-in-key would add O(N²) cost.
      if t == "nat" then
        let
          isDescSucc = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInr"
            && v.d.val.tag == "VPair";
          isDescZero = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInl";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              if isDescSucc item.val
              then [{ key = item.key + 1; val = item.val.d.val.fst; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
        in
          if isDescZero last.val
          then builtins.length chain - 1
          else throw "extract: Nat value is not a numeral (stuck at ${last.val.tag})"

      else if t == "bool" then
        if val.tag == "VTrue" then true
        else if val.tag == "VFalse" then false
        else throw "extract: Bool value is not true/false (got ${val.tag})"

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
        #   nil:       VDescCon D (VInl _ _ VRefl)
        #   cons h t:  VDescCon D (VInr _ _ (VPair h (VPair t VRefl)))
        # elemTyVal is recovered from the outer description: D = VDescPlus A B,
        # B = VDescArg elem (_: descRec descRet), whose .S is elem.
        # Trampolined via genericClosure for stack safety.
        let
          elemTy = hoasTy.elem;
          isDescCons = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInr"
            && v.d.val.tag == "VPair"
            && v.d.val.snd.tag == "VPair";
          isDescNil = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInl";
          elemTyVal =
            if tyVal.tag == "VMu" && tyVal.D.tag == "VDescPlus"
               && tyVal.D.B.tag == "VDescArg"
            then tyVal.D.B.S
            else throw "extract: list tyVal must be VMu(plus _ (descArg _ _)), got ${tyVal.tag}";
          chain = builtins.genericClosure {
            startSet = [{ key = 0; inherit val; }];
            operator = item:
              if isDescCons item.val
              then [{ key = item.key + 1; val = item.val.d.val.snd.fst; }]
              else [];
          };
          n = builtins.length chain;
          last = builtins.elemAt chain (n - 1);
        in
          if !(isDescNil last.val)
          then throw "extract: List is not a proper cons/nil chain (stuck at ${last.val.tag})"
          else builtins.genList (i:
            let item = (builtins.elemAt chain i).val; in
            self.extractInner elemTy elemTyVal item.d.val.fst
          ) (n - 1)

      else if t == "sum" then
        # H.sum l r elaborates to μ(sumDesc l r), so every value of type Sum
        # arrives as a single-layer VDescCon. Under the plus-based
        # sumDesc l r = plus (descArg l (_: descRet)) (descArg r (_: descRet)):
        #   inl a: VDescCon D (VInl _ _ (VPair a VRefl))
        #   inr b: VDescCon D (VInr _ _ (VPair b VRefl))
        # Branch element type is recovered from D = VDescPlus A B, where
        # A = VDescArg l (_: descRet), B = VDescArg r (_: descRet).
        let
          isDescInl = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInl"
            && v.d.val.tag == "VPair";
          isDescInr = v:
            v.tag == "VDescCon"
            && v.d.tag == "VInr"
            && v.d.val.tag == "VPair";
          armTy = side:
            if tyVal.tag == "VMu" && tyVal.D.tag == "VDescPlus" then
              let sub = if side == "L" then tyVal.D.A else tyVal.D.B; in
              if sub.tag == "VDescArg" then sub.S
              else throw "extract: sum tyVal has non-sum description (sub-${side}=${sub.tag})"
            else throw "extract: sum tyVal must be VMu(plus _ _), got ${tyVal.tag}";
        in
        if isDescInl val then
          { _tag = "Left"; value = self.extractInner hoasTy.left (armTy "L") val.d.val.fst; }
        else if isDescInr val then
          { _tag = "Right"; value = self.extractInner hoasTy.right (armTy "R") val.d.val.fst; }
        else throw "extract: Sum value is neither inl nor inr (got ${val.tag})"

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
        # Maybe = Sum(inner, Unit). VInl = value present, VInr = null
        if val.tag == "VInl" then self.extractInner hoasTy.inner tyVal.left val.val
        else if val.tag == "VInr" then null
        else throw "extract: Maybe value is neither inl nor inr (got ${val.tag})"

      else if t == "variant" then
        let
          branches = hoasTy.branches;
          extractBranch = bs: tyV: v:
            let n = builtins.length bs; in
            if n == 1 then
              { _tag = (builtins.head bs).tag; value = self.extractInner (builtins.head bs).type tyV v; }
            else
              let b1 = builtins.head bs; rest = builtins.tail bs; in
              if v.tag == "VInl" then
                { _tag = b1.tag; value = self.extractInner b1.type tyV.left v.val; }
              else if v.tag == "VInr" then
                extractBranch rest tyV.right v.val
              else throw "extract: Variant value is neither inl nor inr (got ${v.tag})";
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
          descTyVal = tyVal.D;
          meta = hoasTy._dtypeMeta or null;

          # Description-shape predicates under the plus-coproduct encoding.
          # NatPlus: A=descRet, B=descRec descRet.
          isNatPlusDesc = d:
            d.tag == "VDescPlus"
            && d.A.tag == "VDescRet"
            && d.B.tag == "VDescRec"
            && d.B.D.tag == "VDescRet";
          # ListPlus(elem): A=descRet, B=descArg elem (_: descRec descRet).
          # The inner body is instantiated at VTt (placeholder; the closure
          # ignores its argument for listDesc).
          isListPlusDesc = d:
            d.tag == "VDescPlus"
            && d.A.tag == "VDescRet"
            && d.B.tag == "VDescArg"
            && (let body = E.instantiate d.B.T V.vTt; in
                body.tag == "VDescRec" && body.D.tag == "VDescRet");
          # SumPlus(l,r): A=descArg l (_: descRet), B=descArg r (_: descRet).
          isSumPlusDesc = d:
            d.tag == "VDescPlus"
            && d.A.tag == "VDescArg"
            && d.B.tag == "VDescArg"
            && (let bA = E.instantiate d.A.T V.vTt;
                    bB = E.instantiate d.B.T V.vTt; in
                bA.tag == "VDescRet" && bB.tag == "VDescRet");
          # BoolPlus shape: D = VDescPlus (VDescRet VTt) (VDescRet VTt).
          # Each summand is a non-recursive retI leaf; val.d is VInl/VInr
          # from plus's kernel-Sum interpretation. Covers both the
          # prelude `boolDesc` and the datatype-macro-generated n=2 spine
          # where both ctors are fieldless.
          isBoolPlusShape = d:
            d.tag == "VDescPlus"
            && d.A.tag == "VDescRet" && d.A.j.tag == "VTt"
            && d.B.tag == "VDescRet" && d.B.j.tag == "VTt";
          # UnitDT shape: bare descRet (n=1).
          isUnitDTShape = d:
            d.tag == "VDescRet";

          # Generic decomposition for non-prelude shapes. Walks the plus
          # spine to determine the constructor index, then walks the per-arm
          # data spine to extract fields. `pickArm` recurses through nested
          # VDescPlus layers — VInl commits to the current summand
          # (d.A), VInr descends into the rest-spine (d.B), advancing
          # ctorIdx on every VInr step. `extractFields` recurses through
          # the per-arm data spine (VDescArg → field, VDescRec → recursive
          # value, VDescPi → opaque function, VDescRet → terminus).
          pickArm = idx: dTy: pl:
            if dTy.tag == "VDescPlus" then
              if pl.tag == "VInl" then pickArm idx dTy.A pl.val
              else if pl.tag == "VInr" then pickArm (idx + 1) dTy.B pl.val
              else throw "extract: mu plus-tag is neither VInl/VInr (got ${pl.tag})"
            else { ctorIdx = idx; armDesc = dTy; armPayload = pl; };
          extractFields = dTy: pl:
            if dTy.tag == "VDescRet" then []
            else if dTy.tag == "VDescArg" then
              let fieldVal = pl.fst;
                  rest = pl.snd;
                  fieldHoas = self.reifyType dTy.S;
                  fieldNix = self.extractInner fieldHoas dTy.S fieldVal;
                  subDesc = E.instantiate dTy.T fieldVal;
              in [ fieldNix ] ++ extractFields subDesc rest
            else if dTy.tag == "VDescRec" then
              let recVal = pl.fst;
                  rest = pl.snd;
                  recNix = self.extractInner hoasTy tyVal recVal;
              in [ recNix ] ++ extractFields dTy.D rest
            else if dTy.tag == "VDescPi" then
              # Opaque lambda field: return the kernel VLam wrapped as a
              # Nix function via the existing pi-extract discipline. Domain
              # is reified; codomain is the outer mu's hoasTy (rec under Pi).
              let lamVal = pl.fst;
                  rest = pl.snd;
                  domainHoas = self.reifyType dTy.S;
                  piHoas = H.forall "_" domainHoas (_: hoasTy);
                  piTyVal = V.vPi "_" dTy.S (V.mkClosure [] (H.elab hoasTy));
                  lamNix = self.extractInner piHoas piTyVal lamVal;
              in [ lamNix ] ++ extractFields dTy.D rest
            else throw "extract: mu generic decomposition: unsupported VDesc tag '${dTy.tag}'";

        in
        if val.tag != "VDescCon"
        then throw "extract: mu value is not a VDescCon (got ${val.tag})"
        else if isUnitDTShape descTyVal then null
        else if isBoolPlusShape descTyVal then
          if val.d.tag == "VInl" then true
          else if val.d.tag == "VInr" then false
          else throw "extract: BoolPlus-shape value tag is neither VInl/VInr (got ${val.d.tag})"
        else if isNatPlusDesc descTyVal
        then self.extractInner { _htag = "nat"; } tyVal val
        else if isListPlusDesc descTyVal then
          let elemTyVal = descTyVal.B.S;
          in self.extractInner { _htag = "list"; elem = self.reifyType elemTyVal; } tyVal val
        else if isSumPlusDesc descTyVal then
          let leftTyVal = descTyVal.A.S;
              rightTyVal = descTyVal.B.S;
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

  tests = {};
}
