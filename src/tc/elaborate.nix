# Type-checking kernel: Elaboration bridge
#
# Bridges fx.types to kernel term representation (de Bruijn Tm)
# via the HOAS surface combinator layer.
#
# Eight operations:
#   elaborateType    : FxType → HoasTree              (type level)
#   elaborateValue   : HoasTree → NixVal → HoasTree   (value level: Nix → HOAS)
#   validateValue    : String → HoasTree → NixVal → [Error]  (structural validation)
#   extract          : HoasTree → Val → NixValue       (value level: kernel → Nix)
#   extractInner     : HoasTree → Val → Val → NixValue (3-arg: HOAS + type val + val)
#   reifyType        : Val → HoasTree                  (kernel type val → HOAS fallback)
#   decide           : HoasTree → NixVal → Bool        (decision procedure)
#   decideType       : FxType → NixVal → Bool          (elaborate type then decide)
#   verifyAndExtract : HoasTree → HoasTree → NixValue  (full pipeline)
#
# elaborateType dispatches on:
#   1. _kernel field (types built via mkType with kernelType)
#   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
#   3. Name convention (Bool, Nat, Unit, Null, String, Int, Float, ...)
#
# elaborateValue uses sentinel tests for non-dependent Pi/Sigma detection.
# extract uses kernel type value threading (no sentinel tests).
#
# Spec reference: kernel-mvp-research.md §3
{ fx, api, ... }:

let
  inherit (api) mk;
  H = fx.tc.hoas;
  E = fx.tc.eval;

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
    in r1.success && r2.success && r1.value.name == r2.value.name;

  # -- Type elaboration --
  #
  # Dispatches on:
  #   1. _kernel annotation (annotated types from this module)
  #   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
  #   3. Name convention (Bool, Nat, Unit, Null)
  elaborateType = type:
    if !(builtins.isAttrs type) then
      throw "elaborateType: expected a type attrset"
    else if type ? _kernel then type._kernel
    else if isPi type then
      if isConstantFamily type.codomain
      then H.forall "x" (elaborateType type.domain) (_: elaborateType (type.codomain _s1))
      else throw "elaborateType: dependent Pi requires _kernel annotation"
    else if isSigma type then
      if isConstantFamily type.sndFamily
      then H.sigma "x" (elaborateType type.fstType) (_: elaborateType (type.sndFamily _s1))
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

  # -- Value elaboration --
  #
  # Dispatches on HOAS type tag (_htag) to produce HOAS value tree.
  # Guards ensure clean throws (catchable by tryEval) for invalid values.
  elaborateValue = hoasTy: value:
    let t = hoasTy._htag or (throw "elaborateValue: not an HOAS type node"); in

    if t == "bool" then
      if !(builtins.isBool value)
      then throw "elaborateValue: Bool requires boolean, got ${builtins.typeOf value}"
      else if value then H.true_ else H.false_

    else if t == "nat" then
      if !(builtins.isInt value) || value < 0
      then throw "elaborateValue: Nat requires non-negative integer"
      else H.natLit value

    else if t == "unit" then
      if value != null
      then throw "elaborateValue: Unit requires null"
      else H.tt

    else if t == "string" then
      if !(builtins.isString value)
      then throw "elaborateValue: String requires string, got ${builtins.typeOf value}"
      else H.stringLit value

    else if t == "int" then
      if !(builtins.isInt value)
      then throw "elaborateValue: Int requires integer, got ${builtins.typeOf value}"
      else H.intLit value

    else if t == "float" then
      if !(builtins.isFloat value)
      then throw "elaborateValue: Float requires float, got ${builtins.typeOf value}"
      else H.floatLit value

    else if t == "attrs" then
      if !(builtins.isAttrs value)
      then throw "elaborateValue: Attrs requires attrset, got ${builtins.typeOf value}"
      else H.attrsLit

    else if t == "path" then
      if !(builtins.isPath value)
      then throw "elaborateValue: Path requires path, got ${builtins.typeOf value}"
      else H.pathLit

    else if t == "function" then
      if !(builtins.isFunction value)
      then throw "elaborateValue: Function requires function, got ${builtins.typeOf value}"
      else H.fnLit

    else if t == "any" then H.anyLit

    else if t == "list" then
      if !(builtins.isList value)
      then throw "elaborateValue: List requires a list"
      else
        let
          elemTy = hoasTy.elem;
          len = builtins.length value;
        in builtins.foldl' (acc: i:
          let v = builtins.elemAt value (len - 1 - i); in
          H.cons elemTy (elaborateValue elemTy v) acc
        ) (H.nil elemTy) (builtins.genList (x: x) len)

    else if t == "sum" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then throw "elaborateValue: Sum requires { _tag = \"Left\"|\"Right\"; value = ...; }"
      else if value._tag == "Left"
      then H.inl hoasTy.left hoasTy.right (elaborateValue hoasTy.left value.value)
      else if value._tag == "Right"
      then H.inr hoasTy.left hoasTy.right (elaborateValue hoasTy.right value.value)
      else throw "elaborateValue: Sum _tag must be \"Left\" or \"Right\""

    else if t == "sigma" then
      if !(builtins.isAttrs value && value ? fst && value ? snd)
      then throw "elaborateValue: Sigma requires { fst; snd; }"
      else
        let
          # Guard: dependent sigma (body uses its argument) cannot be elaborated
          # from a plain Nix value — the second type depends on the first value's
          # HOAS representation, which we can't reconstruct here. Use explicit
          # _kernel annotation on the type for dependent sigma elaboration.
          _hs1 = { _htag = "nat"; _sentinel = 1; };
          _hs2 = { _htag = "nat"; _sentinel = 2; };
          r1 = builtins.tryEval (hoasTy.body _hs1);
          r2 = builtins.tryEval (hoasTy.body _hs2);
          sndTy =
            if r1.success && r2.success && H.elab r1.value == H.elab r2.value
            then r1.value
            else throw "elaborateValue: dependent Sigma requires explicit _kernel annotation";
        in H.pair
          (elaborateValue hoasTy.fst value.fst)
          (elaborateValue sndTy value.snd)
          hoasTy

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      let
        fields = hoasTy.fields;
        n = builtins.length fields;
      in
        if !(builtins.isAttrs value)
        then throw "elaborateValue: Record requires attrset, got ${builtins.typeOf value}"
        else if n == 0 then H.tt
        else if n == 1 then
          let f = builtins.head fields; in
          elaborateValue f.type value.${f.name}
        else
          # Build nested pairs right-to-left
          let
            buildPairs = remaining: v:
              if builtins.length remaining == 1 then
                elaborateValue (builtins.head remaining).type v.${(builtins.head remaining).name}
              else
                let
                  f = builtins.head remaining;
                  rest = builtins.tail remaining;
                  sigTy = H.sigma f.name f.type (_: { _htag = "record"; fields = rest; });
                in H.pair
                  (elaborateValue f.type v.${f.name})
                  (buildPairs rest v)
                  sigTy;
          in buildPairs fields value

    else if t == "maybe" then
      # Maybe = Sum(inner, Unit). null → Right(tt), value → Left(value)
      if value == null
      then H.inr hoasTy.inner H.unit H.tt
      else H.inl hoasTy.inner H.unit (elaborateValue hoasTy.inner value)

    else if t == "variant" then
      let branches = hoasTy.branches; in
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then throw "elaborateValue: Variant requires { _tag; value; }"
      else
        let
          # Find the matching branch and build nested inl/inr injection
          inject = bs: v:
            let n = builtins.length bs; in
            if n == 1 then
              elaborateValue (builtins.head bs).type v.value
            else
              let
                b1 = builtins.head bs;
                rest = builtins.tail bs;
                restTy = { _htag = "variant"; branches = rest; };
              in
                if v._tag == b1.tag
                then H.inl b1.type restTy (elaborateValue b1.type v.value)
                else H.inr b1.type restTy (inject rest v);
        in inject branches value

    else throw "elaborateValue: unsupported type tag '${t}'";

  # -- Structural validation --
  #
  # validateValue : String → HoasTree → NixVal → [{ path; msg; }]
  #
  # Mirrors elaborateValue's structural recursion over HOAS type tags but
  # returns a list of errors instead of producing HOAS terms or throwing.
  # Empty list means the value would elaborate successfully.
  #
  # Design:
  #   elaborateValue is monadic (Either) — fails fast on the first error.
  #   validateValue is applicative (Validation) — accumulates all errors.
  #   These are different morphisms: one produces values, the other diagnostics.
  #   The path accumulator is the Reader effect (inherited attribute in the fold).
  #   The error list is the Writer effect (free monoid).
  #
  # Soundness: checks the same predicates as elaborateValue. If validateValue
  # returns [] then elaborateValue will not throw (and vice versa). Both have
  # catch-all branches for unknown tags, so they cannot silently diverge.
  validateValue = path: hoasTy: value:
    let t = hoasTy._htag or "invalid"; in

    # -- Scalar types --

    if t == "bool" then
      if !(builtins.isBool value)
      then [{ inherit path; msg = "expected bool, got ${builtins.typeOf value}"; }]
      else []

    else if t == "nat" then
      if !(builtins.isInt value) || value < 0
      then [{ inherit path; msg = "expected non-negative integer, got ${builtins.typeOf value}"; }]
      else []

    else if t == "unit" then
      if value != null
      then [{ inherit path; msg = "expected null (unit), got ${builtins.typeOf value}"; }]
      else []

    else if t == "string" then
      if !(builtins.isString value)
      then [{ inherit path; msg = "expected string, got ${builtins.typeOf value}"; }]
      else []

    else if t == "int" then
      if !(builtins.isInt value)
      then [{ inherit path; msg = "expected integer, got ${builtins.typeOf value}"; }]
      else []

    else if t == "float" then
      if !(builtins.isFloat value)
      then [{ inherit path; msg = "expected float, got ${builtins.typeOf value}"; }]
      else []

    else if t == "attrs" then
      if !(builtins.isAttrs value)
      then [{ inherit path; msg = "expected attrset, got ${builtins.typeOf value}"; }]
      else []

    else if t == "path" then
      if !(builtins.isPath value)
      then [{ inherit path; msg = "expected path, got ${builtins.typeOf value}"; }]
      else []

    else if t == "function" then
      if !(builtins.isFunction value)
      then [{ inherit path; msg = "expected function, got ${builtins.typeOf value}"; }]
      else []

    else if t == "any" then []

    # -- List: validate every element with indexed path --

    else if t == "list" then
      if !(builtins.isList value)
      then [{ inherit path; msg = "expected list, got ${builtins.typeOf value}"; }]
      else
        let
          elemTy = hoasTy.elem;
          len = builtins.length value;
        in builtins.concatMap (i:
          validateValue "${path}[${toString i}]" elemTy (builtins.elemAt value i)
        ) (builtins.genList (x: x) len)

    # -- Sum: validate tag structure then recurse into branch --

    else if t == "sum" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then [{ inherit path; msg = "expected { _tag = \"Left\"|\"Right\"; value = ...; }"; }]
      else if value._tag == "Left" then validateValue "${path}.Left" hoasTy.left value.value
      else if value._tag == "Right" then validateValue "${path}.Right" hoasTy.right value.value
      else [{ inherit path; msg = "_tag must be \"Left\" or \"Right\", got \"${value._tag}\""; }]

    # -- Sigma: non-dependent only (same sentinel test as elaborateValue) --

    else if t == "sigma" then
      if !(builtins.isAttrs value && value ? fst && value ? snd)
      then [{ inherit path; msg = "expected { fst; snd; }"; }]
      else
        let
          _hs1 = { _htag = "nat"; _sentinel = 1; };
          _hs2 = { _htag = "nat"; _sentinel = 2; };
          r1 = builtins.tryEval (hoasTy.body _hs1);
          r2 = builtins.tryEval (hoasTy.body _hs2);
        in
        if !(r1.success && r2.success && H.elab r1.value == H.elab r2.value)
        then [{ inherit path; msg = "dependent Sigma requires explicit _kernel annotation"; }]
        else
          (validateValue "${path}.fst" hoasTy.fst value.fst)
          ++ (validateValue "${path}.snd" r1.value value.snd)

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      if !(builtins.isAttrs value)
      then [{ inherit path; msg = "expected record (attrset), got ${builtins.typeOf value}"; }]
      else
        builtins.concatMap (f:
          if !(builtins.hasAttr f.name value)
          then [{ path = "${path}.${f.name}"; msg = "missing required field"; }]
          else validateValue "${path}.${f.name}" f.type value.${f.name}
        ) (hoasTy.fields or [])

    else if t == "maybe" then
      if value == null then []
      else validateValue path hoasTy.inner value

    else if t == "variant" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then [{ inherit path; msg = "expected { _tag; value; }"; }]
      else
        let
          branches = hoasTy.branches;
          matching = builtins.filter (b: b.tag == value._tag) branches;
        in
        if matching == []
        then [{ inherit path; msg = "unknown variant tag \"${value._tag}\"; expected one of: ${builtins.concatStringsSep ", " (map (b: "\"${b.tag}\"") branches)}"; }]
        else validateValue "${path}.${value._tag}" (builtins.head matching).type value.value

    else [{ inherit path; msg = "unsupported type tag '${t}'"; }];

  # -- Reification: kernel type value → HOAS type --
  #
  # reifyType : Val → HoasTree
  # Converts a kernel type value back to an HOAS type for extract dispatch.
  # Used as fallback when the HOAS body cannot be applied (dependent types).
  # Loses sugar (VSigma → H.sigma, not H.record) — HOAS body is preferred
  # when available since it preserves record/variant/maybe structure.
  reifyType = tyVal:
    let t = tyVal.tag; in
    if t == "VNat" then H.nat
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
    else if t == "VList" then H.listOf (reifyType tyVal.elem)
    else if t == "VSum" then H.sum (reifyType tyVal.left) (reifyType tyVal.right)
    else if t == "VSigma" then
      H.sigma tyVal.name (reifyType tyVal.fst)
        (x: reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
    else if t == "VPi" then
      H.forall tyVal.name (reifyType tyVal.domain)
        (x: reifyType (E.instantiate tyVal.closure (E.eval [] (H.elab x))))
    else if t == "VU" then H.u tyVal.level
    else throw "reifyType: unsupported value tag '${t}'";

  # -- Value extraction (internal) --
  #
  # extractInner : HoasTree → Val → Val → NixValue
  # Three-argument extraction: HOAS type (for dispatch and sugar), kernel type
  # value (for dependent codomain/snd computation), and kernel value to extract.
  # Uses closure instantiation instead of sentinel tests for dependent types.
  extractInner = hoasTy: tyVal: val:
    let t = hoasTy._htag or (throw "extract: not an HOAS type"); in

    # Nat: VZero → 0, VSucc^n(VZero) → n
    # Trampolined via genericClosure for stack safety on large nats
    if t == "nat" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; inherit val; }];
          operator = item:
            if item.val.tag == "VSucc"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        last = builtins.elemAt chain (builtins.length chain - 1);
      in
        if last.val.tag == "VZero" then builtins.length chain - 1
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
      # VNil → [], VCons(h,t) → [extract(h)] ++ rest
      # Trampolined via genericClosure for stack safety on large lists
      let
        elemTy = hoasTy.elem;
        chain = builtins.genericClosure {
          startSet = [{ key = 0; inherit val; }];
          operator = item:
            if item.val.tag == "VCons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        n = builtins.length chain;
        last = builtins.elemAt chain (n - 1);
      in
        if last.val.tag != "VNil"
        then throw "extract: List is not a proper cons/nil chain (stuck at ${last.val.tag})"
        else builtins.genList (i:
          extractInner elemTy tyVal.elem (builtins.elemAt chain i).val.head
        ) (n - 1)

    else if t == "sum" then
      if val.tag == "VInl" then { _tag = "Left"; value = extractInner hoasTy.left tyVal.left val.val; }
      else if val.tag == "VInr" then { _tag = "Right"; value = extractInner hoasTy.right tyVal.right val.val; }
      else throw "extract: Sum value is neither inl nor inr (got ${val.tag})"

    else if t == "sigma" then
      let
        fstNix = extractInner hoasTy.fst tyVal.fst val.fst;
        sndTyVal = E.instantiate tyVal.closure val.fst;
        r = builtins.tryEval (hoasTy.body { _htag = "unit"; });
        sndHoas = if r.success then r.value else reifyType sndTyVal;
      in { fst = fstNix; snd = extractInner sndHoas sndTyVal val.snd; }

    # -- Compound types (record, maybe, variant) --

    else if t == "record" then
      let
        fields = hoasTy.fields;
        n = builtins.length fields;
      in
        if n == 0 then {}
        else if n == 1 then
          { ${(builtins.head fields).name} = extractInner (builtins.head fields).type tyVal val; }
        else
          let
            extractFields = remaining: tyV: v:
              if builtins.length remaining == 1 then
                { ${(builtins.head remaining).name} = extractInner (builtins.head remaining).type tyV v; }
              else
                let
                  f = builtins.head remaining;
                  rest = builtins.tail remaining;
                  sndTyVal = E.instantiate tyV.closure v.fst;
                in
                { ${f.name} = extractInner f.type tyV.fst v.fst; }
                // extractFields rest sndTyVal v.snd;
          in extractFields fields tyVal val

    else if t == "maybe" then
      # Maybe = Sum(inner, Unit). VInl = value present, VInr = null
      if val.tag == "VInl" then extractInner hoasTy.inner tyVal.left val.val
      else if val.tag == "VInr" then null
      else throw "extract: Maybe value is neither inl nor inr (got ${val.tag})"

    else if t == "variant" then
      let
        branches = hoasTy.branches;
        extractBranch = bs: tyV: v:
          let n = builtins.length bs; in
          if n == 1 then
            { _tag = (builtins.head bs).tag; value = extractInner (builtins.head bs).type tyV v; }
          else
            let b1 = builtins.head bs; rest = builtins.tail bs; in
            if v.tag == "VInl" then
              { _tag = b1.tag; value = extractInner b1.type tyV.left v.val; }
            else if v.tag == "VInr" then
              extractBranch rest tyV.right v.val
            else throw "extract: Variant value is neither inl nor inr (got ${v.tag})";
      in extractBranch branches tyVal val

    else if t == "pi" then
      # Extract a verified function.
      # Returns a Nix function that:
      #   1. Elaborates its argument to HOAS → kernel value
      #   2. Applies the VLam closure
      #   3. Extracts the result back to a Nix value
      # Codomain type is computed per-invocation from the type's closure,
      # supporting both dependent and non-dependent Pi.
      let domainTy = hoasTy.domain; in
        nixArg:
          let
            hoasArg = elaborateValue domainTy nixArg;
            kernelArg = E.eval [] (H.elab hoasArg);
            resultVal = E.instantiate val.closure kernelArg;
            codomainTyVal = E.instantiate tyVal.closure kernelArg;
            r = builtins.tryEval (hoasTy.body hoasArg);
            codomainHoas = if r.success then r.value else reifyType codomainTyVal;
          in extractInner codomainHoas codomainTyVal resultVal

    else throw "extract: unsupported type '${t}'";

  # -- Value extraction (public API) --
  #
  # extract : HoasTree → Val → NixValue
  # Computes kernel type value from HOAS type, then delegates to extractInner.
  extract = hoasTy: val:
    let tyVal = E.eval [] (H.elab hoasTy);
    in extractInner hoasTy tyVal val;

  # -- verifyAndExtract : HoasTree → HoasTree → NixValue --
  # Full pipeline: type-check HOAS term → eval → extract to Nix value.
  # Computes kernel type value once and uses extractInner directly.
  verifyAndExtract = hoasTy: hoasImpl:
    let
      checked = H.checkHoas hoasTy hoasImpl;
    in if checked ? error
      then throw "verifyAndExtract: type check failed"
      else
        let
          tm = H.elab hoasImpl;
          val = E.eval [] tm;
          tyVal = E.eval [] (H.elab hoasTy);
        in extractInner hoasTy tyVal val;

  # -- Decision procedure --
  #
  # decide : HoasTree → NixValue → Bool
  # Returns true iff both elaboration and kernel type-checking succeed.
  # Uses tryEval to catch elaboration throws and checks for kernel errors.
  decide = hoasTy: value:
    let
      result = builtins.tryEval (
        let
          hoasVal = elaborateValue hoasTy value;
          checked = H.checkHoas hoasTy hoasVal;
        in !(checked ? error)
      );
    in result.success && result.value;

  # -- Convenience: elaborate type then decide --
  decideType = type: value:
    decide (elaborateType type) value;

in mk {
  doc = ''
    # fx.tc.elaborate — Elaboration Bridge

    Bridges the fx.types layer to the kernel's term representation
    via the HOAS combinator layer. Provides the Nix ↔ kernel boundary.

    Spec reference: kernel-mvp-research.md §3.

    ## Type Elaboration

    - `elaborateType : FxType → Hoas` — convert an fx.types type descriptor
      to an HOAS tree. Dispatches on: (1) `_kernel` annotation, (2) structural
      fields (Pi: domain/codomain, Sigma: fstType/sndFamily), (3) name
      convention (Bool, Nat, String, Int, Float, ...).
      Dependent Pi/Sigma require explicit `_kernel` annotation.

    ## Value Elaboration

    - `elaborateValue : Hoas → NixVal → Hoas` — convert a Nix value to
      an HOAS term tree given its HOAS type. Bool→true_/false_, Int→natLit,
      List→cons chain, Sum→inl/inr, Sigma→pair. Trampolined for large lists.

    ## Structural Validation

    - `validateValue : String → Hoas → NixVal → [{ path; msg; }]` —
      applicative structural validator. Mirrors `elaborateValue`'s recursion
      but accumulates all errors instead of throwing on the first.
      Path accumulator threads structural context (Reader effect).
      Error list is the free monoid (Writer effect).
      Empty list ↔ `elaborateValue` would succeed (soundness invariant).

    ## Value Extraction

    - `extract : Hoas → Val → NixValue` — reverse of `elaborateValue`.
      Converts kernel values back to Nix values. VZero→0, VSucc^n→n,
      VCons chain→list, VInl/VInr→tagged union.
      Pi extraction wraps the VLam as a Nix function with boundary conversion.
      Opaque types (Attrs, Path, Function, Any) throw — kernel discards payloads.
    - `extractInner : Hoas → Val → Val → NixValue` — three-argument extraction
      with kernel type value threading. Supports dependent Pi/Sigma via closure
      instantiation instead of sentinel tests.
    - `reifyType : Val → Hoas` — converts a kernel type value back to HOAS.
      Fallback for when HOAS body application fails (dependent types).
      Loses sugar (VSigma→sigma, not record).

    ## Decision Procedure

    - `decide : Hoas → NixVal → Bool` — returns true iff elaboration
      and kernel type-checking both succeed. Uses `tryEval` for safety.
    - `decideType : FxType → NixVal → Bool` — elaborate type then decide.

    ## Full Pipeline

    - `verifyAndExtract : Hoas → Hoas → NixValue` — type-check an HOAS
      implementation against an HOAS type, evaluate, extract to Nix value.
      Throws on type error.
  '';
  value = {
    inherit elaborateType elaborateValue validateValue extract extractInner reifyType verifyAndExtract decide decideType;
  };
  tests = let
    FP = fx.types.primitives;
    FC = fx.types.constructors;
    FD = fx.types.dependent;
    BoolT = FP.Bool;
    IntT = FP.Int;
    UnitT = FP.Unit;
    Arrow = domType: codType:
      FD.Pi { domain = domType; codomain = _: codType;
              universe = let a = domType.universe; b = codType.universe;
                         in if a >= b then a else b; };
    Product = fstType: sndType:
      FD.Sigma { fst = fstType; snd = _: sndType;
                 universe = let a = fstType.universe; b = sndType.universe;
                            in if a >= b then a else b; };
  in {
    # ===== Type elaboration: _kernel dispatch =====

    "elab-type-bool" = {
      expr = (elaborateType BoolT)._htag;
      expected = "bool";
    };
    "elab-type-int" = {
      expr = (elaborateType IntT)._htag;
      expected = "int";
    };
    "elab-type-unit" = {
      expr = (elaborateType UnitT)._htag;
      expected = "unit";
    };
    "elab-type-list-int" = {
      expr = (elaborateType (FC.ListOf IntT))._htag;
      expected = "list";
    };
    "elab-type-list-bool" = {
      expr = (elaborateType (FC.ListOf BoolT))._htag;
      expected = "list";
    };
    "elab-type-either" = {
      expr = (elaborateType (FC.Either IntT BoolT))._htag;
      expected = "sum";
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

    # ===== Type elaboration: structural auto-detection =====

    # Structural: non-dependent Pi auto-detected
    "elab-type-auto-pi" = {
      expr = let
        piT = FD.Pi { domain = BoolT; codomain = _: IntT; universe = 0; };
      in (elaborateType piT)._htag;
      expected = "pi";
    };

    # Structural: non-dependent Sigma auto-detected
    "elab-type-auto-sigma" = {
      expr = let
        sigT = FD.Sigma { fst = BoolT; snd = _: IntT; universe = 0; };
      in (elaborateType sigT)._htag;
      expected = "sigma";
    };

    # Dependent Pi (codomain uses argument) REJECTED without _kernel
    "reject-elab-dependent-pi" = {
      expr = let
        depPi = FD.Pi { domain = BoolT; codomain = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
      in (builtins.tryEval (elaborateType depPi)).success;
      expected = false;
    };

    # Dependent Sigma (snd uses argument) REJECTED without _kernel
    "reject-elab-dependent-sigma" = {
      expr = let
        depSig = FD.Sigma { fst = BoolT; snd = x: if x.name == "__elab_sentinel_1__" then IntT else BoolT; universe = 0; };
      in (builtins.tryEval (elaborateType depSig)).success;
      expected = false;
    };

    # ===== Value elaboration =====

    "elab-val-true" = {
      expr = (H.elab (elaborateValue H.bool true)).tag;
      expected = "true";
    };
    "elab-val-false" = {
      expr = (H.elab (elaborateValue H.bool false)).tag;
      expected = "false";
    };
    "elab-val-zero" = {
      expr = (H.elab (elaborateValue H.nat 0)).tag;
      expected = "zero";
    };
    "elab-val-nat-3" = {
      expr = (H.elab (elaborateValue H.nat 3)).tag;
      expected = "succ";
    };
    "elab-val-unit" = {
      expr = (H.elab (elaborateValue H.unit null)).tag;
      expected = "tt";
    };
    "elab-val-nil" = {
      expr = (H.elab (elaborateValue (H.listOf H.nat) [])).tag;
      expected = "nil";
    };
    "elab-val-cons" = {
      expr = (H.elab (elaborateValue (H.listOf H.nat) [0 1])).tag;
      expected = "cons";
    };
    "elab-val-inl" = {
      expr = (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 0; })).tag;
      expected = "inl";
    };
    "elab-val-inr" = {
      expr = (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; })).tag;
      expected = "inr";
    };
    "elab-val-pair" = {
      expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; })).tag;
      expected = "pair";
    };

    "elab-val-sigma-pi-snd" = {
      expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool))) { fst = 0; snd = _: true; })).tag;
      expected = "pair";
    };

    # ===== Decision procedure: positive =====

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
      expr = decide (H.listOf H.nat) [];
      expected = true;
    };
    "decide-list-nat" = {
      expr = decide (H.listOf H.nat) [0 1 2];
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

    # ===== Decision procedure: negative =====

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
      expr = decide (H.listOf H.nat) [true];
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

    # Stack safety: decide on large list (buildList + HOAS elab both trampolined)
    # Note: eval/check still recurse on cons chains, limiting full-pipeline depth.
    # The HOAS layer itself handles 5000+ (see hoas.nix elab-cons-5000 test).
    # Stack safety: full pipeline (elaborate → eval → check) trampolined for cons
    "decide-list-5000" = {
      expr = decide (H.listOf H.nat) (builtins.genList (x: x) 5000);
      expected = true;
    };

    # Dependent sigma cleanly rejected (tryEval catches the throw)
    "decide-dep-sigma-rejected" = {
      expr = decide (H.sigma "x" H.nat (x: H.eq H.nat x H.zero)) { fst = 0; snd = null; };
      expected = false;
    };

    # ===== Regression: decide(T,v) == T.check(v) =====

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
      expr = let lt = FC.ListOf IntT; in (decideType lt [0 1 2]) == (lt.check [0 1 2]);
      expected = true;
    };
    "regression-list-int-empty" = {
      expr = let lt = FC.ListOf IntT; in (decideType lt []) == (lt.check []);
      expected = true;
    };
    "regression-list-int-rejects-bad" = {
      expr = let lt = FC.ListOf IntT; in (decideType lt [true]) == (lt.check [true]);
      expected = true;
    };
    "regression-either-left-valid" = {
      expr = let et = FC.Either IntT BoolT; v = { _tag = "Left"; value = 0; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "regression-either-right-bad" = {
      expr = let et = FC.Either IntT BoolT; v = { _tag = "Right"; value = 42; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "regression-product-valid" = {
      expr = let pt = Product IntT BoolT; v = { fst = 0; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };
    "regression-product-bad-fst" = {
      expr = let pt = Product IntT BoolT; v = { fst = true; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };

    # ===== Primitive type elaboration: name-based auto-detection =====

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

    # ===== Value elaboration: primitives =====

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

    # ===== Decision procedure: primitive positives =====

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

    # ===== Decision procedure: primitive negatives =====

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
      expr = decide H.attrs [1 2];
      expected = false;
    };
    "decide-fn-rejects-string" = {
      expr = decide H.function_ "hello";
      expected = false;
    };

    # ===== Extraction: roundtrip tests =====
    # Roundtrip: extract(T, eval(elab(elaborateValue(T, v)))) == v

    "extract-nat-0" = {
      expr = extract H.nat (E.eval [] (H.elab (elaborateValue H.nat 0)));
      expected = 0;
    };
    "extract-nat-5" = {
      expr = extract H.nat (E.eval [] (H.elab (elaborateValue H.nat 5)));
      expected = 5;
    };
    "extract-bool-true" = {
      expr = extract H.bool (E.eval [] (H.elab (elaborateValue H.bool true)));
      expected = true;
    };
    "extract-bool-false" = {
      expr = extract H.bool (E.eval [] (H.elab (elaborateValue H.bool false)));
      expected = false;
    };
    "extract-unit" = {
      expr = extract H.unit (E.eval [] (H.elab (elaborateValue H.unit null)));
      expected = null;
    };
    "extract-string" = {
      expr = extract H.string (E.eval [] (H.elab (elaborateValue H.string "hello")));
      expected = "hello";
    };
    "extract-int" = {
      expr = extract H.int_ (E.eval [] (H.elab (elaborateValue H.int_ 42)));
      expected = 42;
    };
    "extract-float" = {
      expr = extract H.float_ (E.eval [] (H.elab (elaborateValue H.float_ 3.14)));
      expected = 3.14;
    };
    "extract-list-empty" = {
      expr = extract (H.listOf H.nat) (E.eval [] (H.elab (elaborateValue (H.listOf H.nat) [])));
      expected = [];
    };
    "extract-list-nat" = {
      expr = extract (H.listOf H.nat) (E.eval [] (H.elab (elaborateValue (H.listOf H.nat) [1 2 3])));
      expected = [1 2 3];
    };
    "extract-sum-left" = {
      expr = extract (H.sum H.nat H.bool) (E.eval [] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 42; })));
      expected = { _tag = "Left"; value = 42; };
    };
    "extract-sum-right" = {
      expr = extract (H.sum H.nat H.bool) (E.eval [] (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; })));
      expected = { _tag = "Right"; value = true; };
    };
    "extract-sigma" = {
      expr = let ty = H.sigma "x" H.nat (_: H.bool); in
        extract ty (E.eval [] (H.elab (elaborateValue ty { fst = 5; snd = true; })));
      expected = { fst = 5; snd = true; };
    };

    "extract-sigma-pi-snd" = {
      expr = let
        ty = H.sigma "x" H.nat (_: H.forall "y" H.nat (_: H.bool));
        hoasVal = H.pair (H.ann H.zero H.nat) (H.lam "y" H.nat (_: H.true_)) ty;
        val = E.eval [] (H.elab hoasVal);
        result = extract ty val;
      in (result.snd 0);
      expected = true;
    };

    # ===== Extraction: Pi (verified function) =====

    "extract-pi-identity" = {
      # Identity function: λ(x:Nat).x → extract → call with 5
      expr = let
        fnTy = H.forall "x" H.nat (_: H.nat);
        idFn = H.lam "x" H.nat (x: x);
        val = E.eval [] (H.elab idFn);
        nixFn = extract fnTy val;
      in nixFn 5;
      expected = 5;
    };
    "extract-pi-const" = {
      # Constant function: λ(x:Bool).0 → extract → call with true
      expr = let
        fnTy = H.forall "x" H.bool (_: H.nat);
        constFn = H.lam "x" H.bool (_: H.zero);
        val = E.eval [] (H.elab constFn);
        nixFn = extract fnTy val;
      in nixFn true;
      expected = 0;
    };

    # ===== verifyAndExtract pipeline =====

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
      expr = let
        fnTy = H.forall "x" H.nat (_: H.nat);
        fnImpl = H.lam "x" H.nat (x: x);
        nixFn = verifyAndExtract fnTy fnImpl;
      in nixFn 10;
      expected = 10;
    };
    "verify-extract-type-error" = {
      # Type error: Bool term against Nat type → throws
      expr = (builtins.tryEval (verifyAndExtract H.nat H.true_)).success;
      expected = false;
    };

    # ===== Extraction: stack safety =====

    "extract-list-5000" = {
      # Stack safety: extract a 5000-element list (booleans for O(1) per element)
      expr = builtins.length (
        extract (H.listOf H.bool)
          (E.eval [] (H.elab (elaborateValue (H.listOf H.bool)
            (builtins.genList (_: true) 5000))))
      );
      expected = 5000;
    };

    # ===== Extraction: opaque types throw =====

    "extract-attrs-throws" = {
      expr = (builtins.tryEval (extract H.attrs (E.eval [] (H.elab (elaborateValue H.attrs { x = 1; }))))).success;
      expected = false;
    };
    "extract-fn-throws" = {
      expr = (builtins.tryEval (extract H.function_ (E.eval [] (H.elab (elaborateValue H.function_ (x: x)))))).success;
      expected = false;
    };
  };
}
