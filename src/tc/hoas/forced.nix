# McBride-forced argument analysis for datatype constructors.
#
# A binder `b_i` of `c : (b_1) → … → (b_n) → R idx(b̄)` is *forced* iff
# `b_i` occurs in a strict (Miller-pattern) position of `idx(b̄)` or of
# `T_j` for some `j > i`. Forced binders recover by pattern unification
# from the conclusion alone; marking them implicit is decidability-
# preserving. McBride, "Inductive Families Need Not Store Their Indices"
# §5; mirrors Agda's force analysis.
#
# `mentionsOf t` collects `_signatureField`-tagged marker names from `t`.
# Markers carry `{ _signatureField = true; name; index; }` per
# `_datatypeImpl.fieldMarker` in `datatype.nix`.
{ self, api, ... }:

let
  # Stand-in for HOAS-bound variables when descending through binder
  # bodies. The tag is distinct from any marker so the walker can't
  # mistake the sentinel for a signature field.
  bodyProbe = { _htag = "forced-probe"; };

  mentionsOf = t: collect t [ ];

  collect = t: acc:
    if !(builtins.isAttrs t) then
      if builtins.isList t then
        builtins.foldl' (a: x: collect x a) acc t
      else acc
    else if (t._signatureField or false) then
      acc ++ [ t.name ]
    else
      collectByTag (t._htag or null) t acc;

  # Dispatch on `_htag`; descend into known HOAS subterm slots. Binder
  # bodies are invoked at `bodyProbe`. Unrecognised tags fall through to
  # a conservative attribute walk.
  collectByTag = tag: t: acc:
    if tag == "pi" || tag == "lam" then
      let acc1 = collect t.domain acc;
      in collect (t.body bodyProbe) acc1
    else if tag == "sigma" then
      let acc1 = collect t.fst acc;
      in collect (t.body bodyProbe) acc1
    else if tag == "let" then
      let
        acc1 = collect t.type acc;
        acc2 = collect t.val acc1;
      in
      collect (t.body bodyProbe) acc2
    else if tag == "app" then
      let acc1 = collect t.fn acc;
      in collect t.arg acc1
    else if tag == "pair" then
      let acc1 = collect t.fst acc;
      in collect t.snd acc1
    else if tag == "ann" then
      let acc1 = collect t.term acc;
      in collect t.type acc1
    else if tag == "fst" then collect t.pair acc
    else if tag == "snd" then collect t.pair acc
    else if tag == "absurd" then
      let acc1 = collect t.type acc;
      in collect t.term acc1
	    else if tag == "mu" && t ? _dtypeMeta then
	      let
	        acc1 = builtins.foldl'
	          (a: x: collect x a)
	          acc
	          (t._dtypeMeta.paramArgs or [ ]);
	      in
	      collect t.i acc1
	    else if tag == "mu" then
	      let
	        acc1 = collect t.I acc;
	        acc2 = collect t.D acc1;
      in
      collect t.i acc2
    else if tag == "desc" then
      collect t.I acc
    else if tag == "boot-eq" then
      let
        acc1 = collect t.type acc;
        acc2 = collect t.lhs acc1;
      in
      collect t.rhs acc2
    else if tag == "boot-j" || tag == "j" then
      let
        acc1 = collect t.type acc;
        acc2 = collect t.lhs acc1;
        acc3 = collect t.motive acc2;
        acc4 = collect t.base acc3;
        acc5 = collect t.rhs acc4;
      in
      collect t.eq acc5
    else if tag == "boot-sum" then
      let acc1 = collect t.L acc;
      in collect t.R acc1
    else if tag == "boot-inl" || tag == "boot-inr" then
      let
        acc1 = collect t.L acc;
        acc2 = collect t.R acc1;
      in
      collect t.term acc2
    else if tag == "boot-sum-elim" then
      let
        acc1 = collect t.left acc;
        acc2 = collect t.right acc1;
        acc3 = collect t.motive acc2;
        acc4 = collect t.onLeft acc3;
        acc5 = collect t.onRight acc4;
      in
      collect t.scrut acc5
    else if tag == "squash" then collect t.A acc
    else if tag == "squash-intro" then collect t.a acc
    else if tag == "squash-elim" then
      let
        acc1 = collect t.A acc;
        acc2 = collect t.B acc1;
        acc3 = collect t.f acc2;
      in
      collect t.x acc3
    else if tag == "level-suc" then collect t.pred acc
    else if tag == "level-max" then
      let acc1 = collect t.lhs acc;
      in collect t.rhs acc1
    else if tag == "maybe" || tag == "thunk" then collect t.inner acc
    else if tag == "variant" then
      builtins.foldl'
        (a: br: collect (br.type or br) a)
        acc
        (t.branches or [ ])
    else if tag == "str-eq" then
      let acc1 = collect t.lhs acc;
      in collect t.rhs acc1
    else if tag == "opaque-lam" then
      collect (t.nixFn bodyProbe) acc
    else if isLeafTag tag then acc
    else conservativeWalk t acc;

  isLeafTag = tag:
    tag == "pre-elab" || tag == "lit-val"
    || tag == "string-lit" || tag == "int-lit" || tag == "float-lit"
    || tag == "attrs-lit" || tag == "path-lit" || tag == "derivation-lit"
    || tag == "fn-lit" || tag == "any-lit"
    || tag == "string" || tag == "int" || tag == "float" || tag == "attrs"
    || tag == "path" || tag == "derivation" || tag == "function" || tag == "any"
    || tag == "level" || tag == "level-zero" || tag == "U"
    || tag == "unit" || tag == "tt" || tag == "empty"
    || tag == "boot-refl" || tag == "refl" || tag == "funext"
    || tag == "forced-probe";

  # Fallback descent. Walks attrset slots that could carry HOAS subterms
  # (nested attrsets, lists, functions). Skips primitives.
  conservativeWalk = t: acc:
    builtins.foldl'
      (a: k:
        let v = t.${k}; in
        if builtins.isAttrs v then collect v a
        else if builtins.isList v then
          builtins.foldl' (aa: x: collect x aa) a v
        else if builtins.isFunction v then collect (v bodyProbe) a
        else a)
      acc
      (builtins.attrNames t);

  # Only data/dataD fields extend `prev`. Matches `_datatypeImpl.extendsPrev`.
  extendsPrevField = f: f.kind == "data" || f.kind == "dataD";

  buildPrev = fields: markers:
    builtins.foldl'
      (acc: i:
        let f = builtins.elemAt fields i; in
        if extendsPrevField f
        then acc // { ${f.name} = builtins.elemAt markers i; }
        else acc)
      { }
      (builtins.genList (x: x) (builtins.length fields));

  prevBefore = fields: markers: j:
    builtins.foldl'
      (acc: i:
        let f = builtins.elemAt fields i; in
        if i < j && extendsPrevField f
        then acc // { ${f.name} = builtins.elemAt markers i; }
        else acc)
      { }
      (builtins.genList (x: x) (builtins.length fields));

  defaultMarker = f: i: {
    _signatureField = true;
    inherit (f) name;
    index = i;
  };

	  # When `fieldTyOf` is null, degenerates to "appears in conclusion".
	  forcedFieldNames = { fields, targetIdx, fieldTyOf ? null }:
	    let
	      nFields = builtins.length fields;
      markers = builtins.genList
        (i: defaultMarker (builtins.elemAt fields i) i)
        nFields;
      prevFull = buildPrev fields markers;

      inTargetIdx = mentionsOf (targetIdx prevFull);

	      fieldMentions = f: prev:
	        if f.kind == "data" || f.kind == "pi" then [ ]
	        else if f.kind == "dataD" then mentionsOf (f.typeFn prev)
	        else if f.kind == "recAt" then mentionsOf (f.idxFn prev)
	        else if f.kind == "piAt" then mentionsOf (f.branchIdxFn prev bodyProbe)
	        else if f.kind == "piD" then mentionsOf (f.SFn prev)
	        else if f.kind == "piDAt" then
	          mentionsOf (f.SFn prev) ++ mentionsOf (f.branchIdxFn prev bodyProbe)
	        else mentionsOf (fieldTyOf f prev);

	      inLaterTypes =
	        if fieldTyOf == null then [ ]
	        else
	          builtins.concatLists (builtins.genList
	            (j:
	              let
	                f = builtins.elemAt fields j;
	                prevJ = prevBefore fields markers j;
	              in
	              fieldMentions f prevJ)
	            nFields);

      allMentions = inTargetIdx ++ inLaterTypes;
      fieldNames = map (f: f.name) fields;
    in
    builtins.filter (n: builtins.elem n allMentions) fieldNames;

  forcedFieldSet = spec:
    let names = forcedFieldNames spec; in
    builtins.listToAttrs (map (n: { name = n; value = true; }) names);

  isFieldForced = spec: name:
    builtins.elem name (forcedFieldNames spec);

in
{
  scope = {
    mentionsOf = api.leaf {
      value = mentionsOf;
      description = "Collect `_signatureField` marker names occurring in a HOAS term. Binder bodies are descended by applying their closure to a `forced-probe` sentinel.";
      signature = "Hoas -> [String]";
    };
    forcedFieldNames = api.leaf {
      value = forcedFieldNames;
      description = "McBride-forced subset of a constructor's fields: a field is forced iff its sentinel marker occurs in `targetIdx prevFull` or in `fieldTyOf f_j prev_<j` for some j > i. Returns field names in declaration order.";
      signature = "{ fields : [Field]; targetIdx : Prev -> Hoas; fieldTyOf : ?Field -> Prev -> Hoas } -> [String]";
    };
    forcedFieldSet = api.leaf {
      value = forcedFieldSet;
      description = "forcedFieldNames re-keyed as `{ <name> = true; }` for O(1) membership.";
      signature = "{ fields; targetIdx; fieldTyOf? } -> { <name> = true; }";
    };
    isFieldForced = api.leaf {
      value = isFieldForced;
      description = "Predicate form: whether the named field appears in the forced set.";
      signature = "{ fields; targetIdx; fieldTyOf? } -> String -> Bool";
    };
  };

  tests = {
    "forced-mentionsOf-finds-marker-in-app" = {
      expr =
        let
          m = { _signatureField = true; name = "m"; index = 0; };
          term = self.app self.NatDT.succ m;
        in
        mentionsOf term;
      expected = [ "m" ];
    };

    "forced-mentionsOf-finds-marker-in-pair" = {
      expr =
        let
          a = { _signatureField = true; name = "a"; index = 0; };
          b = { _signatureField = true; name = "b"; index = 1; };
          term = self.pair a b;
        in
        mentionsOf term;
      expected = [ "a" "b" ];
    };

    "forced-mentionsOf-finds-marker-under-binder" = {
      expr =
        let
          m = { _signatureField = true; name = "m"; index = 0; };
          term = self.forall "x" self.nat (_: m);
        in
        mentionsOf term;
      expected = [ "m" ];
    };

    "forced-mentionsOf-skips-leaf-types" = {
      expr =
        mentionsOf self.nat
        ++ mentionsOf self.zero
        ++ mentionsOf (self.u 0);
      expected = [ ];
    };

    "forced-mentionsOf-deep-nested-app" = {
      expr =
        let
          n = { _signatureField = true; name = "n"; index = 0; };
          term = self.pair self.zero (self.app self.NatDT.succ n);
        in
        mentionsOf term;
      expected = [ "n" ];
    };

    "forced-Vec-vcons-shape" = {
      # vcons : (A:U)(m:Nat) → A → Vec A m → Vec A (succ m).
      # m appears in targetIdx and in xs's type → forced.
      expr =
        let
          A = { _signatureField = true; name = "A_param"; index = 99; };
          mkData = name: type: { inherit name type; kind = "data"; };
          fields = [
            (mkData "m" self.nat)
            (mkData "x" A)
            { name = "xs"; kind = "recAt"; idxFn = p: p.m; }
          ];
          targetIdx = p: self.app self.NatDT.succ p.m;
          fakeFieldTyOf = f: prev:
            if f.kind == "data" then f.type
            else if f.kind == "recAt" then
              self.app self.NatDT.succ (f.idxFn prev)
            else throw "test fakeFieldTyOf: unsupported";
        in
        forcedFieldNames {
          inherit fields targetIdx;
          fieldTyOf = fakeFieldTyOf;
        };
      expected = [ "m" ];
    };

    "forced-Fin-fzero-shape" = {
      # fzero : (m:Nat) → Fin (succ m). m appears in targetIdx → forced.
      expr =
        let
          fields = [{ name = "m"; kind = "data"; type = self.nat; }];
          targetIdx = p: self.app self.NatDT.succ p.m;
        in
        forcedFieldNames {
          inherit fields targetIdx;
          fieldTyOf = null;
        };
      expected = [ "m" ];
    };

    "forced-cons-shape-fields-not-forced" = {
      # cons : (A:U) → A → List A → List A. Neither head nor tail appears
      # in targetIdx (() at I=⊤) or in any later field's type.
      expr =
        let
          A = { _signatureField = true; name = "A_param"; index = 99; };
          fields = [
            { name = "head"; kind = "data"; type = A; }
            { name = "tail"; kind = "recAt"; idxFn = _: self.ttPrim; }
          ];
          targetIdx = _: self.ttPrim;
          fakeFieldTyOf = f: _:
            if f.kind == "data" then f.type
            else if f.kind == "recAt" then self.unit
            else throw "test fakeFieldTyOf: unsupported";
        in
        forcedFieldNames {
          inherit fields targetIdx;
          fieldTyOf = fakeFieldTyOf;
        };
      expected = [ ];
    };

    "forced-Le-leSS-shape" = {
      # leSS : (m n:Nat) → Le m n → Le (suc m) (suc n).
      # m, n appear in targetIdx and in lemn's type → forced.
      expr =
        let
          mkRec = idxFn: { name = "lemn"; kind = "recAt"; inherit idxFn; };
          fields = [
            { name = "m"; kind = "data"; type = self.nat; }
            { name = "n"; kind = "data"; type = self.nat; }
            (mkRec (p: self.pair p.m p.n))
          ];
          targetIdx = p:
            self.pair (self.app self.NatDT.succ p.m)
              (self.app self.NatDT.succ p.n);
          fakeFieldTyOf = f: prev:
            if f.kind == "data" then f.type
            else if f.kind == "recAt" then f.idxFn prev
            else throw "test fakeFieldTyOf: unsupported";
        in
        forcedFieldNames {
          inherit fields targetIdx;
          fieldTyOf = fakeFieldTyOf;
        };
      expected = [ "m" "n" ];
    };

    "forced-isFieldForced-positive" = {
      expr =
        let
          fields = [{ name = "m"; kind = "data"; type = self.nat; }];
          targetIdx = p: self.app self.NatDT.succ p.m;
          spec = { inherit fields targetIdx; fieldTyOf = null; };
        in
        isFieldForced spec "m";
      expected = true;
    };

    "forced-isFieldForced-negative" = {
      expr =
        let
          fields = [{ name = "h"; kind = "data"; type = self.nat; }];
          targetIdx = _: self.ttPrim;
          spec = { inherit fields targetIdx; fieldTyOf = null; };
        in
        isFieldForced spec "h";
      expected = false;
    };
  };

}
