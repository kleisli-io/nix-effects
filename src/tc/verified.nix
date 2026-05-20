# Convenience combinators for writing verified implementations in HOAS.
#
# Produces valid HOAS term trees that the kernel type-checks.
# Use with v.verify for the full pipeline:
#   write combinators → kernel checks → extract Nix function.
#
# Example: verified successor function
#   v.verify (H.forall "x" H.nat (_: H.nat))
#            (v.fn "x" H.nat (x: H.succ x))
#   → 1-argument Nix function, correct by construction
{ fx, ... }:
let
  H = fx.tc.hoas;
  Elab = fx.tc.elaborate;

  # -- Literal constructors --
  # Produce HOAS value terms from Nix literals.
  nat = H.natLit;
  str = H.stringLit;
  int_ = H.intLit;
  float_ = H.floatLit;
  true_ = H.true_;
  false_ = H.false_;
  null_ = H.tt;

  # -- Binding forms --
  # v.fn "x" domainType (x: body) — lambda abstraction
  fn = H.lam;
  # v.let_ "x" type val (x: body) — let binding
  let__ = H.let_;

  # -- Pair operations --
  # v.pair fst snd annType — construct a pair
  pair = H.pair;
  # v.fst p — first projection
  fst = H.fst_;
  # v.snd p — second projection
  snd = H.snd_;

  # -- Sum operations --
  # v.inl leftTy rightTy term — left injection
  inl = H.inl;
  # v.inr leftTy rightTy term — right injection
  inr = H.inr;

  # -- Application --
  # v.app f arg — function application
  app = H.app;

  # -- Eliminators with inferred constant motives --
  #
  # These construct the required motive automatically from the result type.
  # The motive is always constant (non-dependent): λ_.resultTy.

  # v.if_ resultTy scrut { then_; else_; }
  # Bool elimination with constant motive.
  if_ = resultTy: scrut: { then_, else_ }:
    H.boolElim 0 (H.lam "_" H.bool (_: resultTy)) then_ else_ scrut;

  # v.match resultTy scrut { zero; succ = k: ih: body; }
  # Nat elimination with constant motive.
  # succ callback receives: k (predecessor) and ih (inductive hypothesis).
  match = resultTy: scrut: { zero, succ }:
    H.ind 0 (H.lam "_" H.nat (_: resultTy)) zero
      (H.lam "k" H.nat (k: H.lam "ih" resultTy (ih: succ k ih)))
      scrut;

  # v.matchList elemTy resultTy scrut { nil; cons = h: t: ih: body; }
  # List elimination with constant motive.
  # cons callback receives: h (head), t (tail), ih (inductive hypothesis).
  matchList = elemTy: resultTy: scrut: { nil, cons }:
    H.listElim 0 elemTy (H.lam "_" (H.listOf elemTy) (_: resultTy))
      nil
      (H.lam "h" elemTy (h: H.lam "t" (H.listOf elemTy) (t:
        H.lam "ih" resultTy (ih: cons h t ih))))
      scrut;

  # v.matchSum leftTy rightTy resultTy scrut { left = x: body; right = y: body; }
  # Sum elimination with constant motive.
  matchSum = leftTy: rightTy: resultTy: scrut: { left, right }:
    H.sumElim 0 leftTy rightTy (H.lam "_" (H.sum leftTy rightTy) (_: resultTy))
      (H.lam "l" leftTy (l: left l))
      (H.lam "r" rightTy (r: right r))
      scrut;

  # -- Derived combinators (built on list elimination) --

  # v.map elemTy resultTy f list
  # List map: apply f to each element. f is an HOAS function term.
  # Annotates f with its type so the checker can infer App(f, h).
  map = elemTy: resultTy: f: list:
    let fAnn = H.ann f (H.forall "_" elemTy (_: resultTy)); in
    H.listElim 0 elemTy (H.lam "_" (H.listOf elemTy) (_: H.listOf resultTy))
      (H.nil resultTy)
      (H.lam "h" elemTy (h: H.lam "_" (H.listOf elemTy) (_:
        H.lam "ih" (H.listOf resultTy) (ih:
          H.cons resultTy (H.app fAnn h) ih))))
      list;

  # v.fold elemTy resultTy init f list
  # List fold: combine elements using f. f is an HOAS function term (A → R → R).
  # Annotates f with its type so the checker can infer App(App(f, h), ih).
  fold = elemTy: resultTy: init: f: list:
    let fAnn = H.ann f (H.forall "_" elemTy (_: H.forall "_" resultTy (_: resultTy))); in
    H.listElim 0 elemTy (H.lam "_" (H.listOf elemTy) (_: resultTy))
      init
      (H.lam "h" elemTy (h: H.lam "_" (H.listOf elemTy) (_:
        H.lam "ih" resultTy (ih:
          H.app (H.app fAnn h) ih))))
      list;

  # v.filter elemTy pred list
  # List filter: keep elements where pred returns true.
  # pred is an HOAS function term (A → Bool).
  # Annotates pred with its type so the checker can infer App(pred, h).
  filter = elemTy: pred: list:
    let predAnn = H.ann pred (H.forall "_" elemTy (_: H.bool)); in
    H.listElim 0 elemTy (H.lam "_" (H.listOf elemTy) (_: H.listOf elemTy))
      (H.nil elemTy)
      (H.lam "h" elemTy (h: H.lam "_" (H.listOf elemTy) (_:
        H.lam "ih" (H.listOf elemTy) (ih:
          H.boolElim 0 (H.lam "_" H.bool (_: H.listOf elemTy))
            (H.cons elemTy h ih) ih (H.app predAnn h)))))
      list;

  # -- String comparison --
  # v.strEq a b — kernel string equality (returns Bool HOAS term)
  strEq = H.strEq;

  # v.strElem target list — check if target string is in list of strings.
  # Uses fold with strEq to check membership. Returns Bool.
  strElem = target: list:
    fold H.string H.bool false_
      (fn "s" H.string (s: fn "acc" H.bool (acc:
        if_ H.bool (H.strEq s target) { then_ = true_; else_ = acc; })))
      list;

  # -- Record field access --
  # v.field recordTy fieldName record — project a named field from a
  # mono-constructor record by universal-property eliminator projection.
  #
  # For `R := μ(mk : A₀ → … → Aₙ₋₁ → R)`, the i-th field projector is
  #   πᵢ := λr:R. elim K (λ_:R. Aᵢ) (λa₀ … λaᵢ … λaₙ₋₁. aᵢ) r
  # where `K = level(Aᵢ)` is the motive's codomain universe. The selector
  # method binds n field variables in declaration order and returns the
  # idx-th one. Uniform over arity and field position; the `n == 1` case
  # is handled by ι-reduction (`elim P (λa.a) (mk a) ≡ a`), not a special
  # case in the surface.
  #
  # `recordTy` must carry `_dtypeMeta` with exactly one constructor.
  field = recordTy: fieldName: record:
    let
      meta = fx.tc.generic.datatype.datatypeInfo recordTy;
      cs = meta.constructors;
      nCons = builtins.length cs;
      _conCheck =
        if nCons != 1
        then throw "v.field: expected mono-constructor datatype '${meta.name}', got ${toString nCons}"
        else null;
      con = builtins.head cs;
      fields = con.fields;
      n = builtins.length fields;
      _empty = if n == 0
               then throw "v.field: record '${meta.name}' has no fields"
               else null;

      idxs = builtins.genList (i: i) n;
      matches = builtins.filter
                  (i: (builtins.elemAt fields i).name == fieldName) idxs;
      idx = if matches == []
            then throw "v.field: field '${fieldName}' not found in '${meta.name}'"
            else builtins.head matches;

      selectedField = builtins.elemAt fields idx;
      fieldTy = selectedField.type;
      # Forced to 0 by `H.field` (`datatype.nix:32`); read from fieldMeta
      # so the construction generalises if a higher-level field DSL appears.
      motiveK = if selectedField.level != null then selectedField.level else 0;

      motive = H.lam "_" recordTy (_: fieldTy);
      # Curried selector: λa₀ … λaᵢ … λaₙ₋₁. aᵢ. Uniform over arity; the
      # idx-th binder is returned at the leaf.
      buildSelector = remaining: priorBinders:
        if remaining == []
        then builtins.elemAt priorBinders idx
        else
          let f = builtins.head remaining;
              rest = builtins.tail remaining;
          in H.lam f.name f.type (v: buildSelector rest (priorBinders ++ [v]));
      step = buildSelector fields [];
    in
      builtins.seq _conCheck (builtins.seq _empty
        (H.app
          (H.app
            (H.app (meta.elim motiveK) motive)
            step)
          record));

  # -- Record construction by name --
  # v.makeRecord recordTy { fieldName = hoasValue; ... } — construct a
  # mono-constructor record by applying its kernel constructor to the
  # field values, ordered by declaration. Dual to `v.field`: named
  # projection meets named construction, hiding the μ-encoding from
  # callers (no positional `foldl' H.app DT.mk [...]` at consumer sites).
  #
  # For `R := μ(mk : A₀ → … → Aₙ₋₁ → R)`, this is `mk a₀ … aₙ₋₁` where
  # `aᵢ = argsAttrs.${fieldᵢ.name}`. Field order is read from
  # `meta.constructors[0].fields`; for `H.record` this coincides with
  # alphabetical name order, but the implementation defers to whatever
  # order the description carries.
  #
  # Throws at build time on a multi-constructor datatype, on a missing
  # field, or on an unknown field. The constructor term is
  # `meta.constructors[0].ctor` (the HOAS constructor exposed under
  # `_dtypeMeta.cons[i].ctor` by `_datatypeImpl`).
  makeRecord = recordTy: argsAttrs:
    let
      meta = fx.tc.generic.datatype.datatypeInfo recordTy;
      cs = meta.constructors;
      nCons = builtins.length cs;
      _conCheck =
        if nCons != 1
        then throw "v.makeRecord: expected mono-constructor datatype '${meta.name}', got ${toString nCons}"
        else null;
      con = builtins.head cs;
      fields = con.fields;
      # `map` is shadowed by the local v.map HOAS combinator at the top
      # of this file; reach for the builtin explicitly here and below.
      fieldNames = builtins.map (f: f.name) fields;
      argNames = builtins.attrNames argsAttrs;
      missing = builtins.filter (n: !(argsAttrs ? ${n})) fieldNames;
      extras = builtins.filter (n: !(builtins.elem n fieldNames)) argNames;
      _missingCheck =
        if missing != []
        then throw "v.makeRecord: '${meta.name}' missing fields: ${builtins.concatStringsSep ", " missing}"
        else null;
      _extrasCheck =
        if extras != []
        then throw "v.makeRecord: '${meta.name}' has unknown fields: ${builtins.concatStringsSep ", " extras}"
        else null;
      orderedArgs = builtins.map (n: argsAttrs.${n}) fieldNames;
    in
      builtins.seq _conCheck (builtins.seq _missingCheck (builtins.seq _extrasCheck
        (builtins.foldl' H.app con.ctor orderedArgs)));

  # -- Full pipeline wrapper --
  # v.verify type impl → Nix value (type-checked and extracted)
  verify = Elab.verifyAndExtract;

  # -- Verified callable --
  # v.verifiedFn piType bodyHoas → callable attrset with kernel-verified body.
  # The returned value is callable as a Nix function (via __functor) and
  # carries _hoasImpl so elaborateValue's Pi case uses it for full body
  # verification instead of wrapping in an opaque lambda trust boundary.
  verifiedFn = piHoas: bodyHoas:
    let nixFn = Elab.verifyAndExtract piHoas bodyHoas;
    in builtins.seq nixFn {
      __functor = _self: nixFn;
      _hoasImpl = bodyHoas;
    };

in {
  inherit nat str int_ float_ true_ false_ null_ fn pair fst snd
          field makeRecord inl inr app if_ match matchList matchSum
          map fold filter strEq strElem verify verifiedFn;
  let_ = let__;


  __docs = {
    _self = {
      doc = ''
    # fx.tc.verified — Verified Implementation Combinators

    High-level combinators for writing kernel-checked implementations.
    Write programs with these combinators, then call `v.verify` to
    type-check and extract a Nix function that is correct by construction.

    ## Example

    ```nix
    # Verified successor: Nat → Nat
    v.verify (H.forall "x" H.nat (_: H.nat))
             (v.fn "x" H.nat (x: H.succ x))
    # → Nix function: n → n + 1
    ```

    ## Literals

    - `nat : Int → Hoas` — natural number literal (S^n(zero))
    - `str : String → Hoas` — string literal
    - `int_ : Int → Hoas` — integer literal
    - `float_ : Float → Hoas` — float literal
    - `true_`, `false_` — boolean literals
    - `null_` — unit value (tt)

    ## Binding

    - `fn : String → Hoas → (Hoas → Hoas) → Hoas` — lambda abstraction
    - `let_ : String → Hoas → Hoas → (Hoas → Hoas) → Hoas` — let binding

    ## Data Operations

    - `pair`, `fst`, `snd` — Σ-type construction and projection
    - `field : Hoas → String → Hoas → Hoas` — record field projection by name
    - `inl`, `inr` — Sum injection
    - `app` — function application

    ## Eliminators (Constant Motive)

    These auto-generate the motive `λ_.resultTy`, so you only supply
    the result type and the branches:

    - `if_ : Hoas → Hoas → { then_; else_; } → Hoas` — Bool elimination
    - `match : Hoas → Hoas → { zero; succ : k → ih → Hoas; } → Hoas` — Nat elimination
    - `matchList : Hoas → Hoas → Hoas → { nil; cons : h → t → ih → Hoas; } → Hoas` — List elimination
    - `matchSum : Hoas → Hoas → Hoas → Hoas → { left; right; } → Hoas` — Sum elimination

    ## Derived Combinators

    - `map : Hoas → Hoas → Hoas → Hoas → Hoas` — map f over a list
    - `fold : Hoas → Hoas → Hoas → Hoas → Hoas → Hoas` — fold over a list
    - `filter : Hoas → Hoas → Hoas → Hoas` — filter a list by predicate

    ## Pipeline

    - `verify : Hoas → Hoas → NixValue` — type-check + eval + extract
    - `verifiedFn : Hoas → Hoas → VerifiedValue` — callable value with
      `_hoasImpl` for full kernel body verification in parent types
  '';
      tests = let
    # Type shorthands
    NatT = H.nat;
    BoolT = H.bool;
    StringT = H.string;
    IntT = H.int_;
    FloatT = H.float_;
    UnitT = H.unit;
    SigT = H.sigma "x" NatT (_: BoolT);

    E = fx.tc.eval;
  in {

    # ===== Literal constructors type-check =====

    "v-nat-5" = {
      expr = let t = H.checkHoas NatT (nat 5); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };
    "v-str-hello" = {
      expr = (H.checkHoas StringT (str "hello")).tag;
      expected = "string-lit";
    };
    "v-int-42" = {
      expr = (H.checkHoas IntT (int_ 42)).tag;
      expected = "int-lit";
    };
    "v-float-pi" = {
      expr = (H.checkHoas FloatT (float_ 3.14)).tag;
      expected = "float-lit";
    };
    "v-true" = {
      expr = (H.checkHoas BoolT true_).tag;
      expected = "desc-con";
    };
    "v-false" = {
      expr = (H.checkHoas BoolT false_).tag;
      expected = "desc-con";
    };
    "v-null" = {
      expr = (H.checkHoas UnitT null_).tag;
      expected = "tt";
    };

    # ===== Binding forms =====

    # Identity: λ(x:Nat).x : Nat → Nat
    "v-fn-identity" = {
      expr = (H.checkHoas (H.forall "x" NatT (_: NatT)) (fn "x" NatT (x: x))).tag;
      expected = "lam";
    };

    # Let binding: let x = 5 in x : Nat
    "v-let-bind" = {
      expr = (H.checkHoas NatT (let__ "x" NatT (nat 5) (x: x))).tag;
      expected = "let";
    };

    # ===== Pair operations =====

    # Pair: (0, true) : Σ(x:Nat).Bool
    "v-pair-check" = {
      expr = (H.checkHoas SigT (pair (nat 0) true_)).tag;
      expected = "pair";
    };

    # Fst: fst((0, true)) evaluates to 0
    "v-fst-eval" = {
      expr = let
        p = pair (nat 0) true_;
        val = E.eval [] (H.elab (fst p));
      in Elab.extract NatT val;
      expected = 0;
    };

    # Snd: snd((0, true)) evaluates to true
    "v-snd-eval" = {
      expr = let
        p = pair (nat 0) true_;
        val = E.eval [] (H.elab (snd p));
      in Elab.extract BoolT val;
      expected = true;
    };

    # ===== if_ eliminator =====

    # if true then 1 else 0 → 1
    "v-if-true" = {
      expr = verify NatT (if_ NatT true_ { then_ = nat 1; else_ = nat 0; });
      expected = 1;
    };

    # if false then 1 else 0 → 0
    "v-if-false" = {
      expr = verify NatT (if_ NatT false_ { then_ = nat 1; else_ = nat 0; });
      expected = 0;
    };

    # ===== match (nat) eliminator =====

    # match 0 { zero = 42; succ = ... } → 42
    "v-match-zero" = {
      expr = verify NatT (match NatT (nat 0) {
        zero = nat 42;
        succ = _k: _ih: nat 0;
      });
      expected = 42;
    };

    # match 3 { zero = 0; succ = k: ih: S(ih) } → 3
    # (identity via induction: natElim(λ_.Nat, 0, λk.λih.S(ih), 3) = 3)
    "v-match-succ" = {
      expr = verify NatT (match NatT (nat 3) {
        zero = nat 0;
        succ = _k: ih: H.succ ih;
      });
      expected = 3;
    };

    # ===== matchList eliminator =====

    # matchList [] { nil = 0; cons = ... } → 0
    "v-matchList-nil" = {
      expr = verify NatT (matchList NatT NatT (H.nil NatT) {
        nil = nat 0;
        cons = _h: _t: _ih: nat 99;
      });
      expected = 0;
    };

    # matchList [1,2,3] — count elements via fold
    "v-matchList-count" = {
      expr = verify NatT (matchList NatT NatT
        (H.cons NatT (nat 1) (H.cons NatT (nat 2) (H.cons NatT (nat 3) (H.nil NatT))))
        {
          nil = nat 0;
          cons = _h: _t: ih: H.succ ih;
        });
      expected = 3;
    };

    # ===== matchSum eliminator =====

    # matchSum (inl 5) { left = x → S(x); right = _ → 0 }
    "v-matchSum-left" = {
      expr = verify NatT (matchSum NatT BoolT NatT (inl NatT BoolT (nat 5)) {
        left = x: H.succ x;
        right = _: nat 0;
      });
      expected = 6;
    };

    # matchSum (inr true) { left = x → x; right = _ → 99 }
    "v-matchSum-right" = {
      expr = verify NatT (matchSum NatT BoolT NatT (inr NatT BoolT true_) {
        left = x: x;
        right = _: nat 99;
      });
      expected = 99;
    };

    # ===== map =====

    # map succ [0, 1, 2] → [1, 2, 3]
    "v-map-succ" = {
      expr = let
        succFn = fn "x" NatT (x: H.succ x);
        input = H.cons NatT (nat 0) (H.cons NatT (nat 1) (H.cons NatT (nat 2) (H.nil NatT)));
        result = map NatT NatT succFn input;
      in verify (H.listOf NatT) result;
      expected = [1 2 3];
    };

    # map over empty list → []
    "v-map-empty" = {
      expr = let
        succFn = fn "x" NatT (x: H.succ x);
      in verify (H.listOf NatT) (map NatT NatT succFn (H.nil NatT));
      expected = [];
    };

    # ===== fold =====

    # fold 0 add [1,1,1] → 3 (counting via nat addition)
    "v-fold-sum" = {
      expr = let
        # addFn : Nat → Nat → Nat
        # addFn = λa. λb. natElim(λ_.Nat, b, λk.λih.S(ih), a)
        addFn = fn "a" NatT (a: fn "b" NatT (b:
          match NatT a { zero = b; succ = _k: ih: H.succ ih; }));
        input = H.cons NatT (nat 1) (H.cons NatT (nat 1) (H.cons NatT (nat 1) (H.nil NatT)));
      in verify NatT (fold NatT NatT (nat 0) addFn input);
      expected = 3;
    };

    # ===== filter =====

    # filter isZero [0, 1, 0, 2] → [0, 0]
    "v-filter-zeros" = {
      expr = let
        # isZero : Nat → Bool — returns true for zero, false for succ
        isZero = fn "n" NatT (n:
          match BoolT n { zero = true_; succ = _k: _ih: false_; });
        input = H.cons NatT (nat 0) (H.cons NatT (nat 1)
          (H.cons NatT (nat 0) (H.cons NatT (nat 2) (H.nil NatT))));
      in verify (H.listOf NatT) (filter NatT isZero input);
      expected = [0 0];
    };

    # ===== Integration: verified add function =====

    # add : Nat → Nat → Nat (verified and extracted)
    "v-verify-add" = {
      expr = let
        addTy = H.forall "m" NatT (_: H.forall "n" NatT (_: NatT));
        addImpl = fn "m" NatT (m: fn "n" NatT (n:
          match NatT m {
            zero = n;
            succ = _k: ih: H.succ ih;
          }));
        add = verify addTy addImpl;
      in add 2 3;
      expected = 5;
    };

    # ===== Integration: verified identity (extract and call) =====

    "v-verify-identity" = {
      expr = let
        idTy = H.forall "x" NatT (_: NatT);
        idImpl = fn "x" NatT (x: x);
        id = verify idTy idImpl;
      in id 10;
      expected = 10;
    };

    # ===== Integration: verified constant function =====

    "v-verify-const" = {
      expr = let
        constTy = H.forall "_" BoolT (_: NatT);
        constImpl = fn "_" BoolT (_: nat 42);
        constFn = verify constTy constImpl;
      in constFn true;
      expected = 42;
    };

    # ===== Record-domain verified functions =====

    # v.field: project first field from 2-field record
    "v-record-get-fst" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        getFst = verify (H.forall "r" recTy (_: NatT))
          (fn "r" recTy (r: field recTy "x" r));
      in getFst { x = 3; y = true; };
      expected = 3;
    };

    # v.field: project second field from 2-field record
    "v-record-get-snd" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        getSnd = verify (H.forall "r" recTy (_: BoolT))
          (fn "r" recTy (r: field recTy "y" r));
      in getSnd { x = 3; y = true; };
      expected = true;
    };

    # v.field: 3-field record, access middle field
    "v-record-3field-middle" = {
      expr = let
        recTy = H.record [
          { name = "a"; type = NatT; }
          { name = "b"; type = StringT; }
          { name = "c"; type = BoolT; }
        ];
        getB = verify (H.forall "r" recTy (_: StringT))
          (fn "r" recTy (r: field recTy "b" r));
      in getB { a = 7; b = "hello"; c = false; };
      expected = "hello";
    };

    # v.field: 3-field record, access last field
    "v-record-3field-last" = {
      expr = let
        recTy = H.record [
          { name = "a"; type = NatT; }
          { name = "b"; type = StringT; }
          { name = "c"; type = BoolT; }
        ];
        getC = verify (H.forall "r" recTy (_: BoolT))
          (fn "r" recTy (r: field recTy "c" r));
      in getC { a = 7; b = "hello"; c = true; };
      expected = true;
    };

    # Record-domain function with computation: project field and add 1
    "v-record-compute" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        succX = verify (H.forall "r" recTy (_: NatT))
          (fn "r" recTy (r: H.succ (field recTy "x" r)));
      in succX { x = 10; y = false; };
      expected = 11;
    };

    # 1-field record: v.field returns the record itself
    "v-record-1field" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } ];
        getX = verify (H.forall "r" recTy (_: NatT))
          (fn "r" recTy (r: field recTy "x" r));
      in getX { x = 42; };
      expected = 42;
    };

    # ===== v.makeRecord: named record construction =====

    # 2-field construction: build {x; y} and extract.
    "v-makeRecord-2field-construct" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        builder = verify (H.forall "_" UnitT (_: recTy))
          (fn "_" UnitT (_: makeRecord recTy { x = nat 7; y = true_; }));
        r = builder null;
      in { x = r.x; y = r.y; };
      expected = { x = 7; y = true; };
    };

    # 3 fields: attrset is name-keyed, so declaration order in `H.record`
    # versus call-site order in the attrset don't need to match.
    "v-makeRecord-3field-construct" = {
      expr = let
        recTy = H.record [
          { name = "a"; type = NatT; }
          { name = "b"; type = StringT; }
          { name = "c"; type = BoolT; }
        ];
        builder = verify (H.forall "_" UnitT (_: recTy))
          (fn "_" UnitT (_: makeRecord recTy {
            c = false_; a = nat 5; b = str "ok";
          }));
        r = builder null;
      in { a = r.a; b = r.b; c = r.c; };
      expected = { a = 5; b = "ok"; c = false; };
    };

    # Roundtrip: construct then project each field returns the input value.
    "v-makeRecord-roundtrip" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        round = verify (H.forall "_" UnitT (_: recTy))
          (fn "_" UnitT (_: makeRecord recTy { x = nat 9; y = true_; }));
        getX = verify (H.forall "r" recTy (_: NatT))
          (fn "r" recTy (r: field recTy "x" r));
        getY = verify (H.forall "r" recTy (_: BoolT))
          (fn "r" recTy (r: field recTy "y" r));
        r = round null;
      in { x = getX r; y = getY r; };
      expected = { x = 9; y = true; };
    };

    # Missing field throws at build time.
    "v-makeRecord-missing-fields-throws" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        attempt = builtins.tryEval (makeRecord recTy { x = nat 1; });
      in attempt.success;
      expected = false;
    };

    # Extra field throws at build time.
    "v-makeRecord-extra-fields-throws" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } { name = "y"; type = BoolT; } ];
        attempt = builtins.tryEval
          (makeRecord recTy { x = nat 1; y = true_; z = null_; });
      in attempt.success;
      expected = false;
    };

    # Multi-constructor datatype (Variant) is rejected: makeRecord is for
    # mono-constructor records only. Caller would use a tag-aware builder.
    "v-makeRecord-non-record-throws" = {
      expr = let
        varTy = H.variant [
          { tag = "Left"; type = NatT; }
          { tag = "Right"; type = BoolT; }
        ];
        attempt = builtins.tryEval (makeRecord varTy { Left = nat 1; });
      in attempt.success;
      expected = false;
    };

    # 1-field record: builder produces the wrapped value, projector
    # recovers it.
    "v-makeRecord-1field" = {
      expr = let
        recTy = H.record [ { name = "x"; type = NatT; } ];
        round = verify (H.forall "_" UnitT (_: recTy))
          (fn "_" UnitT (_: makeRecord recTy { x = nat 42; }));
        getX = verify (H.forall "r" recTy (_: NatT))
          (fn "r" recTy (r: field recTy "x" r));
      in getX (round null);
      expected = 42;
    };

    # ===== verifiedFn: callable with _hoasImpl protocol =====

    "verified-fn-is-callable" = {
      expr = let
        f = verifiedFn (H.forall "x" NatT (_: NatT)) (fn "x" NatT (x: H.succ x));
      in f 5;
      expected = 6;
    };
    "verified-fn-has-hoasImpl" = {
      expr = let
        f = verifiedFn (H.forall "x" NatT (_: NatT)) (fn "x" NatT (x: H.succ x));
      in f ? _hoasImpl;
      expected = true;
    };
    "verified-fn-kernel-checks" = {
      # elaborateValue Pi uses _hoasImpl for full body verification
      expr = let
        piTy = H.forall "x" NatT (_: NatT);
        f = verifiedFn piTy (fn "x" NatT (x: H.succ x));
      in Elab.decide piTy f;
      expected = true;
    };
    "verified-fn-body-rejects" = {
      # Kernel catches body type error at construction time
      expr = let
        piTy = H.forall "x" NatT (_: NatT);
        # Body returns Bool instead of Nat
        result = builtins.tryEval (verifiedFn piTy (fn "x" NatT (_: true_)));
      in result.success;
      expected = false;
    };
    "verified-fn-roundtrip" = {
      # elaborate → check → eval → extract = same function behavior
      expr = let
        piTy = H.forall "x" NatT (_: NatT);
        f = verifiedFn piTy (fn "x" NatT (x: H.succ x));
        hoasVal = Elab.elaborateValue piTy f;
        val = fx.tc.eval.eval [] (H.elab hoasVal);
        extracted = Elab.extract piTy val;
      in extracted 5;
      expected = 6;
    };
    "verified-vs-opaque-same-domain-check" = {
      # Both verified and opaque reject domain mismatch
      expr = let
        natToNat = H.forall "x" NatT (_: NatT);
        boolToNat = H.forall "x" BoolT (_: NatT);
        f = verifiedFn natToNat (fn "x" NatT (x: H.succ x));
      in Elab.decide boolToNat f;
      expected = false;
    };
  };
    };

    nat = {
      description = "nat: HOAS literal — wrap a Nix `Int` as a `succ^n zero` natural-number HOAS term checkable against `H.nat`.";
      signature = "nat : Int -> Hoas";
    };
    str = {
      description = "str: HOAS literal — lift a Nix `String` to a `stringLit` HOAS term checkable against `H.string`.";
      signature = "str : String -> Hoas";
    };
    int_ = {
      description = "int_: HOAS literal — lift a Nix integer to an `intLit` HOAS term checkable against `H.int_` (the kernel `Int` axiom, distinct from `nat`).";
      signature = "int_ : Int -> Hoas";
    };
    float_ = {
      description = "float_: HOAS literal — lift a Nix float to a `floatLit` HOAS term checkable against `H.float_`.";
      signature = "float_ : Float -> Hoas";
    };
    true_ = {
      description = "true_: HOAS literal — the `True` constructor of `H.bool` as `inr tt`; reflects the bool-as-sum levitation discipline.";
      signature = "true_ : Hoas";
    };
    false_ = {
      description = "false_: HOAS literal — the `False` constructor of `H.bool` as `inl tt`; reflects the bool-as-sum levitation discipline.";
      signature = "false_ : Hoas";
    };
    null_ = {
      description = "null_: HOAS literal — the unique inhabitant `tt` of `H.unit`; the conventional empty / placeholder value in verified code.";
      signature = "null_ : Hoas";
    };
    fn = {
      description = "fn: HOAS lambda — `fn name domTy body` builds `λ(name:domTy). body`, with `body` a Nix function receiving the bound variable as a HOAS term.";
      signature = "fn : String -> Hoas -> (Hoas -> Hoas) -> Hoas";
    };
    let_ = {
      description = "let_: HOAS let binding — `let_ name ty val body` builds `let name : ty = val in body`; `body` is a Nix function receiving the bound variable.";
      signature = "let_ : String -> Hoas -> Hoas -> (Hoas -> Hoas) -> Hoas";
    };
    pair = {
      description = "pair: HOAS Σ-pair constructor — `pair fst snd` packages two HOAS values; the surrounding annotation fixes which Σ-type the pair inhabits.";
      signature = "pair : Hoas -> Hoas -> Hoas";
    };
    fst = {
      description = "fst: first projection on a HOAS Σ-pair; reduces by π₁ during normalisation.";
      signature = "fst : Hoas -> Hoas";
    };
    snd = {
      description = "snd: second projection on a HOAS Σ-pair; reduces by π₂ during normalisation.";
      signature = "snd : Hoas -> Hoas";
    };
    field = {
      description = "field: HOAS record field-projection by name — derives the universal-property eliminator for a mono-constructor datatype and applies it to extract the named field.";
      signature = "field : Hoas -> String -> Hoas -> Hoas";
      doc = ''
        Requires `recordTy` to carry `_dtypeMeta` with exactly one
        constructor (records are mono-constructor datatypes via
        `H.record`). Throws at build time if the type is
        multi-constructor, has no fields, or the requested field name
        is absent. The 1-field special case reduces via ι
        (`elim P (λa.a) (mk a) ≡ a`); no surface branching is needed.
        Field positions are read from `meta.constructors[0].fields` in
        declaration order, so renaming a field in source is a
        breaking change.
      '';
    };
    makeRecord = {
      description = "makeRecord: HOAS record construction by name — applies the mono-constructor of a μ-encoded record type to the field values in declaration order, dual to `field`'s named projection.";
      signature = "makeRecord : Hoas -> { <field> = Hoas; ... } -> Hoas";
      doc = ''
        Dual to `field`. Given a record type built by `H.record` (or
        any mono-constructor datatype carrying `_dtypeMeta`) and an
        attrset keyed by field name, produces the HOAS term
        `mk a₀ … aₙ₋₁` where each `aᵢ` is read from `argsAttrs`
        by field name, and
        field order follows `meta.constructors[0].fields` (for
        `H.record`, alphabetical by name).

        Throws at build time on a multi-constructor datatype, a
        missing required field, or an unknown extra field. The
        constructor term used is `meta.constructors[0].ctor`, exposed
        on the kernel datatype attrset by `_datatypeImpl`.

        Use this in verified implementations that return records, so
        consumer code never needs to reach for `builtins.foldl' H.app
        DT.mk [...]` or know the μ-encoding.
      '';
    };
    inl = {
      description = "inl: HOAS sum left-injection — `inl leftTy rightTy term` builds an `A + B` term carrying `term : A` in the left branch.";
      signature = "inl : Hoas -> Hoas -> Hoas -> Hoas";
    };
    inr = {
      description = "inr: HOAS sum right-injection — `inr leftTy rightTy term` builds an `A + B` term carrying `term : B` in the right branch.";
      signature = "inr : Hoas -> Hoas -> Hoas -> Hoas";
    };
    app = {
      description = "app: HOAS function application — `app f arg` builds the redex; β-reduces during normalisation when `f` is a lambda.";
      signature = "app : Hoas -> Hoas -> Hoas";
    };
    if_ = {
      description = "if_: bool-elimination wrapper — supplies a constant motive `λ_.resultTy` so callers write only the result type and the two branches.";
      signature = "if_ : Hoas -> Hoas -> { then_ : Hoas; else_ : Hoas; } -> Hoas";
      doc = ''
        Use when the branch result type does not depend on the
        scrutinee. For a dependent motive (different result type per
        branch), drop to `H.boolElim` directly. The synthesised motive
        is `λ_:bool.resultTy`; `boolElim`'s level argument is fixed at
        0 here, so cross-universe branching also needs `H.boolElim`.
      '';
    };
    match = {
      description = "match: nat-elimination wrapper — supplies a constant motive `λ_.resultTy`; the `succ` callback receives both predecessor `k` and inductive hypothesis `ih`.";
      signature = "match : Hoas -> Hoas -> { zero : Hoas; succ : Hoas -> Hoas -> Hoas; } -> Hoas";
      doc = ''
        The succ callback receives two HOAS values: `k` (the
        predecessor binder, of type `nat`) and `ih` (the inductive
        hypothesis, of type `resultTy`). Use when result type is
        non-dependent on the scrutinee; drop to `H.ind` for dependent
        motives. Level is fixed at 0 by the synthesised motive.
      '';
    };
    matchList = {
      description = "matchList: list-elimination wrapper — constant motive `λ_.resultTy`; the `cons` callback binds head, tail, and inductive hypothesis.";
      signature = "matchList : Hoas -> Hoas -> Hoas -> { nil : Hoas; cons : Hoas -> Hoas -> Hoas -> Hoas; } -> Hoas";
      doc = ''
        The cons callback receives three HOAS values: `h` (the head
        element of type `elemTy`), `t` (the tail list of type
        `listOf elemTy`), and `ih` (the inductive hypothesis of type
        `resultTy`). For dependent motives, drop to `H.listElim`.
        Level fixed at 0.
      '';
    };
    matchSum = {
      description = "matchSum: sum-elimination wrapper — constant motive `λ_.resultTy`; the left and right callbacks receive their respective payloads.";
      signature = "matchSum : Hoas -> Hoas -> Hoas -> Hoas -> { left : Hoas -> Hoas; right : Hoas -> Hoas; } -> Hoas";
      doc = ''
        Each callback receives one HOAS value: the left payload for
        `left`, the right payload for `right`. Use when the result
        type doesn't depend on which case fires; drop to `H.sumElim`
        for dependent motives. Level fixed at 0.
      '';
    };
    map = {
      description = "map: HOAS list-map combinator built on `listElim` — applies `f : elemTy -> resultTy` to every element, threading the inductive hypothesis to accumulate the output list.";
      signature = "map : Hoas -> Hoas -> Hoas -> Hoas -> Hoas";
      doc = ''
        Annotates `f` with `H.forall "_" elemTy (_: resultTy)` so the
        kernel can infer the application type. `f` must be a HOAS
        function term (build one with `fn`), not a Nix function. For
        element transformations that aren't expressible as a uniform
        HOAS function (e.g. type-dependent on element shape), drop to
        `H.listElim` directly.
      '';
    };
    fold = {
      description = "fold: HOAS list-fold combinator — combines elements right-to-left using `f : elemTy -> resultTy -> resultTy` starting from `init`.";
      signature = "fold : Hoas -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas";
      doc = ''
        Annotates `f` with `H.forall "_" elemTy (_: H.forall "_" resultTy (_: resultTy))`
        so the applications `f h ih` infer correctly. `f` must be a
        HOAS function term built with `fn` (or nested `fn` for the
        curried two-argument case). The accumulator threads through
        `ih`; the empty-list case returns `init`.
      '';
    };
    filter = {
      description = "filter: HOAS list-filter combinator — keeps elements where `pred : elemTy -> Bool` returns `true_`; built on `listElim` plus per-element `boolElim`.";
      signature = "filter : Hoas -> Hoas -> Hoas -> Hoas";
      doc = ''
        Annotates `pred` with `H.forall "_" elemTy (_: H.bool)` so
        the application infers. `pred` must be a HOAS function term
        producing a `bool` HOAS value (e.g. via `if_`, `match`, or a
        direct `true_`/`false_`). Element order is preserved; the
        accumulator threads via the inductive hypothesis.
      '';
    };
    strEq = {
      description = "strEq: kernel string equality returning a `Bool` HOAS term; reflects the `mkStrEq` primitive of the kernel.";
      signature = "strEq : Hoas -> Hoas -> Hoas";
    };
    strElem = {
      description = "strElem: HOAS membership check on a `List String` — folds `strEq target` across the list, accumulating `true_` if any element matches.";
      signature = "strElem : Hoas -> Hoas -> Hoas";
      doc = ''
        Built on `fold` plus `strEq`: each list element is compared
        to `target`; the accumulator starts at `false_` and stays
        `true_` once a match is seen. Use when verified code needs a
        membership predicate over strings; for raw kernel-level
        equality on a single pair, use `strEq`.
      '';
    };
    verify = {
      description = "verify: full pipeline — kernel-check a HOAS implementation against a HOAS type, then evaluate and extract a Nix value witnessing the body.";
      signature = "verify : Hoas -> Hoas -> NixValue";
      doc = ''
        Calls `fx.tc.elaborate.verifyAndExtract` internally. Returns
        the Nix value (typically a function or data structure) that
        the type-checked HOAS body denotes; consume via normal Nix
        call or attribute access. Use as the final step of a
        verified-implementation pipeline. For a callable wrapper that
        retains the HOAS implementation so parent-type elaboration can
        re-check the body, use `verifiedFn` instead.
      '';
    };
    verifiedFn = {
      description = "verifiedFn: extract a kernel-verified callable carrying `_hoasImpl` — `elaborateValue`'s Pi case uses the HOAS body for full re-verification instead of falling back to an opaque trust boundary.";
      signature = "verifiedFn : Hoas -> Hoas -> { __functor; _hoasImpl }";
      doc = ''
        Returns an attrset callable via `__functor` (so
        `(verifiedFn piTy body) arg` works) and carrying
        `_hoasImpl = body` so parent elaboration can re-check the body
        against a more general type instead of treating it as an
        opaque lambda. Use when the verified function will be
        embedded inside another verified type-check (e.g. as a field
        of a verified record); for standalone use, `verify` is
        simpler.
      '';
    };

  };
}
