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
{ fx, api, ... }:

let
  inherit (api) mk;
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
    H.boolElim (H.lam "_" H.bool (_: resultTy)) then_ else_ scrut;

  # v.match resultTy scrut { zero; succ = k: ih: body; }
  # Nat elimination with constant motive.
  # succ callback receives: k (predecessor) and ih (inductive hypothesis).
  match = resultTy: scrut: { zero, succ }:
    H.ind (H.lam "_" H.nat (_: resultTy)) zero
      (H.lam "k" H.nat (k: H.lam "ih" resultTy (ih: succ k ih)))
      scrut;

  # v.matchList elemTy resultTy scrut { nil; cons = h: t: ih: body; }
  # List elimination with constant motive.
  # cons callback receives: h (head), t (tail), ih (inductive hypothesis).
  matchList = elemTy: resultTy: scrut: { nil, cons }:
    H.listElim elemTy (H.lam "_" (H.listOf elemTy) (_: resultTy))
      nil
      (H.lam "h" elemTy (h: H.lam "t" (H.listOf elemTy) (t:
        H.lam "ih" resultTy (ih: cons h t ih))))
      scrut;

  # v.matchSum leftTy rightTy resultTy scrut { left = x: body; right = y: body; }
  # Sum elimination with constant motive.
  matchSum = leftTy: rightTy: resultTy: scrut: { left, right }:
    H.sumElim leftTy rightTy (H.lam "_" (H.sum leftTy rightTy) (_: resultTy))
      (H.lam "l" leftTy (l: left l))
      (H.lam "r" rightTy (r: right r))
      scrut;

  # -- Derived combinators (built on list elimination) --

  # v.map elemTy resultTy f list
  # List map: apply f to each element. f is an HOAS function term.
  # Annotates f with its type so the checker can infer App(f, h).
  map = elemTy: resultTy: f: list:
    let fAnn = H.ann f (H.forall "_" elemTy (_: resultTy)); in
    H.listElim elemTy (H.lam "_" (H.listOf elemTy) (_: H.listOf resultTy))
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
    H.listElim elemTy (H.lam "_" (H.listOf elemTy) (_: resultTy))
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
    H.listElim elemTy (H.lam "_" (H.listOf elemTy) (_: H.listOf elemTy))
      (H.nil elemTy)
      (H.lam "h" elemTy (h: H.lam "_" (H.listOf elemTy) (_:
        H.lam "ih" (H.listOf elemTy) (ih:
          H.boolElim (H.lam "_" H.bool (_: H.listOf elemTy))
            (H.cons elemTy h ih) ih (H.app predAnn h)))))
      list;

  # -- Full pipeline wrapper --
  # v.verify type impl → Nix value (type-checked and extracted)
  verify = Elab.verifyAndExtract;

in mk {
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
  '';
  value = {
    # Literals
    inherit nat str int_ float_ true_ false_ null_;
    # Binding
    inherit fn;
    let_ = let__;
    # Pairs
    inherit pair fst snd;
    # Sums
    inherit inl inr;
    # Application
    inherit app;
    # Eliminators
    inherit if_ match matchList matchSum;
    # Derived
    inherit map fold filter;
    # Pipeline
    inherit verify;
  };
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
      expr = (H.checkHoas NatT (nat 5)).tag;
      expected = "succ";
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
      expected = "true";
    };
    "v-false" = {
      expr = (H.checkHoas BoolT false_).tag;
      expected = "false";
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
      expr = (H.checkHoas SigT (pair (nat 0) true_ SigT)).tag;
      expected = "pair";
    };

    # Fst: fst((0, true)) evaluates to 0
    "v-fst-eval" = {
      expr = let
        p = pair (nat 0) true_ SigT;
        val = E.eval [] (H.elab (fst p));
      in Elab.extract NatT val;
      expected = 0;
    };

    # Snd: snd((0, true)) evaluates to true
    "v-snd-eval" = {
      expr = let
        p = pair (nat 0) true_ SigT;
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
  };
}
