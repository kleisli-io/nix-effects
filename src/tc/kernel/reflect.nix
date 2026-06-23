# Reflection of a Nix-side carrier type into its kernel KType code, plus the
# checkable predicate vocabulary used to build refinement arms.
#
#   reflect A         := iota A                : KType   (base carrier, empty stack)
#   reflectRefine A p := refine (reflect A) p  : KType   (extend with one predicate)
#
# A code's predicate stack is List (A -> Bool), so a refinement predicate is a
# Boolean decision over the carrier. The Int predicates decide via the kernel's
# host-backed intLe/intEq primitives on the opaque int_ carrier (O(1), no unary
# tower); the String predicate decides membership via strEq. A Bool-valued term
# IS the predicate — the on-stack form the decider conjoins. The propositional
# decidability vocabulary (dec/le/sum) is deliberately not used here: its codes
# carry proof-or-refutation structure that a refinement immediately projects back
# to Bool, the wrong altitude for a Boolean predicate stack.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  app = H.app;

  inherit (self.ktype) KType beta decide iota refine andB;

  bool = H.bool;
  true_ = H.true_;
  false_ = H.false_;

  int_ = H.int_;
  intLit = H.intLit;

  string = H.string;
  stringLit = H.stringLit;
  strEq = H.strEq;

  # Nix value -> kernel term, for bridging compound values under their carrier.
  elaborateValue = fx.tc.elaborate.elaborateValue;

  # Eval / convertibility / checks-against — the reductions a derived guard rides on.
  ev = h: fx.tc.eval.eval [ ] (H.elab h);
  conv = a: b: fx.tc.conv.conv 0 (ev a) (ev b);
  chk = ty: h: !((H.checkHoas ty h) ? error);

  # The predicate type over a carrier: a Boolean decision on its inhabitants.
  predTy = A: H.forall "_" A (_: bool);

  # Named predicates over the int_ primitive carrier, each int_ -> Bool, decided
  # by the host-backed intLe/intEq primitives (O(1), parallel to strEq). lo/hi/k
  # are Nix integers entering via the O(1) intLit bridge.
  positiveInt = H.lam "x" int_ (x: H.intLe (intLit 1) x);            # 1 <= x
  nonNegativeInt = H.lam "x" int_ (x: H.intLe (intLit 0) x);         # 0 <= x
  inRangeInt = lo: hi: H.lam "x" int_ (x:                            # lo <= x <= hi
    andB (H.intLe (intLit lo) x) (H.intLe x (intLit hi)));
  eqInt = k: H.lam "x" int_ (x: H.intEq x (intLit k));               # x == k

  # String literal-set membership (String -> Bool) via the kernel's sole string
  # op strEq; disjunction is a boolElim cascade (no kernel `or`). No
  # length/substring/match — opaque-string boundary holds.
  orB = a: b: H.boolElim 0 (H.lam "_" bool (_: bool)) true_ b a;
  oneOfStrTerm = lits: H.lam "x" string (x:
    builtins.foldl' (acc: lit: orB (strEq x (stringLit lit)) acc) false_ lits);

  # Reflection of a carrier into its base code and the refinement extension.
  reflect = A: iota A;
  reflectRefine = A: p: refine (reflect A) p;

  # KernelPred witness: predicate stack + carrier + Nix->carrier bridge. The
  # decision is authoritative, so only registered provenance tags are trusted;
  # an untagged or foreign witness fails closed everywhere.
  vocabRegistry = { intPositive = true; intNonNegative = true; intInRange = true; intEq = true; strOneOf = true; compoundStructural = true; };

  isKernelPred = g: builtins.isAttrs g && (g._tag or null) == "KernelPred";

  # Non-empty provenance, every tag registered.
  sealed = g:
    isKernelPred g
    && (g ? provenance)
    && builtins.isList g.provenance
    && g.provenance != [ ]
    && builtins.all (n: builtins.hasAttr n vocabRegistry) g.provenance;

  mkKernelPred = { name, predTerm, carrier, bridge }:
    assert builtins.hasAttr name vocabRegistry;
    { _tag = "KernelPred"; provenance = [ name ]; predTerms = [ predTerm ]; inherit carrier bridge; };

  # Concatenate stacks and provenance; keeps the left carrier/bridge.
  andKP = a: b: a // {
    predTerms = a.predTerms ++ b.predTerms;
    provenance = (a.provenance or [ ]) ++ (b.provenance or [ ]);
  };

  # The KType a witness denotes: fold the stack onto the reflected carrier.
  ktypeOf = g: builtins.foldl' (acc: p: refine acc p) (reflect g.carrier) g.predTerms;

  # Fail-closed: sealed, and every predicate checks at carrier -> Bool.
  kernelExpressible = g:
    sealed g
    && (g ? predTerms) && (g ? carrier)
    && (let r = builtins.tryEval
          (builtins.all (p: chk (predTy g.carrier) p) g.predTerms);
        in r.success && r.value);

  # Derived guard: kernel decision at the bridged value. Unsealed -> reject all;
  # sealed -> over-reject only (a stuck decision never spuriously accepts).
  deriveGuard = g:
    if !(sealed g) then (_: false)
    else
      let d = decide (ktypeOf g); in
      v:
        let r = builtins.tryEval (conv (app d (g.bridge v)) true_);
        in r.success && r.value;

  # Int witnesses over int_, bridging via the O(1) intLit; lo/hi/k are Nix integers.
  intPositive = mkKernelPred { name = "intPositive"; predTerm = positiveInt; carrier = int_; bridge = intLit; };
  intNonNegative = mkKernelPred { name = "intNonNegative"; predTerm = nonNegativeInt; carrier = int_; bridge = intLit; };
  intInRange = lo: hi: mkKernelPred {
    name = "intInRange"; predTerm = inRangeInt lo hi; carrier = int_; bridge = intLit;
  };
  intEq = k: mkKernelPred { name = "intEq"; predTerm = eqInt k; carrier = int_; bridge = intLit; };

  # String witness, bridged by stringLit; decides membership in a fixed literal
  # set. Singleton list = equality-against-literal.
  strOneOf = lits: mkKernelPred { name = "strOneOf"; predTerm = oneOfStrTerm lits; carrier = string; bridge = stringLit; };

  # Compound structural witness: the membership predicate of a refined compound,
  # as a `descCataBool` fold over its carrier description `D` that conjoins each
  # child's kernel decision. `childKts` are the child KTypes in `descArg` walk
  # order (record fields sorted; a single uniform element for a list). Any null
  # child KType (a child the kernel cannot decide) makes the compound
  # non-internalizable — returns null so the caller keeps its host guard.
  mkCompoundPred = { carrier, D, childKts }:
    if builtins.any (k: k == null) childKts then null
    else
      let onArg = ix: _node: s: app (decide (builtins.elemAt childKts ix)) s; in
      mkKernelPred {
        name = "compoundStructural";
        predTerm = H.descCataBool { inherit D carrier onArg; };
        inherit carrier;
        bridge = elaborateValue carrier;
      };

  # Sum-carrier structural witnesses. The native `variant`/`maybe` carriers are
  # right-nested binary sums — `variant`: `Sum b0 (Sum b1 (… b_{n-1}))` with the
  # last branch bare; `maybe`: `Sum inner Unit` — NOT μ-datatypes, so a mono
  # description's carrier conv-equals the native one only at two branches. The
  # membership predicate therefore folds the native sum directly with `sumElim`,
  # each branch deciding its own child. The recursion is INLINED into one nested
  # `sumElim` term: a bare lambda in application position has no synthesis rule.
  sumOfTypes = tys:
    if builtins.length tys == 1 then builtins.head tys
    else H.sum (builtins.head tys) (sumOfTypes (builtins.tail tys));

  # `branches : [{ type; kt }]` in carrier (tag-sorted) order.
  variantBody = branches: scrut:
    if builtins.length branches == 1 then
      app (decide (builtins.head branches).kt) scrut
    else
      let
        b0 = builtins.head branches;
        rest = builtins.tail branches;
        A = b0.type;
        B = sumOfTypes (map (b: b.type) rest);
        carrier = H.sum A B;
      in
      H.sumElim 0 A B (H.lam "_" carrier (_: bool))
        (H.lam "a" A (a: app (decide b0.kt) a))
        (H.lam "r" B (r: variantBody rest r))
        scrut;

  # Variant/Either witness: nested `sumElim` over the native variant carrier.
  # Any null branch KType ⇒ null (host guard kept).
  mkVariantPred = { carrier, branches }:
    if branches == [ ] || builtins.any (b: b.kt == null) branches then null
    else
      let domain = sumOfTypes (map (b: b.type) branches); in
      mkKernelPred {
        name = "compoundStructural";
        predTerm = H.lam "x" domain (x: variantBody branches x);
        inherit carrier;
        bridge = elaborateValue carrier;
      };

  # Maybe witness: `inl` decides the inner child, `inr` (absence) accepts.
  mkMaybePred = { carrier, inner, innerKt }:
    if innerKt == null then null
    else
      mkKernelPred {
        name = "compoundStructural";
        predTerm = H.lam "x" carrier (x:
          H.sumElim 0 inner H.unit (H.lam "_" carrier (_: bool))
            (H.lam "v" inner (v: app (decide innerKt) v))
            (H.lam "_" H.unit (_: true_))
            x);
        inherit carrier;
        bridge = elaborateValue carrier;
      };
in
{
  scope = {
    reflect = api.namespace {
      description = "fx.tc.kernel.reflect: reflect a Nix-side carrier type into its KType code (reflect/reflectRefine), the checkable Boolean predicate vocabulary for refinement arms — Int over the primitive carrier via the host-backed intLe/intEq (positiveInt, nonNegativeInt, inRangeInt, eqInt) and String literal-set membership (oneOfStrTerm, via strEq) — and the KernelPred witness layer (mkKernelPred, andKP, isKernelPred, sealed, kernelExpressible, ktypeOf, deriveGuard) with ready-made witnesses: Int (intPositive, intNonNegative, intInRange, intEq) and String (strOneOf), O(1)-bridged and guard-derived from their kernel terms.";
      value = {
        inherit reflect reflectRefine
          positiveInt nonNegativeInt inRangeInt eqInt
          oneOfStrTerm
          isKernelPred sealed mkKernelPred andKP ktypeOf kernelExpressible deriveGuard
          intPositive intNonNegative intInRange intEq
          strOneOf
          mkCompoundPred mkVariantPred mkMaybePred;
      };
    };
  };

  tests =
    let
      # A concrete mu carrier, mirroring the acceptance suite.
      B = H.datatype "B" [ (H.con "tt0" [ ]) (H.con "ff0" [ ]) ];
      A = H.mu B.D H.tt;

      rPos = reflectRefine int_ positiveInt;
      rRange = reflectRefine int_ (inRangeInt 2 5);
      rNested = refine (reflectRefine int_ positiveInt) (inRangeInt 2 5);
    in
    {
      # reflect is total over any U_0 carrier: the int_ primitive, a mu-encoded
      # inductive, and the base mu carrier all reflect to a well-typed code.
      "reflect-iota-int-checks" = { expr = chk KType (reflect int_); expected = true; };
      "reflect-iota-mu-checks" = { expr = chk KType (reflect A); expected = true; };
      "reflect-beta-recovers-carrier" = { expr = conv (beta (reflect int_)) int_; expected = true; };

      # The named predicates check at int_ -> Bool.
      "reflect-positive-checks" = { expr = chk (predTy int_) positiveInt; expected = true; };
      "reflect-nonneg-checks" = { expr = chk (predTy int_) nonNegativeInt; expected = true; };
      "reflect-inrange-checks" = { expr = chk (predTy int_) (inRangeInt 2 5); expected = true; };
      "reflect-eqint-checks" = { expr = chk (predTy int_) (eqInt 3); expected = true; };

      # reflectRefine produces a well-typed code at the single universe; the
      # carrier is constant along refinement.
      "reflect-refine-positive-checks" = { expr = chk KType rPos; expected = true; };
      "reflect-refine-inrange-checks" = { expr = chk KType rRange; expected = true; };
      "reflect-refine-nested-checks" = { expr = chk KType rNested; expected = true; };
      "reflect-refine-beta-constant" = { expr = conv (beta rRange) int_; expected = true; };

      # Direct decide-at-witness: positivity rejects 0, accepts 2.
      "reflect-positive-at-0" = { expr = conv (app positiveInt (intLit 0)) false_; expected = true; };
      "reflect-positive-at-2" = { expr = conv (app positiveInt (intLit 2)) true_; expected = true; };

      # decide on the refined code agrees with the predicate at concrete witnesses.
      "reflect-decide-positive-0" = { expr = conv (app (decide rPos) (intLit 0)) false_; expected = true; };
      "reflect-decide-positive-2" = { expr = conv (app (decide rPos) (intLit 2)) true_; expected = true; };

      # Range [2,5]: below, at lower bound, at upper bound, above.
      "reflect-decide-range-1" = { expr = conv (app (decide rRange) (intLit 1)) false_; expected = true; };
      "reflect-decide-range-2" = { expr = conv (app (decide rRange) (intLit 2)) true_; expected = true; };
      "reflect-decide-range-5" = { expr = conv (app (decide rRange) (intLit 5)) true_; expected = true; };
      "reflect-decide-range-6" = { expr = conv (app (decide rRange) (intLit 6)) false_; expected = true; };

      # The int_ order/equality primitives decide bridged literals as host <=/==,
      # across sign quadrants and the zero boundary.
      "reflect-intle-1-2" = { expr = conv (H.intLe (intLit 1) (intLit 2)) true_; expected = true; };
      "reflect-intle-3-2" = { expr = conv (H.intLe (intLit 3) (intLit 2)) false_; expected = true; };
      "reflect-intle-neg1-0" = { expr = conv (H.intLe (intLit (-1)) (intLit 0)) true_; expected = true; };
      "reflect-intle-neg1-neg3" = { expr = conv (H.intLe (intLit (-1)) (intLit (-3))) false_; expected = true; };
      "reflect-inteq-3-3" = { expr = conv (H.intEq (intLit 3) (intLit 3)) true_; expected = true; };
      "reflect-inteq-3-4" = { expr = conv (H.intEq (intLit 3) (intLit 4)) false_; expected = true; };
      "reflect-inteq-cross-sign" = { expr = conv (H.intEq (intLit 2) (intLit (-2))) false_; expected = true; };

      # decide on the int_-refined code at signed and large-magnitude witnesses;
      # the O(1) intLit bridge makes the 10^8 case as cheap as any other (no
      # unary tower — the regression this whole vocabulary exists to avoid).
      "reflect-decide-positive-neg3" = { expr = conv (app (decide (reflectRefine int_ positiveInt)) (intLit (-3))) false_; expected = true; };
      "reflect-decide-positive-zero" = { expr = conv (app (decide (reflectRefine int_ positiveInt)) (intLit 0)) false_; expected = true; };
      "reflect-decide-positive-large" = { expr = conv (app (decide (reflectRefine int_ positiveInt)) (intLit 100000000)) true_; expected = true; };

      # Witnesses are recognised; raw lambdas are not.
      "reflect-iskernelpred-witness" = { expr = isKernelPred intPositive; expected = true; };
      "reflect-iskernelpred-rawlambda" = { expr = isKernelPred (x: x); expected = false; };

      # kernelExpressible fail-closed: witness true; raw / missing / mistyped false.
      "reflect-ke-witness-true" = { expr = kernelExpressible intPositive; expected = true; };
      "reflect-ke-rawlambda-false" = { expr = kernelExpressible (x: x); expected = false; };
      "reflect-ke-missing-false" = { expr = kernelExpressible { _tag = "KernelPred"; }; expected = false; };
      "reflect-ke-mistyped-false" = {
        expr = kernelExpressible (mkKernelPred { name = "intPositive"; predTerm = positiveInt; carrier = string; bridge = stringLit; });
        expected = false;
      };

      # Seal: only registered-provenance witnesses are trusted; hand-rolled or
      # foreign-tagged ones fail closed even when the predicate is sound.
      "reflect-sealed-witness" = { expr = sealed intPositive; expected = true; };
      "reflect-sealed-handrolled-false" = {
        expr = sealed { _tag = "KernelPred"; predTerms = [ positiveInt ]; carrier = int_; bridge = intLit; };
        expected = false;
      };
      "reflect-ke-handrolled-false" = {
        expr = kernelExpressible { _tag = "KernelPred"; predTerms = [ positiveInt ]; carrier = int_; bridge = intLit; };
        expected = false;
      };
      "reflect-derive-handrolled-rejects" = {
        expr = (deriveGuard {
          _tag = "KernelPred"; provenance = [ "forged" ];
          predTerms = [ positiveInt ]; carrier = int_; bridge = intLit;
        }) 5;
        expected = false;
      };
      "reflect-andkp-sealed" = { expr = sealed (andKP intNonNegative (intInRange (-5) 5)); expected = true; };
      "reflect-andkp-provenance" = {
        expr = (andKP intNonNegative (intInRange (-5) 5)).provenance;
        expected = [ "intNonNegative" "intInRange" ];
      };

      # ktypeOf denotes a well-typed KType.
      "reflect-ktypeof-checks" = { expr = chk KType (ktypeOf intPositive); expected = true; };

      # The derived guard decides signed witnesses, including negatives.
      "reflect-derive-positive-5" = { expr = (deriveGuard intPositive) 5; expected = true; };
      "reflect-derive-positive-0" = { expr = (deriveGuard intPositive) 0; expected = false; };
      "reflect-derive-positive-neg3" = { expr = (deriveGuard intPositive) (-3); expected = false; };
      "reflect-derive-nonneg-0" = { expr = (deriveGuard intNonNegative) 0; expected = true; };
      "reflect-derive-nonneg-neg1" = { expr = (deriveGuard intNonNegative) (-1); expected = false; };
      "reflect-derive-inrange-in" = { expr = (deriveGuard (intInRange (-2) 3)) 0; expected = true; };
      "reflect-derive-inrange-lo" = { expr = (deriveGuard (intInRange (-2) 3)) (-2); expected = true; };
      "reflect-derive-inrange-out" = { expr = (deriveGuard (intInRange (-2) 3)) 4; expected = false; };
      "reflect-derive-eq-hit" = { expr = (deriveGuard (intEq (-1))) (-1); expected = true; };
      "reflect-derive-eq-miss" = { expr = (deriveGuard (intEq (-1))) 1; expected = false; };

      # andKP concatenates stacks: the composite checks at KType, stays
      # expressible, and its derived guard conjoins both predicates.
      "reflect-andkp-ktype-checks" = {
        expr = chk KType (ktypeOf (andKP intNonNegative (intInRange (-5) 5)));
        expected = true;
      };
      "reflect-andkp-expressible" = {
        expr = kernelExpressible (andKP intNonNegative (intInRange (-5) 5));
        expected = true;
      };
      "reflect-andkp-in" = { expr = (deriveGuard (andKP intNonNegative (intInRange (-5) 5))) 3; expected = true; };
      "reflect-andkp-fails-left" = { expr = (deriveGuard (andKP intNonNegative (intInRange (-5) 5))) (-1); expected = false; };
      "reflect-andkp-fails-right" = { expr = (deriveGuard (andKP intNonNegative (intInRange (-5) 5))) 6; expected = false; };

      # Three-deep composition conjoins the whole stack.
      "reflect-andkp-three-hit" = {
        expr = (deriveGuard (andKP (andKP intPositive (intInRange 1 100)) (intEq 7))) 7;
        expected = true;
      };
      "reflect-andkp-three-miss" = {
        expr = (deriveGuard (andKP (andKP intPositive (intInRange 1 100)) (intEq 7))) 8;
        expected = false;
      };

      # String literal-enum witness: membership via strEq; singleton = equality.
      "reflect-stronof-checks" = { expr = chk (predTy string) (oneOfStrTerm [ "a" "b" ]); expected = true; };
      "reflect-stronof-ktype-checks" = { expr = chk KType (ktypeOf (strOneOf [ "a" "b" ])); expected = true; };
      "reflect-stronof-sealed" = { expr = sealed (strOneOf [ "a" "b" ]); expected = true; };
      "reflect-stronof-expressible" = { expr = kernelExpressible (strOneOf [ "a" "b" ]); expected = true; };
      "reflect-stronof-beta-string" = { expr = conv (beta (reflect string)) string; expected = true; };
      "reflect-derive-stronof-hit-first" = { expr = (deriveGuard (strOneOf [ "a" "b" ])) "a"; expected = true; };
      "reflect-derive-stronof-hit-last" = { expr = (deriveGuard (strOneOf [ "a" "b" ])) "b"; expected = true; };
      "reflect-derive-stronof-miss" = { expr = (deriveGuard (strOneOf [ "a" "b" ])) "c"; expected = false; };
      "reflect-derive-stronof-singleton-hit" = { expr = (deriveGuard (strOneOf [ "a" ])) "a"; expected = true; };
      "reflect-derive-stronof-singleton-miss" = { expr = (deriveGuard (strOneOf [ "a" ])) "b"; expected = false; };
      # Fail-closed: a non-string value's bridge throws; deriveGuard's tryEval rejects.
      "reflect-derive-stronof-noncarrier" = { expr = (deriveGuard (strOneOf [ "a" ])) 5; expected = false; };
      "reflect-derive-stronof-triple" = { expr = (deriveGuard (strOneOf [ "a" "b" "c" ])) "b"; expected = true; };
    };
}
