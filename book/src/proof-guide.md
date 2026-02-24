# Proof Guide

Nix configurations are concrete at eval time. Every field, every value,
every list element is known before anything builds. The nix-effects
kernel exploits this: it normalizes both sides of an equation via NbE,
and if they reduce to the same value, `Refl` proves them equal. No
symbolic reasoning, no induction over unknowns — just computation on
concrete data, checked by a type-theoretic kernel implemented in 1,300
lines of pure Nix.

This chapter builds proofs incrementally, from `0 + 0 = 0` through
the J eliminator to a production service builder where invalid
configurations are rejected by a machine-checked proof. Every example
is runnable. The code comes from three files in the repository:
[`proof-basics.nix`](https://github.com/kleisli-io/nix-effects/blob/main/examples/proof-basics.nix),
[`equality-proofs.nix`](https://github.com/kleisli-io/nix-effects/blob/main/examples/equality-proofs.nix), and
[`verified-functions.nix`](https://github.com/kleisli-io/nix-effects/blob/main/examples/verified-functions.nix).

**Prerequisites.** You should know what a function is and what `let`
bindings do in Nix. Familiarity with the Getting Started chapter helps
but isn't required. You do not need to know type theory.

## Your first proof

A proof in nix-effects is a term that type-checks against an equality
type. The simplest equality type is `Eq(Nat, 0+0, 0)` — the claim
that adding zero to zero produces zero. The proof term is `Refl`, which
says "both sides are the same." The kernel checks this by normalizing
`0 + 0`, arriving at `0`, and confirming that `Refl` witnesses `0 = 0`.

```nix
let
  H = fx.types.hoas;
  inherit (H) nat eq zero refl checkHoas;

  # Addition by structural recursion on the first argument
  add = m: n:
    H.ind (H.lam "_" nat (_: nat)) n
      (H.lam "k" nat (_: H.lam "ih" nat (ih: H.succ ih))) m;
in
  # Prove: 0 + 0 = 0
  (checkHoas (eq nat (add zero zero) zero) refl).tag == "refl"
  # → true
```

`checkHoas` is the kernel's entry point. It takes a type and a term,
runs bidirectional type checking with normalization by evaluation, and
returns a result. If the result's `tag` is `"refl"`, the proof was
accepted. If it has an `error` field, the kernel rejected it.

The kernel doesn't pattern-match on `0 + 0 = 0` as a special case. It
evaluates `add(zero, zero)` by running the `NatElim` eliminator — the
base case fires, returns `n` (which is `zero`), and the kernel sees
`Eq(Nat, zero, zero)`. `Refl` witnesses any `Eq(A, x, x)`, so the
proof goes through.

Larger numbers work the same way. The kernel unrolls the recursion:

```nix
# 3 + 5 = 8
(checkHoas (eq nat (add (H.natLit 3) (H.natLit 5)) (H.natLit 8)) refl).tag == "refl"

# 10 + 7 = 17
(checkHoas (eq nat (add (H.natLit 10) (H.natLit 7)) (H.natLit 17)) refl).tag == "refl"
```

Both reduce to `true`. The kernel normalizes `add(3, 5)` step by
step — three `succ` peels, then the base case returns `5`, then three
`succ` wrappers are reapplied — and confirms the result is `8`.

## Dependent witnesses

A computational equality says "these two things are the same." A
dependent witness says "here is a value, and here is evidence that
it has a property." The Sigma type `Σ(x:A).P(x)` packages both: a
value `x` of type `A`, and a proof that `P(x)` holds.

```nix
let
  H = fx.types.hoas;
  inherit (H) nat eq sigma zero pair refl checkHoas;
in {
  # "There exists x : Nat such that x = 0" — witnessed by (0, Refl)
  witness = let
    ty = sigma "x" nat (x: eq nat x zero);
    tm = pair zero refl ty;
  in (checkHoas ty tm).tag == "pair";
  # → true
}
```

The type `Σ(x:Nat). Eq(Nat, x, 0)` says "a natural number equal to
zero." The term `(0, Refl)` inhabits it: `0` for the value, `Refl` for
the proof that `0 = 0`. The kernel checks both components — it
confirms `0 : Nat` and `Refl : Eq(Nat, 0, 0)`.

Witnesses get more interesting when the property involves computation:

```nix
# "There exists x such that 3+5 = x" — witnessed by (8, Refl)
witnessAdd = let
  add = m: n:
    H.ind (H.lam "_" nat (_: nat)) n
      (H.lam "k" nat (_: H.lam "ih" nat (ih: H.succ ih))) m;
  ty = sigma "x" nat (x: eq nat (add (H.natLit 3) (H.natLit 5)) x);
  tm = pair (H.natLit 8) refl ty;
in (checkHoas ty tm).tag == "pair";
```

The kernel normalizes `add(3, 5)` to `8`, checks that `8` matches the
witness value, and accepts the proof. If you claimed the witness was
`7`, the kernel would reject it — `Refl` can't witness `8 = 7`.

## Eliminators

Eliminators are how you compute over inductive types in type theory.
Where Nix uses `if`/`else` and list folds, the kernel uses eliminators:
structured recursion with a *motive* that declares what type the result
has. The motive is what makes these dependently typed — the return type
can vary based on the input.

### Booleans

`BoolElim(motive, trueCase, falseCase, scrutinee)` — case analysis on
a boolean. With a constant motive (return type doesn't depend on the
boolean), it's equivalent to an if/else:

```nix
let
  H = fx.types.hoas;
  inherit (H) nat bool eq zero refl boolElim checkHoas;
in {
  # if true then 42 else 0 = 42
  trueCase = let
    result = boolElim (H.lam "_" bool (_: nat)) (H.natLit 42) zero H.true_;
  in (checkHoas (eq nat result (H.natLit 42)) refl).tag == "refl";

  # if false then 42 else 0 = 0
  falseCase = let
    result = boolElim (H.lam "_" bool (_: nat)) (H.natLit 42) zero H.false_;
  in (checkHoas (eq nat result zero) refl).tag == "refl";
}
```

### Natural numbers

`NatElim(motive, base, step, n)` — structural recursion. The base
case handles zero, the step case takes the predecessor `k` and the
inductive hypothesis `ih` (the result for `k`) and produces the result
for `S(k)`:

```nix
let
  H = fx.types.hoas;
  inherit (H) nat eq refl checkHoas;

  # double(n): double(0) = 0, double(S(k)) = S(S(double(k)))
  double = n: H.ind (H.lam "_" nat (_: nat)) H.zero
    (H.lam "k" nat (_: H.lam "ih" nat (ih: H.succ (H.succ ih)))) n;
in
  # double(4) = 8
  (checkHoas (eq nat (double (H.natLit 4)) (H.natLit 8)) refl).tag == "refl"
```

The kernel unrolls four steps: `double(4) = S(S(double(3))) = ... = 8`.

### Lists

`ListElim(elemType, motive, nilCase, consCase, list)` — structural
recursion on lists. The nil case provides the base value, the cons case
takes the head, tail, and inductive hypothesis:

```nix
let
  H = fx.types.hoas;
  inherit (H) nat eq refl checkHoas;

  list123 = H.cons nat (H.natLit 1) (H.cons nat (H.natLit 2)
              (H.cons nat (H.natLit 3) (H.nil nat)));

  # sum(xs): fold with addition
  sumList = xs: H.listElim nat (H.lam "_" (H.listOf nat) (_: nat)) H.zero
    (H.lam "h" nat (h: H.lam "t" (H.listOf nat) (_:
      H.lam "ih" nat (ih:
        H.ind (H.lam "_" nat (_: nat)) ih
          (H.lam "k" nat (_: H.lam "ih2" nat (ih2: H.succ ih2))) h)))) xs;
in
  # sum([1, 2, 3]) = 6
  (checkHoas (eq nat (sumList list123) (H.natLit 6)) refl).tag == "refl"
```

### Sums (coproducts)

`SumElim(L, R, motive, leftCase, rightCase, scrutinee)` — case
analysis on `Left(a)` or `Right(b)`:

```nix
let
  H = fx.types.hoas;
  inherit (H) nat bool sum eq zero refl checkHoas;
in {
  # case Left(5) of { Left n → n; Right _ → 0 } = 5
  leftCase = let
    scrut = H.inl nat bool (H.natLit 5);
    result = H.sumElim nat bool (H.lam "_" (sum nat bool) (_: nat))
      (H.lam "n" nat (n: n))
      (H.lam "b" bool (_: zero))
      scrut;
  in (checkHoas (eq nat result (H.natLit 5)) refl).tag == "refl";
}
```

## The J eliminator

Everything above uses `Refl` on equalities that the kernel verifies
by computation — normalize both sides, confirm they match. But what if
you want to reason *about* equalities? Prove that equality is
symmetric, or that applying a function to equal inputs gives equal
outputs? That requires the J eliminator, the fundamental proof
principle for identity types in Martin-Löf type theory [1].

J says: if you can prove something about `x = x` (the reflexive case),
you can prove it about any `x = y` where the equality is witnessed.

```
J(A, a, P, pr, b, eq)
  A  : type
  a  : left side of the equality
  P  : λ(y:A). λ(_:Eq(A,a,y)). Type    — the motive
  pr : P(a, refl)                       — the base case (when y = a)
  b  : right side
  eq : Eq(A, a, b)                      — proof that a = b
  Returns: P(b, eq)

Computation rule: J(A, a, P, pr, a, refl) = pr
```

When the equality proof is `Refl`, J returns the base case directly.
The kernel reduces `J(..., refl)` to `pr`, and the proof goes through.

### Congruence

If `x = y`, then `f(x) = f(y)` for any function `f`. This is the
standard *cong* combinator, derived from J:

```nix
let
  H = fx.types.hoas;
  inherit (H) nat eq u forall refl checkHoas;

  congType =
    forall "A" (u 0) (a:
      forall "B" (u 0) (b:
        forall "f" (forall "_" a (_: b)) (f:
          forall "x" a (x:
            forall "y" a (y:
              forall "_" (eq a x y) (_:
                eq b (H.app f x) (H.app f y)))))));

  congTerm = H.lam "A" (u 0) (a:
    H.lam "B" (u 0) (b:
      H.lam "f" (forall "_" a (_: b)) (f:
        H.lam "x" a (x:
          H.lam "y" a (y:
            H.lam "p" (eq a x y) (p:
              H.j a x
                (H.lam "y'" a (y':
                  H.lam "_" (eq a x y') (_:
                    eq b (H.app f x) (H.app f y'))))
                refl y p))))));
in
  (checkHoas congType congTerm).tag == "lam"
```

The derivation: J eliminates the proof `p : Eq(A, x, y)`. The motive
says "given `y'` equal to `x`, produce `Eq(B, f(x), f(y'))`." In the
base case, `y' = x`, so the goal is `Eq(B, f(x), f(x))` — which
`Refl` proves. J then transports this to `Eq(B, f(x), f(y))`.

This generic combinator type-checks with abstract variables `A`, `B`,
`f`, `x`, `y` — the kernel verifies the reasoning is valid for all
inputs. On concrete data, J receives `Refl` (since concrete equalities
reduce by computation), and the kernel simplifies:

```nix
# Concrete: from add(2,1) = 3, derive succ(add(2,1)) = succ(3)
congConcrete = let
  add21 = add (H.natLit 2) (H.succ H.zero);
  three = H.natLit 3;
in (checkHoas
    (eq nat (H.succ add21) (H.succ three))
    (H.j nat add21
      (H.lam "y" nat (y:
        H.lam "_" (eq nat add21 y) (_:
          eq nat (H.succ add21) (H.succ y))))
      refl three refl)).tag == "j";
```

### Symmetry

If `x = y`, then `y = x`. The motive is `λy'.λ_. Eq(A, y', x)` —
when `y' = x`, the goal is `Eq(A, x, x)`, proved by `Refl`:

```nix
# sym : Π(A:U₀). Π(x:A). Π(y:A). Eq(A,x,y) → Eq(A,y,x)
symTerm = H.lam "A" (u 0) (a:
  H.lam "x" a (x:
    H.lam "y" a (y:
      H.lam "p" (eq a x y) (p:
        H.j a x
          (H.lam "y'" a (y': H.lam "_" (eq a x y') (_: eq a y' x)))
          refl y p))));
```

### Transitivity

If `x = y` and `y = z`, then `x = z`. Fix `p : Eq(A, x, y)`, then
eliminate `q` with J. The motive is `λz'.λ_. Eq(A, x, z')` — when
`z' = y`, the goal is `Eq(A, x, y)`, proved by `p`:

```nix
# trans : Π(A:U₀). Π(x:A). Π(y:A). Π(z:A). Eq(A,x,y) → Eq(A,y,z) → Eq(A,x,z)
transTerm = H.lam "A" (u 0) (a:
  H.lam "x" a (x:
    H.lam "y" a (y:
      H.lam "z" a (z:
        H.lam "p" (eq a x y) (p:
          H.lam "q" (eq a y z) (q:
            H.j a y
              (H.lam "z'" a (z': H.lam "_" (eq a y z') (_: eq a x z')))
              p z q))))));
```

### Transport

The most general form. If `x = y` and `P(x)` holds, then `P(y)` holds.
Congruence, symmetry, and transitivity are all special cases.

```nix
# transport : Π(A:U₀). Π(P:A→U₀). Π(x:A). Π(y:A). Eq(A,x,y) → P(x) → P(y)
transportTerm = H.lam "A" (u 0) (a:
  H.lam "P" (forall "_" a (_: u 0)) (bigP:
    H.lam "x" a (x:
      H.lam "y" a (y:
        H.lam "p" (eq a x y) (p:
          H.lam "px" (H.app bigP x) (px:
            H.j a x
              (H.lam "y'" a (y': H.lam "_" (eq a x y') (_: H.app bigP y')))
              px y p))))));
```

### Chaining proofs

J applications compose. Here we chain congruence (lift through `succ`)
with symmetry (reverse the equality) — two J applications, the output
of the first feeding as the equality proof to the second:

```nix
# From Eq(Nat, add(2,1), 3):
#   Step 1 (cong succ): Eq(Nat, S(add(2,1)), S(3))
#   Step 2 (sym):       Eq(Nat, S(3), S(add(2,1)))
combinedProof = let
  add21 = add (H.natLit 2) (H.succ H.zero);
  three = H.natLit 3;
  sadd21 = H.succ add21;
  sthree = H.succ three;
  # Step 1: cong succ
  congStep = H.j nat add21
    (H.lam "y" nat (y: H.lam "_" (eq nat add21 y) (_: eq nat sadd21 (H.succ y))))
    refl three refl;
  # Step 2: sym on the cong result
in (checkHoas (eq nat sthree sadd21)
    (H.j nat sadd21
      (H.lam "y" nat (y: H.lam "_" (eq nat sadd21 y) (_: eq nat y sadd21)))
      refl sthree congStep)).tag == "j";
```

## Verified extraction

Proofs establish that properties hold. Verified extraction goes
further: write an implementation in HOAS, the kernel type-checks it
against a specification, and `v.verify` extracts a callable Nix
function. The result is an ordinary Nix value — an integer, a boolean,
a function, a list — but one whose implementation was machine-checked
before use.

### The simplest case

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  # Kernel-verified successor: Nat → Nat
  succFn = v.verify (H.forall "x" H.nat (_: H.nat))
                    (v.fn "x" H.nat (x: H.succ x));
in
  succFn 5    # → 6
```

`v.verify` does three things: elaborates the HOAS into kernel terms,
type-checks the implementation against the type, and extracts the
result as a Nix value. The extracted function is plain Nix — no kernel
overhead at call time.

`v.fn` is a convenience wrapper around `H.lam` that threads the
extraction metadata. You could write raw `H.lam` instead, but `v.fn`
handles the plumbing for multi-argument functions and pattern matching.

### Pattern matching

`v.match` builds a `NatElim` with a constant motive. You provide the
result type, the scrutinee, and branches for `zero` and `succ`:

```nix
# Verified addition: Nat → Nat → Nat
addFn = v.verify (H.forall "m" H.nat (_: H.forall "n" H.nat (_: H.nat)))
  (v.fn "m" H.nat (m: v.fn "n" H.nat (n:
    v.match H.nat m {
      zero = n;
      succ = _k: ih: H.succ ih;
    })));

addFn 2 3    # → 5
addFn 0 7    # → 7
```

The `succ` branch receives two arguments: `k` (the predecessor) and
`ih` (the inductive hypothesis — the result for `k`). For addition,
`ih` is `add(k, n)`, so wrapping it with `succ` gives `add(S(k), n)`.

### Boolean and cross-type elimination

`v.if_` builds a `BoolElim` for verified booleans:

```nix
# Verified not: Bool → Bool
notFn = v.verify (H.forall "b" H.bool (_: H.bool))
  (v.fn "b" H.bool (b:
    v.if_ H.bool b { then_ = v.false_; else_ = v.true_; }));

notFn true     # → false
notFn false    # → true
```

Cross-type elimination — scrutinize one type, return another — works
by specifying a different result type:

```nix
# Verified isZero: Nat → Bool
isZeroFn = v.verify (H.forall "n" H.nat (_: H.bool))
  (v.fn "n" H.nat (n:
    v.match H.bool n {
      zero = v.true_;
      succ = _k: _ih: v.false_;
    }));

isZeroFn 0    # → true
isZeroFn 5    # → false
```

### List operations

`v.map`, `v.filter`, and `v.fold` are verified list combinators. Each
takes HOAS terms, not Nix functions — the kernel verifies the entire
pipeline:

```nix
# Composed pipeline: filter zeros, then sum
# Input: [0, 3, 0, 2, 1] → Filter: [3, 2, 1] → Sum: 6
composedResult = let
  input = H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 3)
    (H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 2)
      (H.cons H.nat (v.nat 1) (H.nil H.nat)))));
  nonZero = v.fn "n" H.nat (n:
    v.match H.bool n {
      zero = v.false_;
      succ = _k: _ih: v.true_;
    });
  addCombine = v.fn "a" H.nat (a: v.fn "acc" H.nat (acc:
    v.match H.nat a {
      zero = acc;
      succ = _k: ih: H.succ ih;
    }));
in v.verify H.nat (v.fold H.nat H.nat (v.nat 0) addCombine
                     (v.filter H.nat nonZero input));
# → 6
```

The kernel verifies the filter predicate (`Nat → Bool`), the fold
combinator (`Nat → Nat → Nat`), and their composition before extracting
the result. A type error in any component — say, returning a `Nat`
where the filter expects a `Bool` — fails at `nix eval`, not at runtime.

### Records and string operations

The kernel supports record types (elaborated as nested Sigma) and
string equality (`strEq` is a kernel primitive). Together they handle
verified functions over structured data with string fields:

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  RecTy = H.record [
    { name = "name";   type = H.string; }
    { name = "target"; type = H.string; }
  ];

  # Verified: does the name match the target?
  matchFn = v.verify (H.forall "r" RecTy (_: H.bool))
    (v.fn "r" RecTy (r:
      v.strEq (v.field RecTy "name" r) (v.field RecTy "target" r)));
in {
  yes = matchFn { name = "hello"; target = "hello"; };    # → true
  no  = matchFn { name = "hello"; target = "world"; };    # → false
}
```

`v.field` desugars to the right chain of `fst`/`snd` projections for
the field's position in the Sigma chain. `v.strEq` reduces in the
kernel via the `StrEq` primitive — it compares string literals during
normalization, producing `true` or `false` as kernel values.

## Proof-gated derivations

The examples so far verify individual functions or prove individual
equalities. The
[`typed-derivation.nix`](https://github.com/kleisli-io/nix-effects/blob/main/examples/typed-derivation.nix)
example combines them into a proof-gated service builder. To be clear:
this example is contrived. You could enforce the same policy with a few
`assert` statements. The point is that the kernel normalizes and checks
it as a proof obligation rather than a runtime boolean. The interesting
direction is dependent NixOS module types where the type of one option
depends on the value of another; that isn't working yet.

The architecture has three layers:

**Tier 2 — Verified computation.** The kernel computes the effective
protocol. Public-facing services (`bind = "0.0.0.0"`) are forced to
HTTPS regardless of what the config says. The extracted function always
returns the correct protocol because the kernel proved it total.

```nix
effectiveProtocol = v.verify (H.forall "s" ServiceConfig (_: H.string))
  (v.fn "s" ServiceConfig (s:
    v.if_ H.string (v.strEq (v.field ServiceConfig "bind" s)
                             (v.str "0.0.0.0")) {
      then_ = v.str "https";
      else_ = v.field ServiceConfig "protocol" s;
    }));
```

**Tier 3 — Machine-checked proof.** A policy function checks five
constraints: bind address, protocol, log level, and port in allowed
sets, plus the cross-field invariant (public bind requires HTTPS). For
each concrete config, the builder:

1. Encodes the Nix attrset as a kernel record (`elaborateValue`)
2. Applies the policy function to it
3. Normalizes the result via NbE
4. Checks `Refl : Eq(Bool, result, true)`

If the policy evaluates to `true`, `Refl` witnesses `true = true` and
the service builds. If it evaluates to `false`, the kernel rejects
`Refl : Eq(Bool, false, true)` and the build aborts at eval time.

```nix
mkVerifiedService = cfg: let
  cfgHoas  = elaborateValue ServiceConfig cfg;
  applied  = H.app policyAnn cfgHoas;
  proofTy  = H.eq H.bool applied H.true_;
  checked  = H.checkHoas proofTy H.refl;
  protocol = effectiveProtocol cfg;
in if checked ? error
  then throw "Proof rejected: ..."
  else pkgs.writeShellScriptBin cfg.name ''
    echo "${cfg.name} listening on ${protocol}://${cfg.bind}:${cfg.port}"
    ...
  '';
```

The localhost HTTP server passes — all policy constraints hold, the
kernel accepts the proof, and `nix build` produces a runnable binary:

```nix
api-server = mkVerifiedService {
  name = "api-server"; bind = "127.0.0.1";
  port = "8080"; protocol = "http"; logLevel = "info";
};
```

The public HTTP server is rejected — `bind = "0.0.0.0"` with
`protocol = "http"` violates the cross-field invariant. The kernel
normalizes `policy(cfg)` to `false`, and `Refl : Eq(Bool, false, true)`
is ill-typed:

```nix
insecure-public = mkVerifiedService {
  name = "insecure-public"; bind = "0.0.0.0";
  port = "80"; protocol = "http"; logLevel = "debug";
};
# error: Proof rejected: service 'insecure-public' violates policy
```

This is a genuine machine-checked proof, not a runtime assertion. The
kernel's type checker — the same one that verifies `3 + 5 = 8` — does
the work. The proof obligation `Eq(Bool, policy(cfg), true)` is checked
by the same bidirectional algorithm that handles Pi types, Sigma types,
and J elimination. The only difference is that the "theorem" here is
about a service config rather than a natural number.

## What the kernel can and cannot prove

The nix-effects kernel implements Martin-Löf type theory with universes,
dependent functions, dependent pairs, identity types, natural numbers,
booleans, lists, sums, unit, void, and eleven axiomatized Nix
primitives. It can prove any property that reduces to a comparison of
normal forms.

**It can prove:**

- Equalities between computed values: `add(3, 5) = 8`,
  `length([1,2,3]) = 3`, `append([1,2], [3]) = [1,2,3]`
- Properties of concrete data: "this config field is in the allowed
  set," "this port number is valid," "these two strings match"
- Generic combinators: `cong`, `sym`, `trans`, and `transport`
  type-check with abstract variables
- Verified function extraction: any function expressible with the
  kernel's eliminators can be verified and extracted
- Cross-field invariants: "if bind is public, protocol must be HTTPS"

**It cannot prove:**

- **Symbolic induction.** `forall n, n + 0 = n` requires induction over
  an abstract variable. The `NatElim` evaluator only reduces on
  concrete values (`VZero`, `VSucc`), not symbolic ones. You can prove
  `3 + 0 = 3` and `100 + 0 = 100`, but not the universal statement.
  The evaluator would need to produce symbolic normal forms, which is a
  fundamentally different normalization strategy.

- **Properties of Nix builtins.** The kernel axiomatizes `String`,
  `Int`, `Float`, etc. as opaque types. `builtins.stringLength` is not
  a kernel function — the kernel has `strEq` for string comparison but
  no string operations beyond equality and list membership.

- **Eta-expansion.** The kernel does not identify `f` with `λx.f(x)`.
  Functions that are extensionally equal but intensionally different are
  not convertible.

- **User-defined recursive types.** The kernel has inductive types (Nat,
  List, Bool, Sum) built in as eliminators but does not support
  user-defined inductive families. You cannot define a binary tree or a
  red-black tree in the kernel.

For Nix, the "concrete data" restriction is less of a limitation than
it sounds. Nix evaluates configurations completely before building —
every module option, every service config, every package attribute is a
concrete value at eval time. The kernel verifies all computable
properties of that concrete data. What it gives up is proving things
about *all possible* configurations generically. In practice, you prove
properties of the specific configuration being built, which is the one
that matters.

## Quick reference

| Pattern | Type | Proof term |
|---------|------|------------|
| Computational equality | `Eq(A, x, y)` where `x`, `y` normalize to same value | `Refl` |
| Dependent witness | `Σ(x:A). P(x)` | `(value, proof)` |
| Case analysis (bool) | `BoolElim(motive, true_case, false_case, b)` | Result of elimination |
| Structural recursion (nat) | `NatElim(motive, base, step, n)` | Result of elimination |
| List recursion | `ListElim(elem, motive, nil_case, cons_case, xs)` | Result of elimination |
| Sum dispatch | `SumElim(L, R, motive, left_case, right_case, s)` | Result of elimination |
| Congruence | `Eq(A,x,y) → Eq(B, f(x), f(y))` | `J(A, x, λy'.λ_. Eq(B,f(x),f(y')), Refl, y, p)` |
| Symmetry | `Eq(A,x,y) → Eq(A,y,x)` | `J(A, x, λy'.λ_. Eq(A,y',x), Refl, y, p)` |
| Transitivity | `Eq(A,x,y) → Eq(A,y,z) → Eq(A,x,z)` | `J(A, y, λz'.λ_. Eq(A,x,z'), p, z, q)` |
| Transport | `Eq(A,x,y) → P(x) → P(y)` | `J(A, x, λy'.λ_. P(y'), px, y, p)` |
| Ex falso | `Void → A` | `absurd(A, x)` |
| Verified function | `v.verify type impl` | Extracted Nix function |
| Proof-gated build | `Eq(Bool, policy(cfg), true)` | `Refl` (kernel normalizes policy) |

## References

1. Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.

2. The Univalent Foundations Program (2013). *Homotopy Type Theory:
   Univalent Foundations of Mathematics*. Institute for Advanced Study.
   [[pdf](https://homotopytypetheory.org/book/)]

3. Norell, U. (2007). *Towards a practical programming language based
   on dependent type theory*. PhD thesis, Chalmers.
   [[pdf](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf)]
