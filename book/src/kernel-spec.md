# Formal Specification: Type-Checking Kernel

This document is the contract the implementation must satisfy. Every
typing rule, compute rule, and conversion rule is stated precisely.
Every test is derived from this spec. Every invariant the kernel must
maintain is listed.

The spec uses standard type-theoretic notation. No Nix code appears
here — this document is reviewable by anyone who reads dependent type
theory, regardless of implementation language.

---

## 1. Trust Model

The kernel has three layers with strictly decreasing trust requirements.

**Layer 0 — Trusted Computing Base (TCB).** The evaluator, quotation,
and conversion checker. Pure functions. No side effects. No imports
from the effect system. Bugs here compromise soundness. Every line
must be auditable.

- `eval : Env × Tm → Val`
- `quote : ℕ × Val → Tm`
- `conv : ℕ × Val × Val → Bool`

**Layer 1 — Semi-trusted.** The bidirectional type checker. Uses the
TCB and sends effects for error reporting. Bugs here may produce wrong
error messages or reject valid terms, but cannot cause unsoundness
(the TCB rejects ill-typed terms independently).

- `check : Ctx × Tm × Val → Tm`
- `infer : Ctx × Tm → Tm × Val`
- `checkTypeLevel : Ctx × Tm → Tm × ℕ`

**Layer 2 — Untrusted.** The elaborator. Translates surface syntax
(named variables, implicit arguments, level inference, eta-insertion)
into fully explicit core terms. Can have arbitrary bugs without
compromising safety — the kernel verifies the output.

### Failure modes

| Condition | Response | Rationale |
|-----------|----------|-----------|
| Kernel invariant violation | `throw` (crash) | TCB may be buggy; cannot trust own output |
| User type error | Effect `typeError` | Normal operation; handler decides policy |
| Normalization budget exceeded | `throw` (crash) | Layer 0 has no effect access; `tryEval` catches it |
| Unknown term tag | `throw` (crash) | Exhaustiveness violation = kernel bug |

---

## 2. Syntax

### 2.1 Terms (Tm)

The core term language. All binding uses de Bruijn indices. Name
annotations are cosmetic (for error messages only).

```
Tm ::=
  -- Variables and binding
  | Var(i : ℕ)                             -- de Bruijn index
  | Let(n : Name, A : Tm, t : Tm, u : Tm)  -- let n : A = t in u

  -- Functions
  | Pi(n : Name, A : Tm, B : Tm)       -- Π(n : A). B
  | Lam(n : Name, A : Tm, t : Tm)      -- λ(n : A). t
  | App(t : Tm, u : Tm)                -- t u

  -- Pairs
  | Sigma(n : Name, A : Tm, B : Tm)     -- Σ(n : A). B
  | Pair(a : Tm, b : Tm, T : Tm)        -- (a, b) as T
  | Fst(t : Tm)                         -- π₁ t
  | Snd(t : Tm)                         -- π₂ t

  -- Unit
  | Unit                                -- ⊤
  | Tt                                  -- tt

  -- Bootstrap coproduct, private to descPlus interpretation
  | BootSum(A : Tm, B : Tm)             -- A + B
  | BootInl(A : Tm, B : Tm, t : Tm)     -- inl t
  | BootInr(A : Tm, B : Tm, t : Tm)     -- inr t
  | BootSumElim(A : Tm, B : Tm, P : Tm, l : Tm, r : Tm, s : Tm)
    -- private eliminator for descPlus payloads

  -- Bootstrap identity, private to descRet/Lift/index transport
  | BootEq(A : Tm, a : Tm, b : Tm)      -- internal Id_A(a, b)
  | BootRefl                            -- internal refl
  | BootJ(A : Tm, a : Tm, P : Tm, pr : Tm, b : Tm, eq : Tm)
    -- private identity eliminator

  -- Levels (Tarski-style sort of universe levels — see §6.6, §8.5)
  | Level                               -- the Level sort itself, lives at U(0)
  | LevelZero                           -- 0
  | LevelSuc(k : Tm)                    -- successor: k+1
  | LevelMax(a : Tm, b : Tm)            -- join in the level semilattice

  -- Universes (level-indexed, k : Level)
  | U(k : Tm)                           -- Type_k

  -- Descriptions (universe-polymorphic; see §7.6)
  | Desc(K : Tm, I : Tm)                -- Desc^K I — descriptions over index type I
  | DescRet(j : Tm)                     -- ret(j) — leaf returning at index j
  | DescArg(K : Tm, S : Tm, T : Tm)     -- arg^K S T — non-recursive Π over S : U(K)
  | DescRec(j : Tm, D : Tm)             -- rec(j) D — recursive child at index j, then D
  | DescPi(K : Tm, S : Tm, f : Tm, D : Tm)
                                        -- π^K S f D — recursive Π over S : U(K), indexed by f
  | DescPlus(A : Tm, B : Tm)            -- A + B — first-class binary coproduct of descriptions
  | DescElim(K : Tm, P : Tm, onRet : Tm, onArg : Tm,
             onRec : Tm, onPi : Tm, onPlus : Tm, scrut : Tm)
                                        -- description recursor at level K
  | DescInd(D : Tm, motive : Tm, step : Tm, i : Tm, scrut : Tm)
                                        -- generic μ-induction over D at index i

  -- μ-types (description-induced datatypes)
  | Mu(I : Tm, D : Tm, i : Tm)          -- μ I D i — the i-th type in the family classified by D
  | DescCon(D : Tm, i : Tm, payload : Tm)
                                        -- introduction at index i with payload : interp(D, i)

  -- Annotations
  | Ann(t : Tm, A : Tm)                -- (t : A)

  -- Axiomatized primitive types
  | String                              -- string type
  | Int                                 -- integer type
  | Float                               -- float type
  | Attrs                               -- attribute set type
  | Path                                -- path type
  | Function                            -- opaque function type
  | Any                                 -- dynamic/any type

  -- String operations
  | StrEq(lhs : Tm, rhs : Tm)          -- string equality: lhs == rhs → H.bool (derived)

  -- Primitive literals
  | StringLit(s)                        -- string literal
  | IntLit(n)                           -- integer literal
  | FloatLit(f)                         -- float literal
  | AttrsLit                            -- attribute set literal
  | PathLit                             -- path literal
  | FnLit                               -- opaque function literal
  | AnyLit                              -- any literal

```

Public `Nat`, `List`, `Sum`, and `Eq` are not primitive core syntax.
The HOAS prelude generates them as descriptions:

```
H.nat        = Mu(Unit, NatDT.D, Tt)
H.listOf A   = Mu(Unit, ListDT.D A, Tt)
H.sum A B    = Mu(Unit, SumDT.D 0 A B, Tt)
H.eq A a b   = Mu(A, EqDT.D A a, b)

```

Their constructors and eliminators elaborate to `DescCon` and
`DescInd` applications through the datatype macro layer. The kernel
therefore exposes one public induction principle for data: `DescInd`.
The bootstrap coproduct and bootstrap identity above remain internal
support for description interpretation, `DescRet`, `Lift`, and index
transport.

### 2.2 Binding convention

In `Pi(n, A, B)`, `Lam(n, A, t)`, `Sigma(n, A, B)`, and `Let(n, A, t, u)`:
the body (`B`, `t`, or `u`) binds one variable. Index 0 in the body
refers to the bound variable. All other indices shift by 1.

Eliminators take their motives as ordinary function terms, not as
implicit binders. Generated public eliminators build typed HOAS
applications to datatype-specific eliminator functions; the core
eliminator underneath is `DescInd`.

### 2.3 De Bruijn index conventions

Indices count inward from the use site: 0 = most recent binder.

Example: `λ(x : A). λ(y : B). x` is `Lam(x, A, Lam(y, B, Var(1)))`.

---

## 3. Values (Semantic Domain)

Values are the result of evaluation. They use de Bruijn **levels**
(counting outward from the top of the context) instead of indices.

```
Val ::=
  -- Functions
  | VPi(n : Name, A : Val, cl : Closure)   -- Π type
  | VLam(n : Name, A : Val, cl : Closure)  -- λ abstraction

  -- Pairs
  | VSigma(n : Name, A : Val, cl : Closure) -- Σ type
  | VPair(a : Val, b : Val)                  -- pair value

  -- Unit
  | VUnit
  | VTt

  -- Bootstrap coproduct, private to descPlus interpretation
  | VBootSum(A : Val, B : Val)
  | VBootInl(A : Val, B : Val, v : Val)
  | VBootInr(A : Val, B : Val, v : Val)

  -- Bootstrap identity, private to descRet/Lift/index transport
  | VBootEq(A : Val, a : Val, b : Val)
  | VBootRefl

  -- Levels (Tarski-style sort of universe levels — see §6.6, §8.5)
  | VLevel                                -- the Level sort itself
  | VLevelZero                            -- 0
  | VLevelSuc(pred : Val)                 -- successor
  | VLevelMax(lhs : Val, rhs : Val)       -- join

  -- Universes (level-indexed, k : VLevel)
  | VU(k : Val)

  -- Descriptions (universe-polymorphic; see §7.6)
  | VDesc(K : Val, I : Val)                -- Desc^K I
  -- Description constructors are encoded as VDescCon inhabitants of
  -- μ Unit (descDesc I K) tt. Evaluation projects them through the private
  -- DViewRet/DViewArg/DViewRec/DViewPi/DViewPlus semantic view.

  -- μ-types
  | VMu(I : Val, D : Val, i : Val)          -- μ I D i
  | VDescCon(D : Val, i : Val, d : Val)     -- introduction at index i with payload d

  -- Axiomatized primitive types
  | VString | VInt | VFloat | VAttrs | VPath | VFunction | VAny

  -- Primitive literal values
  | VStringLit(s) | VIntLit(n) | VFloatLit(f)
  | VAttrsLit | VPathLit | VFnLit | VAnyLit

  -- Neutrals (stuck computations)
  | VNe(level : ℕ, spine : [Elim])

Elim ::=
  | EApp(v : Val)
  | EFst
  | ESnd
  | EBootSumElim(A : Val, B : Val, P : Val, l : Val, r : Val)
  | EBootJ(A : Val, a : Val, P : Val, pr : Val, b : Val)
  | EStrEq(arg : Val)
  | EDescElim(K : Val, motive : Val, onRet : Val, onArg : Val,
              onRec : Val, onPi : Val, onPlus : Val)
                                            -- carries K so the spine round-trips back to DescElim K
  | EDescInd(D : Val, motive : Val, step : Val, i : Val)

Closure ::= (env : Env, body : Tm)
Env     ::= [Val]          -- list indexed by de Bruijn index

```

### 3.1 Level/index relationship

De Bruijn levels count from the outermost binder: 0 = first-ever
bound variable. Levels are stable under context extension.

Conversion between index and level:

```
index = depth - level - 1
level = depth - index - 1

```

where `depth` is the current binding depth (length of the context).

### 3.2 Fresh variables

A fresh variable at depth `d` is `VNe(d, [])` — a neutral with
level `d` and empty spine. Used in conversion checking to compare
under binders.

### 3.3 Closure instantiation

```
instantiate((env, body), v) = eval([v] ++ env, body)

```

---

## 4. Evaluation Rules

`eval(ρ, t)` interprets term `t` in environment `ρ`, producing
a value. All rules are deterministic.

### 4.1 Variables and let

```
eval(ρ, Var(i))           = ρ[i]
eval(ρ, Let(n, A, t, u))  = eval([eval(ρ, t)] ++ ρ, u)
eval(ρ, Ann(t, A))        = eval(ρ, t)

```

### 4.2 Functions

```
eval(ρ, Pi(n, A, B))   = VPi(n, eval(ρ, A), (ρ, B))
eval(ρ, Lam(n, A, t))  = VLam(n, eval(ρ, A), (ρ, t))
eval(ρ, App(t, u))     = vApp(eval(ρ, t), eval(ρ, u))

```

where `vApp` performs beta reduction or accumulates:

```
vApp(VLam(n, A, cl), v)  = instantiate(cl, v)
vApp(VNe(l, sp), v)      = VNe(l, sp ++ [EApp(v)])
vApp(_, _)               = THROW "kernel bug: vApp on non-function"

```

### 4.3 Pairs

```
eval(ρ, Sigma(n, A, B))  = VSigma(n, eval(ρ, A), (ρ, B))
eval(ρ, Pair(a, b, T))   = VPair(eval(ρ, a), eval(ρ, b))
eval(ρ, Fst(t))          = vFst(eval(ρ, t))
eval(ρ, Snd(t))          = vSnd(eval(ρ, t))

```

where:

```
vFst(VPair(a, b))   = a
vFst(VNe(l, sp))    = VNe(l, sp ++ [EFst])
vFst(_)             = THROW "kernel bug: vFst on non-pair"

vSnd(VPair(a, b))   = b
vSnd(VNe(l, sp))    = VNe(l, sp ++ [ESnd])
vSnd(_)             = THROW "kernel bug: vSnd on non-pair"

```

### 4.4 Generated data families

Natural numbers, lists, public sums, and public equality are prelude
datatypes generated from descriptions. Their types evaluate to
`VMu I D i`; their constructors evaluate to `VDescCon D i payload`;
their eliminators elaborate to `DescInd` over the generated description.

```text
H.nat              == μ Unit NatDT.D tt
H.zero             == descCon NatDT.D tt <zero payload>
H.succ n           == descCon NatDT.D tt <succ payload n>
H.listOf A         == μ Unit (ListDT.D A) tt
H.nil A            == descCon (ListDT.D A) tt <nil payload>
H.cons A h t       == descCon (ListDT.D A) tt <cons payload h t>
H.sum A B          == μ Unit (SumDT.D 0 A B) tt
H.eq A a b         == μ A (EqDT.D A a) b
```

The generated constructor payloads still use private bootstrap
coproduct/identity values where the description interpretation requires
them. These are representation details, not public eliminators.

Deep generated natural/list values are stack-safe through the constructor
flattening and `desc-con` trampoline paths, rather than through primitive
nat/list evaluator cases.

### 4.6 Unit

```
eval(ρ, Unit)  = VUnit
eval(ρ, Tt)    = VTt

```

Unit has no eliminator in the core. The kernel implements ⊤-η: any
neutral of type ⊤ converts against `VTt` (see §6.3). Sound in the
type-free conv because conv is always called on values sharing a type;
if one side is `VTt`, the shared type is ⊤ and the neutral's only
inhabitant is `Tt`.

### 4.7 Bootstrap coproduct

```
eval(ρ, BootSum(A, B))        = VBootSum(eval(ρ, A), eval(ρ, B))
eval(ρ, BootInl(A, B, t))     = VBootInl(eval(ρ, A), eval(ρ, B), eval(ρ, t))
eval(ρ, BootInr(A, B, t))     = VBootInr(eval(ρ, A), eval(ρ, B), eval(ρ, t))
eval(ρ, BootSumElim(A,B,P,l,r,s)) =
  vBootSumElim(eval(ρ,A), eval(ρ,B), eval(ρ,P), eval(ρ,l), eval(ρ,r), eval(ρ,s))

```

where:

```
vBootSumElim(A, B, P, l, r, VBootInl(_, _, v))  = vApp(l, v)
vBootSumElim(A, B, P, l, r, VBootInr(_, _, v))  = vApp(r, v)
vBootSumElim(A, B, P, l, r, VNe(k, sp))         =
  VNe(k, sp ++ [EBootSumElim(A, B, P, l, r)])
vBootSumElim(_, _, _, _, _, _)                  =
  THROW "kernel bug: vBootSumElim on non-boot-sum"

```

This coproduct is private to `descPlus` interpretation. Public `H.sum`,
`H.inl`, `H.inr`, and `H.sumElim` route through generated `SumDT`.

### 4.8 Bootstrap identity

```
eval(ρ, BootEq(A, a, b))        = VBootEq(eval(ρ, A), eval(ρ, a), eval(ρ, b))
eval(ρ, BootRefl)               = VBootRefl
eval(ρ, BootJ(A, a, P, pr, b, eq)) =
  vBootJ(eval(ρ,A), eval(ρ,a), eval(ρ,P), eval(ρ,pr), eval(ρ,b), eval(ρ,eq))

```

where:

```
vBootJ(A, a, P, pr, b, VBootRefl)    = pr
vBootJ(A, a, P, pr, b, VNe(l,sp)) =
  VNe(l, sp ++ [EBootJ(A, a, P, pr, b)])
vBootJ(_, _, _, _, _, _)             = THROW "kernel bug: vBootJ on non-refl"

```

This identity substrate is private to `descRet`, Lift witnesses, index
transport, and no-confusion helpers. Public `H.eq`, `H.refl`, and `H.j`
route through generated `EqDT`.

### 4.9 Universes

```
eval(ρ, U(i)) = VU(i)

```

### 4.10 Axiomatized primitives

Type formers evaluate to their corresponding values. Literals
carry their payload through. No computation, no recursion — these
are axiomatized constants.

```
eval(ρ, String)       = VString
eval(ρ, Int)          = VInt
eval(ρ, Float)        = VFloat
eval(ρ, Attrs)        = VAttrs
eval(ρ, Path)         = VPath
eval(ρ, Function)     = VFunction
eval(ρ, Any)          = VAny

eval(ρ, StringLit(s)) = VStringLit(s)
eval(ρ, IntLit(n))    = VIntLit(n)
eval(ρ, FloatLit(f))  = VFloatLit(f)
eval(ρ, AttrsLit)     = VAttrsLit
eval(ρ, PathLit)      = VPathLit
eval(ρ, FnLit)        = VFnLit
eval(ρ, AnyLit)       = VAnyLit

```

Most primitives have no eliminators. They exist to integrate
Nix's native types into the kernel's type system as opaque,
axiomatized constants. The exception is String, which has
`StrEq` (§4.11).

### 4.11 String equality (StrEq)

```
eval(ρ, StrEq(lhs, rhs)) = vStrEq(eval(ρ, lhs), eval(ρ, rhs))

```

where:

```
-- trueV / falseV are the plus-encoded derived booleans:
--   trueV  = VDescCon boolDescV VTt (VBootInl eqTtV eqTtV VBootRefl)
--   falseV = VDescCon boolDescV VTt (VBootInr eqTtV eqTtV VBootRefl)
-- where boolDescV is the generated encoded BoolDT description.

vStrEq(VStringLit(s₁), VStringLit(s₂)) = if s₁ == s₂ then trueV else falseV
vStrEq(VNe(l, sp),     rhs)            = VNe(l, sp ++ [EStrEq(rhs)])
vStrEq(lhs,            VNe(l, sp))     = VNe(l, sp ++ [EStrEq(lhs)])
vStrEq(_, _)                           = THROW "kernel bug: vStrEq on non-string"

```

`StrEq` is a binary predicate on strings. Both arguments must be of
type `String`. The result type is the derived `H.bool` —
`μ ⊤ (plus (retI tt) (retI tt)) tt` — which is the kernel
representation of booleans after their retirement as primitives.
Unlike other eliminators, StrEq has no motive: it always returns
`H.bool`, not a dependent type.

When both arguments are concrete string literals, `vStrEq` reduces
to the plus-encoded `true_` or `false_` value by Nix-level string
comparison. When either argument is neutral, the neutral's spine is
extended with `EStrEq` carrying the other argument. This is sound
because `StrEq` is symmetric: `StrEq(a, b) ≡ StrEq(b, a)` for all
`a, b : String`.

---

## 5. Quotation Rules

`quote(d, v)` converts a value back to a term, converting levels to
indices. `d` is the current binding depth.

```
quote(d, VPi(n, A, cl))    = Pi(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VLam(n, A, cl))   = Lam(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VSigma(n, A, cl)) = Sigma(n, quote(d, A), quote(d+1, instantiate(cl, fresh(d))))
quote(d, VPair(a, b))      = Pair(quote(d, a), quote(d, b), _)
quote(d, VUnit)            = Unit
quote(d, VTt)              = Tt
quote(d, VBootSum(A, B))       = BootSum(quote(d, A), quote(d, B))
quote(d, VBootInl(A, B, v))    = BootInl(quote(d, A), quote(d, B), quote(d, v))
quote(d, VBootInr(A, B, v))    = BootInr(quote(d, A), quote(d, B), quote(d, v))
quote(d, VBootEq(A, a, b))     = BootEq(quote(d, A), quote(d, a), quote(d, b))
quote(d, VBootRefl)            = BootRefl
quote(d, VU(i))            = U(i)
quote(d, VString)          = String
quote(d, VInt)             = Int
quote(d, VFloat)           = Float
quote(d, VAttrs)           = Attrs
quote(d, VPath)            = Path
quote(d, VFunction)        = Function
quote(d, VAny)             = Any
quote(d, VStringLit(s))    = StringLit(s)
quote(d, VIntLit(n))       = IntLit(n)
quote(d, VFloatLit(f))     = FloatLit(f)
quote(d, VAttrsLit)        = AttrsLit
quote(d, VPathLit)         = PathLit
quote(d, VFnLit)           = FnLit
quote(d, VAnyLit)          = AnyLit
quote(d, VNe(l, sp))       = quoteSp(d, Var(d - l - 1), sp)

quoteSp(d, head, [])                      = head
quoteSp(d, head, [EApp(v) | rest])        = quoteSp(d, App(head, quote(d, v)), rest)
quoteSp(d, head, [EFst | rest])           = quoteSp(d, Fst(head), rest)
quoteSp(d, head, [ESnd | rest])           = quoteSp(d, Snd(head), rest)
quoteSp(d, head, [EBootSumElim(A,B,P,l,r) | rest]) =
  quoteSp(d, BootSumElim(quote(d,A), quote(d,B), quote(d,P), quote(d,l), quote(d,r), head), rest)
quoteSp(d, head, [EBootJ(A,a,P,pr,b) | rest]) =
  quoteSp(d, BootJ(quote(d,A), quote(d,a), quote(d,P), quote(d,pr), quote(d,b), head), rest)
quoteSp(d, head, [EStrEq(arg) | rest]) =
  quoteSp(d, StrEq(head, quote(d, arg)), rest)

fresh(d) = VNe(d, [])

```

---

## 6. Conversion Rules

`conv(d, v₁, v₂)` checks definitional equality of two values at
binding depth `d`. Returns boolean. **No type information is used** —
conversion is purely structural on normalized values.

### 6.1 Structural rules

```
conv(d, VU(i),    VU(j))    = (i == j)
conv(d, VUnit,    VUnit)    = true
conv(d, VTt,      VTt)      = true
conv(d, VBootRefl, VBootRefl) = true
conv(d, VString,      VString)      = true
conv(d, VInt,         VInt)         = true
conv(d, VFloat,       VFloat)       = true
conv(d, VAttrs,       VAttrs)       = true
conv(d, VPath,        VPath)        = true
conv(d, VFunction,    VFunction)    = true
conv(d, VAny,         VAny)         = true
conv(d, VStringLit(s₁), VStringLit(s₂)) = (s₁ == s₂)
conv(d, VIntLit(n₁),    VIntLit(n₂))    = (n₁ == n₂)
conv(d, VFloatLit(f₁),  VFloatLit(f₂))  = (f₁ == f₂)
conv(d, VAttrsLit,    VAttrsLit)    = true
conv(d, VPathLit,     VPathLit)     = true
conv(d, VFnLit,       VFnLit)       = true
conv(d, VAnyLit,      VAnyLit)      = true

```

### 6.2 Binding forms

To compare under binders, generate a fresh variable and instantiate:

```
conv(d, VPi(_, A₁, cl₁), VPi(_, A₂, cl₂)) =
  conv(d, A₁, A₂) ∧ conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

conv(d, VLam(_, _, cl₁), VLam(_, _, cl₂)) =
  conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

conv(d, VLam(_, _, cl), v) =                                        -- Π-η
  conv(d+1, instantiate(cl, fresh(d)), vApp(v, fresh(d)))
  -- only fires when v is not a VLam

conv(d, v, VLam(_, _, cl)) =                                        -- Π-η
  conv(d+1, vApp(v, fresh(d)), instantiate(cl, fresh(d)))
  -- only fires when v is not a VLam

conv(d, VSigma(_, A₁, cl₁), VSigma(_, A₂, cl₂)) =
  conv(d, A₁, A₂) ∧ conv(d+1, instantiate(cl₁, fresh(d)), instantiate(cl₂, fresh(d)))

```

The two Π-η rules fire when exactly one side is a VLam; both sides being
VLam falls through to the symmetric VLam/VLam rule above. Sound because
conv is always called on values sharing a type — if one side is VLam,
that type is VPi, and the other side's only inhabitants up to
definitional equality are its η-expansions. Termination: each rule
strictly decreases VLam-depth on the side it fires on, so no nested
firing can loop.

### 6.3 Compound values

```
conv(d, VPair(a₁, b₁), VPair(a₂, b₂)) =
  conv(d, a₁, a₂) ∧ conv(d, b₁, b₂)

conv(d, VPair(a, b), VNe(l, sp)) =
  conv(d, a, vFst(VNe(l, sp))) ∧ conv(d, b, vSnd(VNe(l, sp)))    -- Σ-η

conv(d, VNe(l, sp), VPair(a, b)) =
  conv(d, vFst(VNe(l, sp)), a) ∧ conv(d, vSnd(VNe(l, sp)), b)    -- Σ-η

conv(d, VTt, VNe(_, _)) = true                                    -- ⊤-η
conv(d, VNe(_, _), VTt) = true                                    -- ⊤-η

conv(d, VBootSum(A₁, B₁), VBootSum(A₂, B₂)) =
  conv(d, A₁, A₂) ∧ conv(d, B₁, B₂)
conv(d, VBootInl(A₁, B₁, v₁), VBootInl(A₂, B₂, v₂)) =
  conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, v₁, v₂)
conv(d, VBootInr(A₁, B₁, v₁), VBootInr(A₂, B₂, v₂)) =
  conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, v₁, v₂)

conv(d, VBootEq(A₁, a₁, b₁), VBootEq(A₂, a₂, b₂)) =
  conv(d, A₁, A₂) ∧ conv(d, a₁, a₂) ∧ conv(d, b₁, b₂)

```

### 6.4 Neutrals

```
conv(d, VNe(l₁, sp₁), VNe(l₂, sp₂)) =
  (l₁ == l₂) ∧ convSp(d, sp₁, sp₂)

convSp(d, [], [])         = true
convSp(d, [e₁|r₁], [e₂|r₂]) = convElim(d, e₁, e₂) ∧ convSp(d, r₁, r₂)
convSp(d, _, _)           = false    -- different lengths

convElim(d, EApp(v₁),   EApp(v₂))   = conv(d, v₁, v₂)
convElim(d, EFst,        EFst)        = true
convElim(d, ESnd,        ESnd)        = true
convElim(d, EBootSumElim(A₁,B₁,P₁,l₁,r₁), EBootSumElim(A₂,B₂,P₂,l₂,r₂)) =
  conv(d, A₁, A₂) ∧ conv(d, B₁, B₂) ∧ conv(d, P₁, P₂) ∧ conv(d, l₁, l₂) ∧ conv(d, r₁, r₂)
convElim(d, EBootJ(A₁,a₁,P₁,pr₁,b₁), EBootJ(A₂,a₂,P₂,pr₂,b₂)) =
  conv(d, A₁, A₂) ∧ conv(d, a₁, a₂) ∧ conv(d, P₁, P₂) ∧ conv(d, pr₁, pr₂) ∧ conv(d, b₁, b₂)
convElim(d, EStrEq(arg₁), EStrEq(arg₂)) = conv(d, arg₁, arg₂)
convElim(_, _, _) = false

```

### 6.5 Catch-all

```
conv(d, _, _) = false

```

Any pair of values not matching the above rules is not definitionally
equal. **Π-eta, Σ-eta, and ⊤-eta are applied** (see §6.2 for Π-η, §6.3
for Σ-η and ⊤-η): `f` converts against `λx. f x` under a fresh binder;
a pair `⟨a, b⟩` converts against a neutral `x : Σ` by projecting both
sides; and any neutral of type `⊤` converts against `tt`. All three
η-rules are sound in the type-free conv because conv is always called
on two values sharing a type — the side carrying the canonical form
(VLam, VPair, VTt) witnesses the shared type's shape (VPi, VSigma, ⊤),
and the other side's η-expansion is its only inhabitant up to
definitional equality.

**Π-η rationale.** Π-η matches the standard semantic models of MLTT
(PER, presheaf, simplicial sets) and is the η-rule consistent with
funext: `f ≡ λx. f x` definitionally. Without it, definitional equality
on Pi-typed values diverges from the equality the surface language
must reason about — every elaborator that produces a function value
would have to maintain its own η-normal form before submitting to
conv. With it, conv handles the canonical-vs-neutral case by descending
under one binder and continues structurally; subsequent ⊤-η, Σ-η, and
neutral-vs-neutral rules fire as usual on the body. This composition
in particular is what closes assemblies that pair a surface
`descPi k S (λ_:S. tt) D` (a 3-arg combinator that fills the kernel's
`f : S → ⊤` slot with a constant lambda) against a kernel-reconstructed
`descPi k S f D` whose `f` is a case-bound variable.

### 6.6 Level conversion (convLevel)

Level expressions form a join-semilattice with `zero` as bottom and
`max` as join. `convLevel(d, k₁, k₂)` checks definitional equality of
two Level values modulo the semilattice laws.

**Fast path** (syntactic equality):

```
convLevel(d, k, k) = true

```

When the same Level value reaches both sides of conv (e.g. a
description's level is reused unchanged across recursive children),
the syntactic-equality check skips the normaliser entirely.
Allocations from re-normalising structurally-identical levels
dominate hot CHECK loops, so this short-circuit is non-optional.

**Normalisation.** Each Level value is reduced to its canonical form
before structural comparison:

- `max(k, zero) = max(zero, k) = k` (zero absorption)
- `max(k, k) = k` (idempotence)
- `suc(max(a, b)) = max(suc(a), suc(b))` (suc distributes over max)
- `max` operands are sorted to a canonical order

The canonical form is `max(s₁, …, sₙ)` where each `sᵢ = sucᵐ(zero)`
or `sᵢ = sucᵐ(VNe(_, _))`, sorted lexicographically. After
normalisation the comparison is structural:

```
convLevel(d, k₁, k₂) = (normLevel(k₁) ≡_struct normLevel(k₂))

```

Used by description and universe CHECK rules (§7.6) to verify that
two level expressions denote the same level.

---

## 7. Typing Rules (Bidirectional)

### 7.1 Contexts

```
Ctx ::= {
  env   : Env,           -- values for evaluation
  types : [Val],         -- types of bound variables (indexed by de Bruijn)
  depth : ℕ              -- current binding depth
}

emptyCtx = { env = [], types = [], depth = 0 }

extend(Γ, n, A) = {
  env   = [fresh(Γ.depth)] ++ Γ.env,
  types = [A] ++ Γ.types,
  depth = Γ.depth + 1
}

lookupType(Γ, i) = Γ.types[i]
  -- THROW if i >= length(Γ.types)

```

### 7.2 Notation

```
Γ ⊢ t ⇐ A  ↝  t'     checking mode:  check(Γ, t, A) = t'
Γ ⊢ t ⇒ A  ↝  t'     synthesis mode: infer(Γ, t) = (t', A)
Γ ⊢ T type  ↝  T'     type formation: checkType(Γ, T) = T'
Γ ⊢ T type@i  ↝  T'   type + level:  checkTypeLevel(Γ, T) = (T', i)

```

The output `t'` is the elaborated core term (fully annotated).

### 7.3 Synthesis rules (infer)

**Var**

```
                lookupType(Γ, i) = A
                ──────────────────────
                Γ ⊢ Var(i) ⇒ A  ↝  Var(i)

```

**Ann** (annotation)

```
                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ ⊢ t ⇐ Â  ↝  t'
                ──────────────────────
                Γ ⊢ Ann(t, A) ⇒ Â  ↝  Ann(t', A')

```

**App** (application)

```
                Γ ⊢ f ⇒ fTy  ↝  f'
                whnf(fTy) = VPi(n, A, cl)
                Γ ⊢ u ⇐ A  ↝  u'
                B = instantiate(cl, eval(Γ.env, u'))
                ──────────────────────
                Γ ⊢ App(f, u) ⇒ B  ↝  App(f', u')

```

**CRITICAL**: `whnf(fTy)` must normalize `fTy` to weak head normal
form before pattern matching. If `fTy` is a let-unfolding or a
neutral that reduces further, the match will fail spuriously.

In this kernel, `eval` already produces WHNF, so `whnf(v) = v` for
all values. But this invariant must be maintained if the value
representation changes.

**Fst** (first projection)

```
                Γ ⊢ t ⇒ tTy  ↝  t'
                whnf(tTy) = VSigma(n, A, cl)
                ──────────────────────
                Γ ⊢ Fst(t) ⇒ A  ↝  Fst(t')

```

**Snd** (second projection)

```
                Γ ⊢ t ⇒ tTy  ↝  t'
                whnf(tTy) = VSigma(n, A, cl)
                B = instantiate(cl, vFst(eval(Γ.env, t')))
                ──────────────────────
                Γ ⊢ Snd(t) ⇒ B  ↝  Snd(t')

```

**Eliminator motive checking (checkMotive).**
All eliminators require a motive `P : domTy → U(k)` for some `k`.
The implementation provides a shared `checkMotive` helper that
handles two forms:

- Lambda motives (`P = λx. body`): extend the context with `x : domTy`
  and verify `body` is a type via `checkType`.
- Non-lambda motives: infer the type and verify it has shape
  `VPi(_, domTy, _ → VU(k))` for some `k`.

The `k` is not fixed — motives may target any universe level,
enabling **large elimination** (eliminators whose return type is a
type, not a value). Generated datatype eliminators use this same
motive checker through `DescInd`.

**Generated eliminators.** Public eliminators for natural numbers,
lists, sums, equality, vectors, finite sets, W-types, and user-defined
datatypes are generated as applications of `DescInd` to their datatype
description. The checker validates the generated motive and branch
terms against the generic indexed-description eliminator.

**Public identity elimination.** `H.j A a P pr b eq` is a HOAS adapter
that preserves the usual J-shaped arguments, but elaborates to
`EqDT.elim`. The adapter checks `pr` against `P a (EqDT.refl A a)` and
checks `eq` against `EqDT.T A a b` before emitting the generated
eliminator spine.

**Bootstrap identity elimination.** Internal description machinery may
still use `BootJ`:

```
                Γ ⊢ A type  ↝  A'    Â = eval(Γ.env, A')
                Γ ⊢ a ⇐ Â  ↝  a'    â = eval(Γ.env, a')
                Γ ⊢ P ⇐ <Π(y : A). Π(e : BootEq A a y). U(k)>  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ pr ⇐ vApp(vApp(P̂, â), VBootRefl)  ↝  pr'
                Γ ⊢ b ⇐ Â  ↝  b'    b̂ = eval(Γ.env, b')
                Γ ⊢ eq ⇐ VBootEq(Â, â, b̂)  ↝  eq'
                ──────────────────────
                Γ ⊢ BootJ(A, a, P, pr, b, eq) ⇒ vApp(vApp(P̂, b̂), eval(Γ.env, eq'))
                   ↝  BootJ(A', a', P', pr', b', eq')

```

**Bootstrap J motive verification.** For non-lambda motives, the
implementation structurally verifies all three components:

1. Outer Pi domain matches `A` (conversion check)
2. Inner Pi domain matches `BootEq(A, a, y)` (conversion check)
3. Innermost codomain is `VU(k)` for some `k`

For lambda motives (`P = λy. body`), the body is checked via
`checkMotive` against `BootEq(A, a, y)`, which performs the same
verification on the inner structure. This catches motive errors
at the motive itself rather than deferring to the base case.

**Axiomatized primitive type formers** (synthesis)

Primitive type formers are synthesized directly — they infer as
inhabitants of `U(0)`:

```
                ──────────────────────
                Γ ⊢ String ⇒ VU(0)  ↝  String

                ──────────────────────
                Γ ⊢ Int ⇒ VU(0)  ↝  Int

```

(Similarly for Float, Attrs, Path, Function, Any — all at level 0.)

**Primitive literals** (synthesis)

Literals synthesize their corresponding type:

```
                ──────────────────────
                Γ ⊢ StringLit(s) ⇒ VString  ↝  StringLit(s)

                ──────────────────────
                Γ ⊢ IntLit(n) ⇒ VInt  ↝  IntLit(n)

                ──────────────────────
                Γ ⊢ FloatLit(f) ⇒ VFloat  ↝  FloatLit(f)

```

(Similarly for AttrsLit → VAttrs, PathLit → VPath,
FnLit → VFunction, AnyLit → VAny.)

**StrEq** (string equality)

```
                boolDescV = eval [] (elab BoolDT.D)
                boolV = VMu VUnit boolDescV VTt
                Γ ⊢ lhs ⇐ VString  ↝  lhs'
                Γ ⊢ rhs ⇐ VString  ↝  rhs'
                ──────────────────────
                Γ ⊢ StrEq(lhs, rhs) ⇒ boolV  ↝  StrEq(lhs', rhs')

```

Both arguments are checked against `VString`. The result type is
the derived `H.bool` — `μ ⊤ (plus (retI tt) (retI tt)) tt` —
written `boolV` above. StrEq is not a dependent eliminator: it has
no motive parameter.

### 7.4 Checking rules (check)

**Lam** (lambda introduction)

```
                whnf(A) = VPi(n, dom, cl)
                Γ' = extend(Γ, n, dom)
                cod = instantiate(cl, fresh(Γ.depth))
                Γ' ⊢ t ⇐ cod  ↝  t'
                ──────────────────────
                Γ ⊢ Lam(n, _, t) ⇐ A  ↝  Lam(n, quote(Γ.depth, dom), t')

```

**Pair** (pair introduction)

```
                whnf(T) = VSigma(n, A, cl)
                Γ ⊢ a ⇐ A  ↝  a'
                B = instantiate(cl, eval(Γ.env, a'))
                Γ ⊢ b ⇐ B  ↝  b'
                ──────────────────────
                Γ ⊢ Pair(a, b, _) ⇐ T  ↝  Pair(a', b', quote(Γ.depth, T))

```

**Generated datatype constructors.** Public constructors such as
`H.zero`, `H.succ`, `H.nil`, `H.cons`, `H.inl`, `H.inr`, and
user-defined datatype constructors check as `DescCon` introductions
against their generated `VMu` type. Their payloads are checked against
the interpretation of the constructor's description. Deep generated
natural/list constructor chains are handled by flat constructor
elaboration and `desc-con` trampolines.

**Tt**

```
                whnf(A) = VUnit
                ──────────────────────
                Γ ⊢ Tt ⇐ A  ↝  Tt

```

**BootRefl**

```
                whnf(T) = VBootEq(A, a, b)
                conv(Γ.depth, a, b) = true
                ──────────────────────
                Γ ⊢ BootRefl ⇐ T  ↝  BootRefl

```

If `conv(Γ.depth, a, b) = false`, this is a **type error**: the
two sides of the equation are not definitionally equal, and
`BootRefl` cannot prove the equation. Public `H.refl` is resolved by
HOAS check mode against generated `EqDT.T A a a`, elaborating to
`EqDT.refl A a`; unrestricted inference for bare public `refl` is
rejected.

**Primitive literals** (checked against their corresponding types)

```
                whnf(A) = VString
                ──────────────────────
                Γ ⊢ StringLit(s) ⇐ A  ↝  StringLit(s)

                whnf(A) = VInt
                ──────────────────────
                Γ ⊢ IntLit(n) ⇐ A  ↝  IntLit(n)

                whnf(A) = VFloat
                ──────────────────────
                Γ ⊢ FloatLit(f) ⇐ A  ↝  FloatLit(f)

                whnf(A) = VAttrs
                ──────────────────────
                Γ ⊢ AttrsLit ⇐ A  ↝  AttrsLit

                whnf(A) = VPath
                ──────────────────────
                Γ ⊢ PathLit ⇐ A  ↝  PathLit

                whnf(A) = VFunction
                ──────────────────────
                Γ ⊢ FnLit ⇐ A  ↝  FnLit

                whnf(A) = VAny
                ──────────────────────
                Γ ⊢ AnyLit ⇐ A  ↝  AnyLit

```

**Let**

```
                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ ⊢ t ⇐ Â  ↝  t'
                t̂ = eval(Γ.env, t')
                Γ' = { env = [t̂] ++ Γ.env, types = [Â] ++ Γ.types, depth = Γ.depth + 1 }
                Γ' ⊢ u ⇐ B  ↝  u'
                ──────────────────────
                Γ ⊢ Let(n, A, t, u) ⇐ B  ↝  Let(n, A', t', u')

```

Note: `Let` in checking mode — the expected type `B` is for the
body `u`, not for the definition `t`.

**Sub** (mode switch: fall through to synthesis)

```
                Γ ⊢ t ⇒ A  ↝  t'
                conv(Γ.depth, A, B) = true   -- or cumulativity check
                ──────────────────────
                Γ ⊢ t ⇐ B  ↝  t'

```

This is the catch-all. If no other checking rule applies, try
synthesis and verify the inferred type matches the expected type.

### 7.5 Type formation (checkType / checkTypeLevel)

The implementation provides two variants: `checkType(Γ, T)` returns
only the elaborated term, while `checkTypeLevel(Γ, T)` returns both
the elaborated term and the universe level. `checkType` is a thin
wrapper: `checkType(Γ, T) = checkTypeLevel(Γ, T).term`. Universe
levels are computed structurally during the type formation check
(see §8.2), not by post-hoc inspection of evaluated values.

```
                ──────────────────────
                Γ ⊢ Unit type  ↝  Unit

                ──────────────────────
                Γ ⊢ String type  ↝  String

                (Similarly for Int, Float, Attrs, Path, Function, Any)

                ──────────────────────
                Γ ⊢ U(i) type  ↝  U(i)

                Γ ⊢ A type  ↝  A'
                Γ ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ BootSum(A, B) type  ↝  BootSum(A', B')

                Γ ⊢ A type  ↝  A'     Â = eval(Γ.env, A')
                Γ ⊢ a ⇐ Â  ↝  a'
                Γ ⊢ b ⇐ Â  ↝  b'
                ──────────────────────
                Γ ⊢ BootEq(A, a, b) type  ↝  BootEq(A', a', b')

                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ' = extend(Γ, n, Â)
                Γ' ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ Pi(n, A, B) type  ↝  Pi(n, A', B')

                Γ ⊢ A type  ↝  A'
                Â = eval(Γ.env, A')
                Γ' = extend(Γ, n, Â)
                Γ' ⊢ B type  ↝  B'
                ──────────────────────
                Γ ⊢ Sigma(n, A, B) type  ↝  Sigma(n, A', B')

                -- Fallback: infer and check it's a universe
                Γ ⊢ T ⇒ A  ↝  T'
                whnf(A) = VU(i)
                ──────────────────────
                Γ ⊢ T type  ↝  T'

```

Public generated data types enter this judgment through the fallback:
their expanded `Mu(...)` terms infer a universe.

### 7.6 Descriptions: typing rules

Descriptions classify strictly-positive datatype signatures over an
index type `I`. A description `D : Desc^k I` quantifies over at most
universe level `k`: `descArg^k S T` requires `S : U(k)`, and
`descPi^k S f D` requires `S : U(k)` and `f : S → I`. The
description's level `k` is recovered from the surrounding `μ` (via
`mu I D i`) at elaboration time; CHECK rules thread `k` through
recursive children without re-synthesising it ("homogeneity by
typing", below).

**Notation.** `Desc^k I` is the kernel value `VDesc(K, Î)` where
`K : Level` (§8.5). `μ I D i` is the kernel value `VMu(Î, D̂, î)`,
the `i`-th type in the family classified by `D`.

#### 7.6.1 desc-elim INFER (universe-polymorphic)

`descElim^K` recurses over a description at level `K`. The motive,
each case branch, and the eliminated description must agree on `K`:

```
                Γ ⊢ K ⇐ Level  ↝  K'    K̂ = eval(Γ.env, K')
                Γ ⊢ scrut ⇒ scrutTy  ↝  scrut'
                whnf(scrutTy) = VDesc(K_scrut, Î)
                convLevel(Γ.depth, K̂, K_scrut) = true     -- K conformance
                Γ ⊢ P ⇐ VPi(_, VDesc(K̂, Î), ([], U(j)))  ↝  P'
                P̂ = eval(Γ.env, P')
                Γ ⊢ onRet ⇐ Π(j:Î). P̂(descRet j)             ↝  onRet'
                Γ ⊢ onArg ⇐ Π(S:U(K̂)). Π(T: S → Desc^K̂ Î).
                              (Π(s:S). P̂(T s)) → P̂(descArg K̂ S T)  ↝  onArg'
                Γ ⊢ onRec ⇐ Π(j:Î). Π(D':Desc^K̂ Î). P̂(D') →
                              P̂(descRec j D')                       ↝  onRec'
                Γ ⊢ onPi  ⇐ Π(S:U(K̂)). Π(f: S → Î). Π(D': S → Desc^K̂ Î).
                              (Π(s:S). P̂(D' s)) → P̂(descPi K̂ S f D')  ↝  onPi'
                Γ ⊢ onPlus ⇐ Π(A:Desc^K̂ Î). Π(B:Desc^K̂ Î).
                              P̂(A) → P̂(B) → P̂(descPlus A B)         ↝  onPlus'
                ──────────────────────
                Γ ⊢ DescElim(K, P, onRet, onArg, onRec, onPi, onPlus, scrut)
                  ⇒ vApp(P̂, eval(Γ.env, scrut'))

```

The `K conformance` check (`convLevel(K̂, K_scrut)`) is the
per-elimination verification that the eliminator's Level argument
matches the scrutinee description's level. Without it an eliminator
at `K = zero` could descend into a description containing
`descArg^1 (U 0) …`, and the case branches' sort binders (typed
`S : U(K̂) = U(0)`) would be ill-typed against the scrutinee's
actual `S : U(1)`.

#### 7.6.2 Homogeneity by typing (desc CHECK rules)

When CHECKing a description against `Desc^K I`, recursive sub-checks
inherit `K` directly from the surrounding type rather than
synthesising their own. The principle:

> A description's recursive children inhabit the same description type
> as the parent. Reconstructing `VDesc(K, Î)` per recursive call to
> thread the type — only to have the recursive CHECK pattern-match
> it back open — is wasted allocation.

The CHECK rules pass the surrounding type directly:

```
                whnf(ty) = VDesc(K, Î)
                Γ ⊢ S ⇐ VU(K)  ↝  S'    Ŝ = eval(Γ.env, S')
                Γ ⊢ T ⇐ VPi(_, Ŝ, ([], ty))  ↝  T'   -- recursive, same ty
                ──────────────────────
                Γ ⊢ DescArg(K, S, T) ⇐ ty  ↝  DescArg(K, S', T')

                whnf(ty) = VDesc(K, Î)
                Γ ⊢ S ⇐ VU(K)  ↝  S'    Ŝ = eval(Γ.env, S')
                Γ ⊢ f ⇐ VPi(_, Ŝ, ([], Î))  ↝  f'
                Γ ⊢ D ⇐ VPi(_, Ŝ, ([], ty))  ↝  D'   -- recursive, same ty
                ──────────────────────
                Γ ⊢ DescPi(K, S, f, D) ⇐ ty  ↝  DescPi(K, S', f', D')

                whnf(ty) = VDesc(K, Î)
                Γ ⊢ A ⇐ ty  ↝  A'                    -- recursive, same ty
                Γ ⊢ B ⇐ ty  ↝  B'                    -- recursive, same ty
                ──────────────────────
                Γ ⊢ DescPlus(A, B) ⇐ ty  ↝  DescPlus(A', B')

                whnf(ty) = VDesc(K, Î)
                Γ ⊢ j ⇐ Î  ↝  j'
                Γ ⊢ D ⇐ ty  ↝  D'                    -- recursive, same ty
                ──────────────────────
                Γ ⊢ DescRec(j, D) ⇐ ty  ↝  DescRec(j', D')

                whnf(ty) = VDesc(K, Î)
                Γ ⊢ j ⇐ Î  ↝  j'
                ──────────────────────
                Γ ⊢ DescRet(j) ⇐ ty  ↝  DescRet(j')

```

The `K` and `Î` are recovered once at the outermost CHECK, then
reused unchanged by every recursive sub-check. The rules' written
shape mirrors the implementation: `ty` (the surrounding `VDesc`
value) flows into recursive positions verbatim, and `convLevel` on
the inner description's level reduces to `convLevel(K, K)` — the
syntactic-equality fast-path of §6.6 fires.

#### 7.6.3 desc-con CHECK with checkDescAtAnyLevel

A `μ I D i` introduction `descCon D i d` checks the description `D`
against `Desc^K I`, where `K` is recovered from the surrounding
`μ`'s classifier. Because `μ` at indexed positions is checked
against `VMu(Î, D̂, î)` whose `D̂` field carries no externally-visible
level, the CHECK rule infers the level from the type-of-`D̂` at
elaboration:

```
                whnf(ty) = VMu(Î, D̂, î)
                checkDescAtAnyLevel(Γ, D) = (D', K)
                conv(Γ.depth, eval(Γ.env, D'), D̂) = true
                Γ ⊢ i ⇐ Î  ↝  i'
                conv(Γ.depth, eval(Γ.env, i'), î) = true
                Γ ⊢ payload ⇐ <interp(D̂, î) at level K>  ↝  payload'
                ──────────────────────
                Γ ⊢ DescCon(D, i, payload) ⇐ ty
                  ↝  DescCon(D', i', payload')

```

`checkDescAtAnyLevel(Γ, D)` is the bidirectional bridge: it
elaborates `D` at the most specific admissible level synthesised
from `D`'s structure, returning both the elaborated term and the
inferred `K`. Equivalent to `∃K. Γ ⊢ D ⇐ Desc^K Î`. The bidirectional
discipline at index positions is preserved: canonical intros (`tt`,
`zero`, `refl`, …) at the index slot remain checkable-only.

---

## 8. Universe Rules

### 8.1 Universe formation

```
U(i) : U(i + 1)                for all i ≥ 0

```

### 8.2 Type former levels

Universe levels are computed by `checkTypeLevel`, which returns
`{ term; level; }` from the **typing derivation**, not from
post-hoc value inspection. This avoids the problem of unknown
levels for neutral type variables. We write `level(A)` as shorthand
for `checkTypeLevel(Γ, A).level`.

```
checkTypeLevel(Γ, Unit)        = { Unit,    0 }
checkTypeLevel(Γ, String)      = { String,  0 }
checkTypeLevel(Γ, Int)         = { Int,     0 }
checkTypeLevel(Γ, Float)       = { Float,   0 }
checkTypeLevel(Γ, Attrs)       = { Attrs,   0 }
checkTypeLevel(Γ, Path)        = { Path,    0 }
checkTypeLevel(Γ, Function)    = { Function, 0 }
checkTypeLevel(Γ, Any)         = { Any,     0 }
checkTypeLevel(Γ, BootSum(A,B))= { BootSum(A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, Pi(n, A, B)) = { Pi(n,A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, Sigma(n,A,B))= { Sigma(n,A',B'), max(level(A), level(B)) }
checkTypeLevel(Γ, BootEq(A,a,b)) = { BootEq(A',a',b'), level(A) }
checkTypeLevel(Γ, U(i))        = { U(i),   i + 1 }
-- Fallback: infer type, require VU(i), extract i
checkTypeLevel(Γ, T)           = { T', i }  where Γ ⊢ T ⇒ VU(i)

```

The fallback handles neutral type expressions (variables,
applications) by inferring their type and requiring it to be a
universe. This correctly propagates levels through type variables:
if `B : U(1)`, then `checkTypeLevel` on `B` infers `VU(1)` and
returns level 1.

### 8.3 Cumulativity

A type `A` at level `i` is also a type at level `j` for all `j > i`.
This is implemented by accepting `conv(d, VU(i), VU(j))` when `i ≤ j`
**in the Sub rule only** (checking mode, when comparing an inferred
universe against an expected universe). The `conv` function itself
uses strict equality `i == j`.

The cumulativity check is in `check`:

```
-- In the Sub rule:
-- If inferredTy = VU(i) and expectedTy = VU(j) and i ≤ j:  accept
-- Otherwise: conv(Γ.depth, inferredTy, expectedTy) must hold

```

### 8.4 Universe consistency

The kernel MUST reject `U(i) : U(i)`. This is guaranteed by the
level computation: `level(U(i)) = i + 1`, so `U(i)` lives at level
`i + 1`, not `i`. Self-containing universes cannot be constructed.

This prevents Girard's paradox (Girard 1972), which requires a type
that contains itself. Hurkens (1995) gives the compact MLTT rendering
of the inconsistency proof. Universe stratification is the standard
fix, and it is why the kernel enforces `level(U(i)) = i + 1`.

### 8.5 Level sort

`Level` is a Tarski-style sort of universe levels, with constructors
`zero`, `suc`, and `max`. It inhabits the lowest universe:

```
                ──────────────────────
                Γ ⊢ Level type  ↝  Level

                ──────────────────────
                Γ ⊢ Level ⇒ VU(0)  ↝  Level

                ──────────────────────
                Γ ⊢ LevelZero ⇐ Level  ↝  LevelZero

                Γ ⊢ k ⇐ Level  ↝  k'
                ──────────────────────
                Γ ⊢ LevelSuc(k) ⇐ Level  ↝  LevelSuc(k')

                Γ ⊢ a ⇐ Level  ↝  a'
                Γ ⊢ b ⇐ Level  ↝  b'
                ──────────────────────
                Γ ⊢ LevelMax(a, b) ⇐ Level  ↝  LevelMax(a', b')

```

Conversion modulo the semilattice laws (idempotence of `max`, `suc`
distribution over `max`, zero absorption) is delegated to `convLevel`
(§6.6); structural conversion on Level values without normalisation
would be too coarse (e.g. `max(zero, k)` and `k` would not compare
equal).

The `Level` sort enables predicative universe polymorphism: the
description type `Desc^k I` and universe `U(k)` quantify over
arbitrary levels via `Π(k:Level). …`. Rank-1 only — `Level` itself
has no eliminator, and admitting one would break parametricity over
the semilattice quotient (any eliminator would be observably
sensitive to the canonical form chosen by `convLevel`).

---

## 9. Fuel Mechanism

### 9.1 Evaluation fuel

Every call to `evalF` receives a fuel parameter and decrements it
by one before evaluating the term. When fuel reaches 0:

```
evalF(fuel=0, ρ, t) = THROW "normalization budget exceeded"

```

The kernel aborts via `throw`. Layer 0 (TCB) has no access to the
effect system by design, so fuel exhaustion and kernel invariant
violations both manifest as Nix-level throws caught by `tryEval`.
Callers should treat any throw from the evaluator as "term not
verified" — the distinction between fuel exhaustion and a kernel bug
is in the error message text, not the failure mechanism.

### 9.2 Default budget

The default fuel budget is 10,000,000 reduction steps. This is
configurable by the caller via `evalF`. No minimum is enforced —
callers may pass arbitrarily low fuel, which will cause immediate
`throw` on the first eval step.

### 9.3 Fuel accounting

Fuel is **per-path**, not a global counter. Each call to `evalF`
captures `f = fuel - 1` and passes `f` to all sub-evaluations of
that term. When evaluating `App(t, u)`, both `evalF(f, ρ, t)` and
`evalF(f, ρ, u)` receive the same `f`. This means fuel bounds the
**depth** of any single evaluation path, not the total work across
all paths.

For a balanced binary tree of N applications, the total work is
O(2^depth × fuel), not O(fuel). This is inherent to pure Nix —
there is no mutable global counter. The fuel mechanism guarantees
termination (every path eventually hits 0) but does not bound total
computation time.

All fuel consumption flows through `evalF`:

- Direct term evaluation (each `evalF` call decrements fuel by 1)
- Beta-reduction in `vApp` consumes fuel indirectly via
  `instantiateF`, which calls `evalF`
- Iota-reduction in generated recursive eliminators consumes fuel
  through `vDescIndF`, `vAllDF`, `vEverywhereDF`, and `vAppF`

`BootJ` completes in O(1) on `BootRefl`. `BootSumElim` is
non-recursive, but branch selection calls `vAppF` on the selected
branch. Structural operations (building values, pattern matching on
tags) do not consume fuel.

### 9.4 Fuel threading in generated eliminators

Generated natural/list eliminators route through datatype-specific
wrappers and the generic `DescInd` evaluator. Deep constructor chains
are not handled by hard-coded nat/list cases: `DescCon` evaluation
recognizes homogeneous linear recursive payloads from the description
profile and flattens them into `builtins.foldl'` loops. Each fold step
threads fuel through the accumulator:

```
foldl'(λ{acc, fuel}. λi.
  if fuel ≤ 0 then THROW "normalization budget exceeded"
  else { acc = step(fuel, acc, chain[i]); fuel = fuel - 1; })
  {acc = base; fuel = fuel}
  [1..n]

```

This ensures that an N-element chain consumes N units of fuel from
the fold, plus whatever fuel each step application consumes
internally. Without this threading, each step would get the
original fuel budget, giving an effective budget of N × fuel.

The worst-case complexity of a threaded fold is O(fuel²): at step
*i*, the inner `vAppF` receives `fuel - i` as its own per-path
budget. Summing over all steps gives Σ(fuel - i) ≈ fuel²/2. To
achieve O(fuel), `vAppF` would need to return remaining fuel — an
invasive signature change. The quadratic residual is inherent to
per-path fuel semantics and is a strict improvement over the
pre-threading O(N × fuel) with unbounded N.

### 9.5 Fuel consumption in constructor chains

Generated constructor evaluation flattens chains of n `DescCon`
layers when the description's linear profile proves the recursion is
structurally homogeneous. The evaluator deducts n fuel units from the
budget before rebuilding the semantic value. Generated natural and
list constructors are instances of this generic path, so the 5000-deep
stress tests are evidence for the description-level trampoline rather
than for datatype-specific hard-coding.

---

## 10. Properties the Implementation Must Satisfy

### 10.1 Soundness (non-negotiable)

If the kernel accepts `Γ ⊢ t : A`, then `t` is a valid term of
type `A` in MLTT with the specified type formers and universe
hierarchy. Formally:

**If `check(Γ, t, A)` succeeds, then `Γ ⊢ t : A` is derivable
in the declarative typing rules of MLTT.**

Equivalently: the kernel never accepts an ill-typed term.

### 10.2 Determinism

For any input `(Γ, t, A)`, the kernel produces the same result
on every invocation. There is no randomness, no system-dependent
behavior, no sensitivity to evaluation order (beyond fuel
exhaustion, which always rejects).

### 10.3 Termination

For any input `(Γ, t, A)`, the kernel terminates. It either:
- Accepts (returns the elaborated term)
- Rejects with a type error (via effect)
- Rejects with fuel exhaustion
- Crashes with a kernel bug diagnostic (throw)

It never loops. The fuel mechanism guarantees this.

### 10.4 Evaluation roundtrip

For any well-typed term `t` and environment `ρ` consistent with
the context:

```
quote(d, eval(ρ, quote(d, eval(ρ, t)))) = quote(d, eval(ρ, t))

```

Evaluation followed by quotation is idempotent. The result is a
normal form.

### 10.5 Conversion reflexivity

For any value `v`:

```
conv(d, v, v) = true

```

### 10.6 Conversion symmetry

For any values `v₁, v₂`:

```
conv(d, v₁, v₂) = conv(d, v₂, v₁)

```

### 10.7 Conversion transitivity

For any values `v₁, v₂, v₃`:

```
conv(d, v₁, v₂) ∧ conv(d, v₂, v₃)  ⟹  conv(d, v₁, v₃)

```

### 10.8 Type preservation under evaluation

If `Γ ⊢ t : A` and `eval(Γ.env, t) = v`, then `v` represents a
value of type `A`. This is not directly testable (values don't
carry types) but is ensured by the correctness of the evaluation
rules.

### 10.9 Strong normalization (for well-typed terms)

For any well-typed term `t`, `eval` terminates without exhausting
fuel for a sufficiently large fuel budget. The fuel mechanism is
a practical safeguard, not a theoretical necessity for well-typed
terms.

---

## 11. Derived Test Cases

Every rule in this spec generates at least one positive test (the
rule applies and succeeds) and one negative test (the rule's
premises are violated and the kernel rejects).

### 11.1 Required positive tests (kernel must ACCEPT)

```
-- Public generated identity
⊢ H.refl : H.eq H.nat H.zero H.zero

-- Function type
⊢ Lam(x, H.nat, Var(0)) : Pi(x, H.nat, H.nat)

-- Application
f : Pi(x, H.nat, H.nat) ⊢ App(f, H.zero) : H.nat

-- Dependent function
⊢ Lam(A, U(0), Lam(x, Var(0), Var(0))) : Pi(A, U(0), Pi(x, A, A))

-- Sigma pair
⊢ Pair(H.zero, Tt, Sigma(x, H.nat, Unit)) : Sigma(x, H.nat, Unit)

-- Generated natural induction: 0 + 0 = 0
⊢ H.refl : H.eq H.nat (H.ind ... H.zero) H.zero

-- List
⊢ H.cons H.nat H.zero (H.nil H.nat) : H.listOf H.nat

-- Sum injection
⊢ H.inl H.nat Unit H.zero : H.sum H.nat Unit

-- Universe hierarchy
⊢ U(0) : U(1)
⊢ U(1) : U(2)
⊢ H.nat : U(0)
⊢ Pi(x, H.nat, H.nat) : U(0)

-- Let binding
⊢ Let(x, H.nat, H.zero, Var(0)) : H.nat

-- Cumulativity: H.nat : U(0) should also be accepted at U(1)

-- StrEq: type inference returns the derived H.bool
--   (= μ ⊤ (plus (retI tt) (retI tt)) tt; see §4.11)
⊢ StrEq(StringLit("a"), StringLit("b")) : H.bool

-- StrEq reduction: equal strings reduce to the derived true_ value;
-- unequal strings reduce to false_. Both witnessed via H.refl over the
-- derived-bool form. Expressing this rule at the Tm level requires
-- the plus/μ machinery; see the examples/verified-functions.nix
-- fixture `recordStrEqMatch` for an executable test.

```

### 11.2 Required negative tests (kernel must REJECT)

```
-- Type mismatch
⊢ H.zero : Unit                        REJECT

-- Universe violation
⊢ U(0) : U(0)                          REJECT

-- H.refl on unequal terms
⊢ H.refl : H.eq H.nat H.zero (H.succ H.zero)  REJECT

-- Application of non-function
⊢ App(H.zero, H.zero)                  REJECT

-- Projection of non-pair
⊢ Fst(H.zero)                          REJECT

-- Wrong eliminator scrutinee
⊢ H.ind ... Tt                         REJECT  (Tt : Unit, not H.nat)

-- Unbound variable
⊢ Var(0)  (in empty context)           REJECT

-- StrEq on non-string
⊢ StrEq(H.zero, StringLit("foo"))     REJECT  (lhs is H.nat, expected String)

-- Ill-typed pair
⊢ Pair(H.zero, H.zero, Sigma(x, H.nat, Unit))  REJECT

```

### 11.3 Required stress tests

```
-- Large H.nat: H.succ^5000(H.zero) : H.nat        ACCEPT (trampoline)
-- Large H.listOf: H.cons^5000 : H.listOf H.nat    ACCEPT (trampoline)
-- H.ind on H.succ^5000(H.zero)                    ACCEPT (trampoline)
-- H.listElim on H.cons^5000                       ACCEPT (trampoline)
-- Succ elaboration: elab-succ-5000               ACCEPT (trampoline)
-- Cons elaboration: elab-cons-5000               ACCEPT (trampoline)
-- Deeply nested Pi: Pi(x₁, ..., Pi(xₙ, H.nat, H.nat)...) for n=500  ACCEPT
-- Fuel exhaustion: artificially low fuel on complex term    REJECT (fuel)
-- Fuel threading: generated natural fold decrements fuel per step  ACCEPT
-- Fuel threading: generated list fold decrements fuel per step     ACCEPT

```

### 11.4 Required roundtrip tests

For each value form, verify:

```
quote(d, eval(ρ, t)) = normal_form(t)

```

where `normal_form(t)` is the expected normal form.

---

## 12. Notation Index

| Symbol | Meaning |
|--------|---------|
| Γ | Typing context |
| ρ | Value environment |
| d | Binding depth (for levels ↔ indices) |
| ⊢ | Typing judgment |
| ⇐ | Checking mode |
| ⇒ | Synthesis mode |
| ↝ | Elaborates to |
| ≡ | Definitional equality |
| Π | Dependent function type |
| Σ | Dependent pair type |
| ℕ | Natural numbers |
| 𝔹 | Booleans (derived: `μ ⊤ (plus (retI tt) (retI tt)) tt`) |
| ⊤ | Unit type |
| ⊥ | Void / empty type (derived: `Fin 0`) |
| U(i) | Universe at level i |
| Id_A(a,b) | Identity type |
| TCB | Trusted computing base |
| WHNF | Weak head normal form |
| NbE | Normalization by evaluation |
| THROW | Kernel invariant violation (crash) |
| REJECT | Term rejected (via effect or fuel) |

---

## 13. Known Limitations

The following are documented implementation choices or limitations,
not bugs. They are recorded here so auditors do not rediscover them.

### 13.1 Pair quotation uses dummy type annotation

`quote(d, VPair(a, b))` produces `Pair(quote(d,a), quote(d,b), Unit)`
— the type annotation is always `Unit` regardless of the actual pair
type. The `VPair` value does not carry its type (values are untyped
in NbE), so the annotation cannot be reconstructed without additional
context. Quoted pairs are structurally correct but carry a dummy
annotation.

### 13.2 Lambda domain annotations discarded in checking mode

When checking `Lam(n, A, t)` against `VPi(n, dom, cl)`, the lambda's
domain annotation `A` is discarded and replaced by `dom` from the
Pi type. This is standard bidirectional type checking (Dunfield &
Krishnaswami 2021, §4): in checking mode, the expected type provides
the domain, not the term. The elaborated output uses `quote(d, dom)`,
making the original annotation unrecoverable.

### 13.3 Term constructors do not validate argument types

Term constructors (`mkVar`, `mkApp`, etc.) accept arbitrary Nix
values without type validation. `mkVar "hello"` produces
`{ tag = "var"; idx = "hello"; }`, which crashes at eval time.
The trust boundary is the HOAS layer (`hoas.nix`), which is the
public API — direct term construction is internal to the kernel.

### 13.4 `tryEval` only catches `throw` and `assert false`

`builtins.tryEval` in the elaborator's `isConstantFamily` sentinel
detection only catches explicit `throw` and `assert false`. Nix
coercion errors (e.g., "cannot convert a function to JSON"),
missing attribute access, and type comparison errors are uncatchable.
The elaborator uses `builtins.typeOf` in error paths to avoid
triggering coercion errors.

### 13.5 HOAS sentinel comparison

The `isConstantFamily` sentinel test in the elaborator applies two
distinct sentinel values and compares the results to detect whether
a binding body is dependent. Both Pi and Sigma paths compare
**elaborated kernel terms** (`H.elab r1.value == H.elab r2.value`)
rather than raw HOAS trees. This avoids false negatives from Nix's
function identity comparison (`==` on lambdas). However, if `H.elab`
itself produces structurally different terms for semantically
equivalent types (e.g., through different elaboration paths), false
negatives remain possible. This is a safe failure mode — the kernel
still type-checks correctly, but elaboration may require explicit
`_kernel` annotations unnecessarily.

### 13.6 StrEq neutral canonicalization

When one argument to `vStrEq` is neutral and the other is a literal,
the neutral's spine is extended with `EStrEq(literal)`. When both
arguments are neutral, the **left** neutral's spine is extended with
`EStrEq(right)`. This means `StrEq(x, y)` and `StrEq(y, x)` (where
both are neutral) produce different normal forms: `VNe(x, [EStrEq(y)])`
vs `VNe(y, [EStrEq(x)])`. Therefore `conv` will report them as
**not** definitionally equal, even though `StrEq` is semantically
symmetric. This is a safe conservatism: the kernel may reject some
provable equalities but never accepts a false one.

### 13.7 Extract uses type value threading (not sentinels)

The `extract` function threads kernel type values (`tyVal`) through
recursive extraction, rather than using sentinel-based non-dependence
tests. For Pi extraction, the codomain type is computed per-invocation
via `instantiate(tyVal.closure, kernelArg)`, supporting both dependent
and non-dependent function extraction. For Sigma extraction (records),
the second component's type is computed via
`instantiate(tyVal.closure, val.fst)`. A `reifyType : Val → HoasTree`
fallback converts kernel type values back to HOAS when the HOAS body
cannot be applied (e.g., when the body accesses record fields from a
neutral). `reifyType` loses sugar (VSigma → `H.sigma`, not
`H.record`) so the HOAS body is preferred when available.

### 13.8 Spine comparison complexity

`convSp` uses `builtins.elemAt` in a fold to compare neutral spines.
In Nix, `builtins.elemAt` on lists is O(1) (Nix lists are internally
vectors/arrays), so the actual complexity is O(n), not O(n²). This
was incorrectly flagged in an earlier audit.

---

## References

1. Coquand, T. et al. (2009). *A simple type-theoretic language: Mini-TT.*
2. Dunfield, J. & Krishnaswami, N. (2021). *Bidirectional Typing.* ACM Computing Surveys.
3. Kovács, A. (2022). *Generalized Universe Hierarchies.* CSL 2022.
4. Abel, A. & Chapman, J. (2014). *Normalization by Evaluation in the Delay Monad.*
5. Girard, J.-Y. (1972). *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur.* Thèse d'État, Université Paris 7.
6. Hurkens, A. J. C. (1995). *A Simplification of Girard's Paradox.* TLCA 1995.
7. de Bruijn, N. (1972). *Lambda Calculus Notation with Nameless Dummies.*
8. Martin-Löf, P. (1984). *Intuitionistic Type Theory.* Bibliopolis.
9. Felicissimo, T. (2023). *Generic Bidirectional Typing for Dependent Type Theories.*
