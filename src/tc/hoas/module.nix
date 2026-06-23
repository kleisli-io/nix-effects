# fx.tc.hoas — HOAS surface combinators module head.
#
# Public export assembly. `self` is the disjoint-union fixpoint of
# `combinators.nix` (core HOAS nodes + binding forms +
# descriptions + eliminator wrappers), `desc.nix` (prelude descriptions and
# descDesc encoders), `datatype.nix` (datatype macro +
# prelude instances + surface forwarders), and `lower.nix` (HOAS → Tm
# lowering + kernel-checker convenience wrappers); `partTests` is the
# aggregated test map.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.hoas: HOAS surface combinators for kernel terms — types, binders, descriptions, datatypes, ornaments, and the lowering pass that compiles to de Bruijn `Tm`.";
  doc = ''
    # fx.types.hoas — HOAS Surface Combinators

    Higher-Order Abstract Syntax layer that lets you write kernel terms
    using Nix lambdas for variable binding. The `lower` function
    compiles HOAS trees to de Bruijn indexed Tm terms.

    ## Example

    ```nix
    # Π(A:U₀). A → A
    H.forall "A" (H.u 0) (A: H.forall "x" A (_: A))
    ```

    ## Type Combinators

    - `nat`, `bool`, `unit`, `void` — base types
    - `string`, `int_`, `float_`, `attrs`, `path`, `derivation`, `function_`, `any` — primitive types
    - `thunk` (parametric: `thunk : Hoas -> Hoas`) — generic deepSeq-safe carrier
    - `listOf : Hoas → Hoas` — List(elem)
    - `sum : Hoas → Hoas → Hoas` — Sum(left, right)
    - `eq : Hoas → Hoas → Hoas → Hoas` — generated EqDT(type, lhs, rhs)
    - `u : Int → Hoas` — Universe at level
    - `forall : String → Hoas → (Hoas → Hoas) → Hoas` — Π-type (Nix lambda for body)
    - `sigma : String → Hoas → (Hoas → Hoas) → Hoas` — Σ-type

    ## Compound Types (Sugar)

    - `record : [{ name; type; }] → Hoas` — nested Sigma (sorted fields)
    - `maybe : Hoas → Hoas` — Sum(inner, Unit)
    - `variant : [{ tag; type; }] → Hoas` — nested Sum (sorted tags)
    - `product : String → [Field] → DataSpec` — named single-constructor μ-datatype

    ## Term Combinators

    - `lam : String → Hoas → (Hoas → Hoas) → Hoas` — λ-abstraction
    - `let_ : String → Hoas → Hoas → (Hoas → Hoas) → Hoas` — let binding
    - `zero`, `succ`, `true_`, `false_`, `tt`, `refl` — intro forms; `refl` is check-mode only
    - `nil`, `cons`, `pair`, `inl`, `inr` — data constructors
    - `stringLit`, `intLit`, `floatLit`, `attrsLit`, `pathLit`, `derivationLit`, `fnLit`, `anyLit` — primitive literals
    - `absurd`, `ann`, `app`, `fst_`, `snd_` — elimination/annotation

    ## Eliminators

    - `ind` — generated natural eliminator adapter
    - `boolElim` — (k : Level) → (Q : bool → U(k)) → Q true_ → Q false_ → (b : bool) → Q b
    - `listElim` — generated list eliminator adapter
    - `sumElim` — generated sum eliminator adapter
    - `j` — EqDT eliminator adapter with J-shaped arguments

    ## Ornaments

    - `ornI`, `ornDesc`, `ornForget` — first-class ornaments compiled to existing `Desc`, `mu`, and `descInd` programs; ornaments are not kernel primitives
    - `ornPullback`, `ornLiftFold` — transport base programs to ornamented datatypes by composing with `ornForget`
    - `ornLiftProducer`, `ornLiftTransform` — lift base producers/transforms through functional ornament output sections
    - `algOrn` — algebraic ornament builder for `descRet`/`descArg`/`descRec`/keep-only `descPi`/`descPlus`, generating an ornament indexed by an algebra result
    - `functionalOrnament`, `ornBuild` — manual sections of `ornForget` for explicit base-to-ornamented construction
    - `validateFunctionalLaws`, `functionalCompose` — law metadata checks and composition for sectioned ornaments
    - `validateOrnament`, `tryOrnament`, `validateAlgOrn`, `tryAlgOrn` — total structured diagnostics for user-facing ornament construction

    ## Lowering

    - `lower : Int → Hoas → Tm` — compile at given depth
    - `elab : Hoas → Tm` — compile from depth 0

    ## Convenience

    - `checkHoas : Hoas → Hoas → Tm|Error` — elaborate type+term, type-check
    - `inferHoas : Hoas → { term; type; }|Error` — elaborate and infer
    - `natLit : Int → Hoas` — build S^n(zero)

    ## Stack Safety

    Binding chains (pi/lam/sigma/let), succ chains, and cons chains
    are elaborated iteratively via `genericClosure` — safe to 8000+ depth.
  '';
  value = {
    inherit (self)
      False True WDT absurd absurdFin0 absurdPrim algArg algOrn algOrnDiagnosticRecords
      algOrnDiagnostics algPiKeep algPlus algRec algRet allD and ann any
      annTrusted anyLit app attrs attrsLit bool boolDesc boolElim canonApp checkFunctionalLaws
      checkHoas con conI cong congSuc cons datatype datatypeI datatypeP datatypePI
      dec decAnd decElim decNot decOr decideEqIntZ decideEqNat decideLeIntZ
      decideLeNat derivation derivationLit
      desc descArg descCon descDesc descElim descInd descCataBool descPi descRec descRet
      elab elab2 embedTm eq eqCongSucc eqDT eqDTToEq eqDesc eqInjSucc
      eqIsoBwd eqIsoFwd eqRefutSuccZero eqRefutZeroSucc eqToEqDT everywhereD
      false_ field fieldD fin finDesc finElim floatLit float_ fnLit forall
      implicitApp implicitForall implicitLam plicity surfacePlicity
      fst_ fsuc function_ functionalCompose functionalLawDiagnosticRecords
      functionalLawDiagnostics functionalOrnament
      functionalOrnamentDiagnosticRecords functionalOrnamentDiagnostics fzero
      iff ind inferHoas inl inr intEq intLe intLit int_ interpD intz intzDecode intzDesc
      intzElim intzLe intzLit intzNegSucc intzNegSuccCong intzNegSuccInjective
      intzPos intzPosCong intzPosInjective isLeafOrn j just lam le leDesc leElim leInjSS
      leRefutSuccZero leSS leZ leafOrnament leafOrnamentDiagnosticRecords
      leafOrnamentDiagnostics let_ level levelMax levelSuc levelZero listDesc
      listElim listOf litVal lower maxSucDom maybe mu nat natCaseU natDesc natLit
      natPredCase natToLevel nil no nothing not opaqueLam or_ ornArgInsert ornArgKeep
      ornBuild ornCompose ornDesc ornForget ornI ornId ornIndexProof
      ornLiftFold ornLiftProducer ornLiftTransform ornMu ornPiKeep ornPlus
      ornPullback ornRec ornRet ornSection ornTargetIndex ornament
      empty
      ornamentDiagnosticRecords ornamentDiagnostics pair path pathLit piField
      piFieldD plus predNat product recField recFieldAt record refinementPred
      refl reflDT reifyLevel retI sigma signsDiffer signsDifferRev snd_
      sourceMapOf squash squashElim squashIntro strEq string stringLit succ
      sum sumDesc sumElim sup thunk thunkOrnament trans true_ tryAlgOrn
      tryFunctionalOrnament tryLeafOrnament tryOrnament tt u unit validateAlgOrn
      validateFunctionalLaws validateFunctionalOrnament validateLeafOrnament
      validateOrnament variant variantInject vcons vec vecDesc
      vecElim vhead vnil void vtail w wDesc wElim withConLabel withDescLabel
      yes zero;

    # Unstable internal surface — reachable cross-module but not part of the
    # end-user API. Three reasons a binding lives here rather than at the
    # public top-level:
    #   - Low-level bootstrap (boot-sum / boot-eq) used by description-
    #     machinery consumers (e.g. `experimental/desc-interp`) because the
    #     freer-monad-as-description encoding constructs μ-values at the raw
    #     description layer where no SumDT/EqDT-generated form applies.
    #   - Kernel-Tm encoders (`encodeDescX` / `descDescTm` / `descDescVal` /
    #     `natDescTm` / `__descDesc`) — Tm/Val-level forms paired with their
    #     surface combinators; consumed only by `tc/eval`, `tc/generic`, and
    #     the kernel adapter glue. End-users write the surface forms.
    #   - Indexed/equality-aligned variants of public surface combinators
    #     (`*At` / `*AtWithEq` / `*I` / `*IAt` / `*IWithEq`) used internally
    #     by ornament construction, levitated-description indexing, and
    #     evaluator test fixtures. End-users write the non-indexed form
    #     unless they're authoring genuinely indexed datatypes (in which
    #     case `H.datatypeI` / `H.conI` / `H.recFieldAt` / `H.piFieldAtIndex`
    #     remain at the public surface).
    # Consumers reach these via `fx.tc.hoas._internal.<binding>` (boot*),
    # `fx.tc.hoas._internal._encoders.<binding>` (Tm/Val encoders), or
    # `fx.tc.hoas._internal._indexed.<binding>` (indexed-variant scaffolding),
    # opting in explicitly at the call site.
    _internal = api.namespace {
      description = "Unstable internal surface — boot-sum/boot-eq helpers, kernel-Tm encoders, and indexed-variant scaffolding; prefer SumDT/EqDT-generated forms in user code.";
      value = {
        inherit (self) bootEq bootRefl bootJ bootSum bootInl bootInr bootSumElim;
        _encoders = api.namespace {
          description = "Kernel-Tm and Val-level encoders for surface description combinators; consumed by `tc/eval` (descDescVal) and `tc/generic` (encodeDescXTm pre-evaluations).";
          value = {
            inherit (self)
              __descDesc descDescApp descDescAppAtI descDescTm descDescVal encodeDescArg
              encodeDescArgAt encodeDescArgAtTm encodeDescArgTm encodeDescElim
              encodeDescElimTm encodeDescElimVal encodeDescPi encodeDescPiAt
              encodeDescPiAtTm encodeDescPiTm encodeDescPlus encodeDescPlusTm
              encodeDescRec encodeDescRecTm encodeDescRet encodeDescRetTm
              natDescTm;
          };
        };
        _indexed = api.namespace {
          description = "Indexed/equality-aligned combinators (`muI`, `piI`, `recI`, `plusI`, `inrAt`, `fieldAt`) consumed by ornament construction and indexed-datatype test fixtures.";
          value = {
            inherit (self)
              datatypeAt datatypePAt descArgAt descArgWithEq descAt descI
              descIAt descIAtI descIAtAtI descPiAt descPiWithEq descArgAtI descArgAtAtI
              fieldAt fieldAtWithEq fieldDAt
              fieldDAtWithEq inlAt inlAtExplicit inrAt inrAtExplicit liftAt LiftAt liftAtWithEq
              LiftAtWithEq lowerAt lowerAtWithEq muI muIAtI piFieldAt piFieldAtIndex
              nilAtExplicit consAtExplicit
              piFieldAtIndexWithEq piFieldAtWithEq piFieldDAt piFieldDAtIndex
              piFieldDAtIndexWithEq piFieldDAtWithEq piI piIAt piIAtI
              piIAtAtI piIWithEq plusI plusIAtI recI recIAtI retIAtI
              sumAt sumElimAt;
          };
        };
        _forced = api.namespace {
          description = "Forced-argument analysis helpers for datatype constructors; consumed by datatype elaboration and tests that inspect recoverable constructor fields.";
          value = {
            inherit (self) forcedFieldNames forcedFieldSet isFieldForced mentionsOf;
          };
        };
      };
    };
  };
  tests = partTests;
}
