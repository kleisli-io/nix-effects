# End-to-end workloads — full pipelines exercising the kernel through
# realistic surface-language constructions rather than synthetic
# microbenchmarks. Each entry forces a complete check / extract /
# eliminator-reduction pass.
{ fx }:

let
  H = fx.types.hoas;

  catApp = import ../../../examples/category-theory { inherit fx; };

  # Tests whose forcing has multi-second cost — bidirectional CHECK
  # against the polymorphic iso, full Q.nf round-trip through
  # descElim/descInd, etc. Excluded from quick-tier suite workloads
  # (which would otherwise run for >>5s) and gated separately by
  # `tc-test-suite-heavy` in the heavy tier. Keys match
  # `fx.tests.tc.results` (i.e. `<module>.<test-name>`).
  heavyProofTestNames = [
    "hoas.test-iso-type-checks-polymorphic"
    "hoas.test-iso-at-level-zero-instantiates"
    "hoas.test-iso-at-level-one-instantiates"
    "hoas.test-iso-at-level-two-instantiates"
    "hoas.test-iso-roundtrip-natDesc-k0"
    "hoas.test-iso-roundtrip-listDesc-bool-k0"
    "hoas.test-iso-roundtrip-sumDesc-nat-bool-k0"
    "hoas.test-iso-toFrom-natDesc-typechecks"
  ];

  results = fx.tests.tc.results;

  # Quick-tier-safe key set: full results minus the heavy proof tests.
  quickKeys = builtins.filter
    (k: !(builtins.elem k heavyProofTestNames))
    (builtins.attrNames results);

  # Group tc test results by source-module prefix (`module.test-name`).
  # Operates on `quickKeys` so quick-tier per-module workloads exclude
  # the heavy proof tests.
  resultsByModule =
    let
      moduleOf = k: builtins.head (builtins.split "\\." k);
      modules = builtins.foldl'
        (acc: k:
          let m = moduleOf k;
          in if builtins.elem m acc then acc else acc ++ [ m ])
        [ ]
        quickKeys;
      keysFor = m:
        builtins.filter (k: moduleOf k == m) quickKeys;
      passedAll = m:
        builtins.all
          (k: results.${k}.pass or false)
          (keysFor m);
    in
    builtins.listToAttrs (map (m: { name = m; value = passedAll m; }) modules);

in
{
  # Full tc test suite — single boolean across ~1000 inline + integration
  # tests, EXCLUDING `heavyProofTestNames`. Forces every kernel-tested
  # path covered by `src/tc/**/tests.nix` that fits the quick-tier
  # budget; the excluded heavy tests are gated by `tc-test-suite-heavy`.
  tc-test-suite-full =
    builtins.all (k: results.${k}.pass or false) quickKeys;

  # Per-module breakdown of the same suite. Each entry is a Bool over
  # the quick-tier-safe tests prefixed with `<module>.` in
  # `fx.tests.tc.results` — heavy proof tests are excluded.
  tc-test-suite-per-module = resultsByModule;

  # Heavy proof-test suite, gated separately in the heavy tier. Each
  # test is multi-second cost; aggregating them here keeps the quick
  # suite's per-workload budget intact without losing regression
  # coverage on the iso bundle.
  tc-test-suite-heavy =
    builtins.all (k: results.${k}.pass or false) heavyProofTestNames;

  # Full check of the category-theory app — 24 algebraic-law proofs
  # (`compComm`, `natAddMonoid`, `natCategory`, monoid laws, etc.),
  # each a `verifyAndExtract` invocation on a typed implementation.
  category-theory-verify = builtins.all (x: x) (builtins.attrValues catApp.tests);

  # Repeated forcing of the two named proofs from `examples/category-theory`.
  # Nix's let-binding sharing means the typecheck cost is paid once;
  # subsequent iterations re-walk the already-forced result. Useful as a
  # multi-pass forced-walk benchmark over already-elaborated proof terms.
  synthetic-large-proof =
    let
      proofs = [ catApp.tests.compComm catApp.tests.natAddMonoid ];
      force = acc: p: builtins.deepSeq p acc;
      loop = builtins.concatMap (_: proofs)
        (builtins.genList (x: x) 100);
    in
    builtins.foldl' force true loop;

  # 20-field single-constructor datatype, application of the constructor
  # checked end-to-end. Stresses macro-driven datatype elaboration plus
  # field-by-field check.
  datatype-macro-big =
    let
      fields = builtins.genList
        (i: H.field "f${toString i}" H.nat) 20;
      DT = H.datatype "Big" [ (H.con "mk" fields) ];
      args = builtins.genList (_: H.zero) 20;
      applied = builtins.foldl' (acc: a: H.app acc a) DT.mk args;
    in
    (H.checkHoas DT.T applied).tag;

  # `fzero (natLit 99) : Fin 100`. Drives the indexed-family check
  # path: elaborator builds `app fin (natLit 100)` and `fzero (natLit
  # 99)` deeply over Nat, kernel checks the constructor against the
  # indexed type.
  datatypeI-fin-deep =
    (H.checkHoas (H.app H.fin (H.natLit 100)) H.fzero).tag;

  # 100-deep nested `let` chain:
  #   let x0:Nat = 0 in let x1:Nat = 0 in ... let x99:Nat = 0 in 0.
  # Each layer exercises check.nix's `let` rule: check the annotated
  # type, check the value, extend the context, recurse into the body.
  # Stable in size (unlike test-suite workloads) and covers the let
  # rule's cost, which is not hit by any other synthetic workload.
  let-chain-100 =
    let
      body = builtins.foldl'
        (inner: i: H.let_ "x${toString i}" H.nat H.zero (_: inner))
        H.zero
        (builtins.genList (x: x) 100);
    in
    (H.checkHoas H.nat body).tag;
}
