# End-to-end workloads — full pipelines exercising the kernel through
# realistic surface-language constructions rather than synthetic
# microbenchmarks. Each entry forces a complete check / extract /
# eliminator-reduction pass.
{ fx }:

let
  H = fx.types.hoas;

  catApp = import ../../../apps/category-theory { inherit fx; };

  # Group tc test results by source-module prefix (`module.test-name`).
  resultsByModule =
    let
      results = fx.tests.tc.results;
      keys = builtins.attrNames results;
      moduleOf = k: builtins.head (builtins.split "\\." k);
      modules = builtins.foldl'
        (acc: k:
          let m = moduleOf k;
          in if builtins.elem m acc then acc else acc ++ [ m ])
        [ ]
        keys;
      keysFor = m:
        builtins.filter (k: moduleOf k == m) keys;
      passedAll = m:
        builtins.all
          (k: results.${k}.pass or false)
          (keysFor m);
    in
      builtins.listToAttrs (map (m: { name = m; value = passedAll m; }) modules);

in {
  # Full tc test suite — single boolean across ~1000 inline + integration
  # tests. Forces every kernel-tested path covered by `src/tc/**/tests.nix`.
  tc-test-suite-full = fx.tests.tc.allPass;

  # Per-module breakdown of the same suite. Each entry is a Bool over
  # the tests prefixed with `<module>.` in `fx.tests.tc.results`.
  tc-test-suite-per-module = resultsByModule;

  # Full check of the category-theory app — 24 algebraic-law proofs
  # (`compComm`, `natAddMonoid`, `natCategory`, monoid laws, etc.),
  # each a `verifyAndExtract` invocation on a typed implementation.
  category-theory-verify = catApp.tests.allPass;

  # Repeated forcing of the two named proofs from `apps/category-theory`.
  # Nix's let-binding sharing means the typecheck cost is paid once;
  # subsequent iterations re-walk the already-forced result. Useful as a
  # multi-pass forced-walk benchmark over already-elaborated proof terms.
  synthetic-large-proof =
    let proofs = [ catApp.tests.compComm catApp.tests.natAddMonoid ];
        force = acc: p: builtins.deepSeq p acc;
        loop = builtins.concatMap (_: proofs)
                 (builtins.genList (x: x) 100);
    in builtins.foldl' force true loop;

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
    in (H.checkHoas DT.T applied).tag;

  # `fzero (natLit 99) : Fin 100`. Drives the indexed-family check
  # path: elaborator builds `app fin (natLit 100)` and `fzero (natLit
  # 99)` deeply over Nat, kernel checks the constructor against the
  # indexed type.
  datatypeI-fin-deep =
    (H.checkHoas (H.app H.fin (H.natLit 100)) (H.fzero (H.natLit 99))).tag;
}
