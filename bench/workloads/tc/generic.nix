# Generic datatype workloads.
#
# These cover metadata normalization, constructor-record view/review,
# derivation artifacts, and a synthetic builder chain that mirrors a
# CoreBuilder -> CodeGenBuilder -> IdlBuilder dependency stack.
{ fx }:

let
  H = fx.types.hoas;
  G = fx.types.generic;

  Tree = H.datatypeP "BenchTree" [{ name = "A"; kind = H.u 0; }] (ps:
    let A = builtins.elemAt ps 0; in [
      (H.con "leaf" [ (H.field "value" A) ])
      (H.con "node" [ (H.recField "left") (H.recField "right") ])
    ]);
  TreeNat = H.app Tree.T H.nat;
  treeRecord = {
    _con = "node";
    left = { _con = "leaf"; value = 0; };
    right = { _con = "leaf"; value = 1; };
  };

  CoreBuilder = H.datatype "BenchCoreBuilder" [
    (H.con "builder" [
      ((H.field "name" H.nat) // {
        role = "dependency";
        source = { path = "builder.name"; };
      })
      (H.field "actionCount" H.nat)
    ])
  ];

  CodeGenBuilder = H.ornament CoreBuilder {
    name = "BenchCodeGenBuilder";
    constructors.builder.fields = [
      { insert = "language"; type = H.nat; }
      { keep = "name"; }
      { keep = "actionCount"; }
    ];
  };

  IdlBuilder = H.ornament CodeGenBuilder {
    name = "BenchIdlBuilder";
    constructors.builder.fields = [
      { insert = "idlVersion"; type = H.nat; }
      { keep = "language"; }
      { keep = "name"; }
      { keep = "actionCount"; }
    ];
  };

  FunctionalCodeGenBuilder = G.ornaments.functional {
    base = CoreBuilder;
    spec = {
      name = "BenchFunctionalCodeGenBuilder";
      constructors.builder.fields = [
        { insert = "language"; type = H.nat; }
        { keep = "name"; }
        { keep = "actionCount"; }
      ];
    };
    synth.constructors.builder.fields.language = _ctx: 2;
  };

  FunctionalIdlBuilder = G.ornaments.functional {
    base = FunctionalCodeGenBuilder.meta.ornamented;
    spec = {
      name = "BenchFunctionalIdlBuilder";
      constructors.builder.fields = [
        { insert = "idlVersion"; type = H.nat; }
        { keep = "language"; }
        { keep = "name"; }
        { keep = "actionCount"; }
      ];
    };
    synth.constructors.builder.fields.idlVersion = _ctx: 1;
  };

  FunctionalIdlChain =
    G.ornaments.composeFunctional FunctionalIdlBuilder FunctionalCodeGenBuilder;

  baseCoreRecord = {
    _con = "builder";
    name = 3;
    actionCount = 5;
  };

  idlRecord = {
    _con = "builder";
    idlVersion = 1;
    language = 2;
    name = 3;
    actionCount = 5;
  };

  idlHoas = G.value.review IdlBuilder.T idlRecord;
  codeHoas = G.ornaments.forget IdlBuilder idlHoas;
  codeRecord = G.value.view CodeGenBuilder.T codeHoas;
  coreHoas = G.ornaments.forget CodeGenBuilder codeHoas;
  coreRecord = G.value.view CoreBuilder.T coreHoas;

  functionalCoreHoas = G.value.review CoreBuilder.T baseCoreRecord;
  functionalCodeHoas =
    G.ornaments.build FunctionalCodeGenBuilder functionalCoreHoas;
  functionalCodeRecord =
    G.value.view FunctionalCodeGenBuilder.meta.ornamented.T functionalCodeHoas;
  functionalIdlHoas =
    G.ornaments.build FunctionalIdlChain functionalCoreHoas;
  functionalIdlRecord =
    G.value.view FunctionalIdlBuilder.meta.ornamented.T functionalIdlHoas;
  functionalForgotCoreRecord =
    G.value.view CoreBuilder.T
      (G.ornaments.forget FunctionalIdlChain functionalIdlHoas);
  functionalProducer =
    H.ann
      (H.lam "builder" CoreBuilder.T (_:
        G.value.review CoreBuilder.T {
          _con = "builder";
          name = 8;
          actionCount = 13;
        }))
      (H.forall "_" CoreBuilder.T (_: CoreBuilder.T));
  functionalLiftedHoas =
    G.ornaments.liftProducer
      FunctionalIdlChain
      functionalProducer
      functionalCoreHoas;
  functionalLiftedRecord =
    G.value.view FunctionalIdlBuilder.meta.ornamented.T functionalLiftedHoas;
  functionalLiftedForgotCoreRecord =
    G.value.view CoreBuilder.T
      (G.ornaments.forget FunctionalIdlChain functionalLiftedHoas);
  functionalMissingLanguage =
    G.ornaments.validateFunctional {
      base = CoreBuilder;
      spec = {
        name = "BenchFunctionalMissingCodeGenBuilder";
        constructors.builder.fields = [
          { insert = "language"; type = H.nat; }
          { keep = "name"; }
          { keep = "actionCount"; }
        ];
      };
      synth = {};
    };

in {
  metadata-normalize =
    let info = G.datatype.datatypeInfo TreeNat;
    in builtins.length info.constructors;

  view-review =
    G.value.view TreeNat (G.value.review TreeNat treeRecord);

  derive-descriptor =
    builtins.length (G.derive.deriveDescriptor TreeNat).constructors;

  derive-schema =
    builtins.length (G.derive.deriveSchema TreeNat).oneOf;

  derive-deps =
    let graph = G.derive.deriveDeps TreeNat treeRecord;
    in {
      nodes = builtins.length graph.nodes;
      edges = builtins.length graph.edges;
      rootPath = graph.rootPath;
    };

  synthetic-builder-chain = {
    idlFields =
      builtins.length
        (builtins.head (G.derive.deriveDescriptor IdlBuilder).constructors).fields;
    codeFields =
      builtins.length
        (builtins.head (G.derive.deriveDescriptor CodeGenBuilder).constructors).fields;
    coreFields =
      builtins.length
        (builtins.head (G.derive.deriveDescriptor CoreBuilder).constructors).fields;
    codeRecord = codeRecord;
    coreRecord = coreRecord;
    schemas = {
      idl = builtins.length (G.derive.deriveSchema IdlBuilder).oneOf;
      code = builtins.length (G.derive.deriveSchema CodeGenBuilder).oneOf;
      core = builtins.length (G.derive.deriveSchema CoreBuilder).oneOf;
    };
    deps = {
      idl = {
        nodes = builtins.length (G.derive.deriveDeps IdlBuilder idlRecord).nodes;
        edges = builtins.length (G.derive.deriveDeps IdlBuilder idlRecord).edges;
      };
      code = {
        nodes = builtins.length (G.derive.deriveDeps CodeGenBuilder codeRecord).nodes;
        edges = builtins.length (G.derive.deriveDeps CodeGenBuilder codeRecord).edges;
      };
      core = {
        nodes = builtins.length (G.derive.deriveDeps CoreBuilder coreRecord).nodes;
        edges = builtins.length (G.derive.deriveDeps CoreBuilder coreRecord).edges;
      };
    };
  };

  functional-builder-chain = {
    codeRecord = functionalCodeRecord;
    idlRecord = functionalIdlRecord;
    forgotCoreRecord = functionalForgotCoreRecord;
    liftedRecord = functionalLiftedRecord;
    liftedForgotCoreRecord = functionalLiftedForgotCoreRecord;
    checks = {
      forget = functionalForgotCoreRecord == baseCoreRecord;
      liftedForget =
        functionalLiftedForgotCoreRecord == {
          _con = "builder";
          name = 8;
          actionCount = 13;
        };
    };
    diagnostics = {
      count = builtins.length functionalMissingLanguage.diagnostics;
      first = {
        inherit ((builtins.head functionalMissingLanguage.diagnostics))
          code path message;
      };
    };
  };
}
