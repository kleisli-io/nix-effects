{ fx, lib ? null, api ? fx.api, ... }:

let
  core = import ./core.nix { inherit fx lib; };
  sumsProducts = import ./sums-products.nix { inherit fx lib core; };
  recursiveLists = import ./recursive-lists.nix { inherit fx lib core; };
  refinementsDiagnostics = import ./refinements-diagnostics.nix {
    inherit fx lib core;
  };

  concatMap = f: xs: builtins.concatLists (map f xs);

  testNamesFor = suite:
    concatMap (section: section.tests or [ ])
      (suite.__example.sections or [ ]);

  boolTests = names: suite:
    builtins.listToAttrs (map
      (name: {
        inherit name;
        value = { expr = suite.${name}; expected = true; };
      })
      names);

  mkExample = suite:
    api.namespace {
      title = suite.__example.title or "";
      description = suite.__example.description or "";
      doc = suite.__example.introduction or "";
      sections = suite.__example.sections or [ ];
      value = { };
      tests = boolTests (testNamesFor suite) suite;
    };

  module = api.namespace {
    title = "Surface STLC";
    description = "Surface-language walkthroughs for a simply typed lambda calculus.";
    doc = ''
      The STLC examples build a source language incrementally over the HOAS
      checker. Each child page introduces one extension, with the full source
      available under `examples/stlc/`.
    '';
    sections = [
      {
        title = "Layered surfaces";
        prose = ''
          The core surface defines functions and application. Later examples
          import that vocabulary and extend it with products, sums, recursive
          lists, refinements, and diagnostics.
        '';
        code = ''
          core = import ./core.nix { inherit fx lib; };
          sumsProducts = import ./sums-products.nix { inherit fx lib core; };
          recursiveLists = import ./recursive-lists.nix { inherit fx lib core; };
          refinementsDiagnostics = import ./refinements-diagnostics.nix {
            inherit fx lib core;
          };
        '';
        tests = [ ];
      }
    ];
    value = {
      core = mkExample core;
      sumsProducts = mkExample sumsProducts;
      recursiveLists = mkExample recursiveLists;
      refinementsDiagnostics = mkExample refinementsDiagnostics;
    };
    tests = { };
  };

  tree = api.extractTests module;
  results = api.runTests tree;

in
{
  inherit module tree results;
  inherit core sumsProducts recursiveLists refinementsDiagnostics;
}
