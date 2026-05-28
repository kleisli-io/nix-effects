# Scalable dependency graph generators for benchmarking.
{}:

let
  sumBuilder = { deps, config }:
    builtins.foldl' (acc: v: acc + v) (config.base or 0) (builtins.attrValues deps);

  failingBuilder = msg: { deps, config }: { _error = msg; };

  leaf = name: value: {
    inherit name;
    deps = [ ];
    builder = { deps, config }: value;
  };

  failingNode = name: msg: {
    inherit name;
    deps = [ ];
    builder = failingBuilder msg;
  };

  # n0 <- n1 <- n2 <- ... <- nN (sequential, no cache hits)
  mkLinear = n:
    let
      nodes = builtins.genList
        (i:
          if i == 0 then leaf "n0" 1
          else { name = "n${toString i}"; deps = [ (builtins.elemAt nodes (i - 1)) ]; builder = sumBuilder; }
        )
        n;
    in
    { root = builtins.elemAt nodes (n - 1); config = { base = 0; }; };

  # root depends on N independent leaves (parallel, no cache hits)
  mkWide = n:
    let leaves = builtins.genList (i: leaf "leaf${toString i}" 1) n;
    in { root = { name = "root"; deps = leaves; builder = sumBuilder; }; config = { }; };

  # Diamond pattern: shared deps at each level (cache stress)
  mkDiamond = depth:
    let
      buildLevel = level: children:
        if level <= 0 then children
        else
          let
            leftNode = { name = "l${toString level}_left"; deps = children; builder = sumBuilder; };
            rightNode = { name = "l${toString level}_right"; deps = children; builder = sumBuilder; };
          in
          buildLevel (level - 1) [ leftNode rightNode ];
      topNodes = buildLevel depth [ (leaf "base" 1) ];
    in
    { root = { name = "root"; deps = topNodes; builder = sumBuilder; }; config = { }; };

  # Binary tree: each node has 2 children, no sharing (exponential, no cache benefit)
  mkBinaryTree = depth:
    let
      buildTree = d: prefix:
        if d <= 0 then leaf "${prefix}" 1
        else { name = prefix; deps = [ (buildTree (d - 1) "${prefix}_l") (buildTree (d - 1) "${prefix}_r") ]; builder = sumBuilder; };
    in
    { root = buildTree depth "root"; config = { }; };

  # Mixed: chains + wide deps
  mkMixed = { chains, chainLength, wideNodes }:
    let
      chainRoots = builtins.genList
        (c:
          let
            chainNodes = builtins.genList
              (i:
                if i == 0 then leaf "c${toString c}_n0" 1
                else { name = "c${toString c}_n${toString i}"; deps = [ (builtins.elemAt chainNodes (i - 1)) ]; builder = sumBuilder; }
              )
              chainLength;
          in
          builtins.elemAt chainNodes (chainLength - 1)
        )
        chains;
      leaves = builtins.genList (i: leaf "wide${toString i}" 1) wideNodes;
    in
    { root = { name = "combiner"; deps = chainRoots ++ leaves; builder = sumBuilder; }; config = { base = 0; }; };

  mkLinearWithFailure = n: failAt:
    let
      nodes = builtins.genList
        (i:
          if i == failAt then failingNode "n${toString i}" "intentional failure at node ${toString i}"
          else if i == 0 then leaf "n0" 1
          else { name = "n${toString i}"; deps = [ (builtins.elemAt nodes (i - 1)) ]; builder = sumBuilder; }
        )
        n;
    in
    { root = builtins.elemAt nodes (n - 1); config = { base = 0; }; };

  mkMixedWithFailures = { chains, chainLength, wideNodes, failingLeaves ? 0 }:
    let
      chainRoots = builtins.genList
        (c:
          let
            chainNodes = builtins.genList
              (i:
                if i == 0 then leaf "c${toString c}_n0" 1
                else { name = "c${toString c}_n${toString i}"; deps = [ (builtins.elemAt chainNodes (i - 1)) ]; builder = sumBuilder; }
              )
              chainLength;
          in
          builtins.elemAt chainNodes (chainLength - 1)
        )
        chains;
      goodLeaves = builtins.genList (i: leaf "wide${toString i}" 1) (wideNodes - failingLeaves);
      badLeaves = builtins.genList (i: failingNode "fail${toString i}" "leaf ${toString i} failed") failingLeaves;
    in
    { root = { name = "combiner"; deps = chainRoots ++ goodLeaves ++ badLeaves; builder = sumBuilder; }; config = { base = 0; }; };

in
{
  inherit leaf failingNode sumBuilder failingBuilder;
  inherit mkLinear mkWide mkDiamond mkBinaryTree mkMixed;
  inherit mkLinearWithFailure mkMixedWithFailures;

  benchmarks = {
    linear50 = mkLinear 50;
    linear100 = mkLinear 100;
    linear200 = mkLinear 200;
    linear500 = mkLinear 500;
    linear1000 = mkLinear 1000;

    wide50 = mkWide 50;
    wide100 = mkWide 100;
    wide200 = mkWide 200;
    wide500 = mkWide 500;
    wide1000 = mkWide 1000;

    diamond3 = mkDiamond 3;
    diamond5 = mkDiamond 5;
    diamond8 = mkDiamond 8;
    diamond10 = mkDiamond 10;
    diamond15 = mkDiamond 15;

    tree5 = mkBinaryTree 5;
    tree8 = mkBinaryTree 8;
    tree10 = mkBinaryTree 10;

    mixed_small = mkMixed { chains = 5; chainLength = 20; wideNodes = 50; };
    mixed_medium = mkMixed { chains = 10; chainLength = 50; wideNodes = 200; };
    mixed_large = mkMixed { chains = 20; chainLength = 100; wideNodes = 500; };

    linear_fail_early = mkLinearWithFailure 100 10;
    linear_fail_mid = mkLinearWithFailure 100 50;
    linear_fail_late = mkLinearWithFailure 100 90;
    mixed_with_failures = mkMixedWithFailures { chains = 5; chainLength = 20; wideNodes = 50; failingLeaves = 5; };
  };
}
