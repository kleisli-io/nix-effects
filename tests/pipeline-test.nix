# nix-effects integration tests for pipeline framework
#
# Tests the full pipeline lifecycle through the public fx.pipeline API:
# - Multi-stage composition with reader, error, and acc effects
# - Environment access via asks
# - Error collection across stages
# - Warning accumulation across stages
{ lib, fx }:

let
  p = fx.pipeline;

  # Full pipeline: reader + error + acc across multiple stages
  fullPipelineTest = {
    expr =
      let
        discover = p.mkStage {
          name = "discover";
          transform = data:
            p.bind (p.asks (env: env.machines)) (machines:
              p.pure (data // { inherit machines; }));
        };
        validate = p.mkStage {
          name = "validate";
          transform = data:
            p.bind (p.raiseWith "validate" "missing key on host-1") (_:
              p.bind (p.warn "host-2 has deprecated config") (_:
                p.pure (data // { validated = true; })));
        };
        enrich = p.mkStage {
          name = "enrich";
          transform = data:
            p.bind (p.warn "using fallback DNS") (_:
              p.pure (data // { enriched = true; }));
        };
        result = p.run { machines = [ "host-1" "host-2" ]; } [ discover validate enrich ];
      in {
        machines = result.value.machines;
        validated = result.value.validated;
        enriched = result.value.enriched;
        errorCount = builtins.length result.errors;
        warnings = result.warnings;
      };
    expected = {
      machines = [ "host-1" "host-2" ];
      validated = true;
      enriched = true;
      errorCount = 1;
      warnings = [ "host-2 has deprecated config" "using fallback DNS" ];
    };
  };

  # Pipeline with only pure stages (no effects used)
  pureOnlyTest = {
    expr =
      let
        s1 = p.mkStage {
          name = "init";
          transform = _: p.pure { items = []; };
        };
        s2 = p.mkStage {
          name = "populate";
          transform = data: p.pure (data // { items = [ 1 2 3 ]; });
        };
        result = p.run {} [ s1 s2 ];
      in {
        value = result.value;
        noErrors = result.errors == [];
        noWarnings = result.warnings == [];
      };
    expected = {
      value = { items = [ 1 2 3 ]; };
      noErrors = true;
      noWarnings = true;
    };
  };

  allPass = fullPipelineTest.expr == fullPipelineTest.expected
            && pureOnlyTest.expr == pureOnlyTest.expected;

in {
  inherit fullPipelineTest pureOnlyTest allPass;
}
