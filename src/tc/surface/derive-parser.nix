{ api, ... }:

let
  deriveParser = args:
    let
      surface = args.surface or (throw "deriveParser: missing surface");
      suppliedParse = args.parse or null;
      parseInput = if suppliedParse != null then suppliedParse else
      (input:
        if builtins.isAttrs input then input
        else throw "surface.parse: parser function required for non-AST input");
    in
    {
      inherit surface;
      parse = parseInput;
    };

  parse = args:
    (deriveParser {
      surface = args.surface or (throw "surface.parse: missing surface");
      parse = args.parse or null;
    }).parse (args.input or (throw "surface.parse: missing input"));
in
{
  scope = {
    deriveParser = api.leaf {
      value = deriveParser;
      description = "Derive a parser shell for a surface specification.";
      signature = "{ surface, parse? } -> { parse }";
    };
    parse = api.leaf {
      value = parse;
      description = "Parse one input value with a derived parser shell or supplied parser.";
      signature = "{ surface, input, parse? } -> Hoas";
    };
  };

  tests = { };
}
