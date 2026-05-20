{ api, ... }:

let
  derivePrinter = args:
    let
      surface = args.surface or (throw "derivePrinter: missing surface");
      render = args.render or null;
      go = term:
        if render != null then render go term
        else if builtins.isAttrs term && term ? _surface && term ? _constructor
        then "${term._surface}.${term._constructor}"
        else if builtins.isAttrs term && term ? _htag
        then term._htag
        else "<value>";
    in
    {
      inherit surface;
      print = go;
    };

  print = args:
    (derivePrinter {
      surface = args.surface or (throw "surface.print: missing surface");
      render = args.render or null;
    }).print (args.term or (throw "surface.print: missing term"));
in
{
  scope = {
    derivePrinter = api.leaf {
      value = derivePrinter;
      description = "Derive a small printer for surface AST nodes.";
      signature = "{ surface, render? } -> { print }";
    };
    print = api.leaf {
      value = print;
      description = "Print one surface AST node with a derived or supplied renderer.";
      signature = "{ surface, term, render? } -> String";
    };
  };

  tests = { };
}
