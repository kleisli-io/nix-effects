# Expression language interpreter using nix-effects.
# Supports: arithmetic, booleans, let bindings, lambdas, application.
# Recursive bindings work via Nix's lazy evaluation.
{ fx }:

let
  inherit (fx) pure bind send handle;

  # Expression constructors
  num = n: { _tag = "Expr"; _variant = "Num"; inherit n; };
  bool = b: { _tag = "Expr"; _variant = "Bool"; inherit b; };
  var = name: { _tag = "Expr"; _variant = "Var"; inherit name; };
  add = l: r: { _tag = "Expr"; _variant = "Add"; inherit l r; };
  mul = l: r: { _tag = "Expr"; _variant = "Mul"; inherit l r; };
  sub = l: r: { _tag = "Expr"; _variant = "Sub"; inherit l r; };
  lt = l: r: { _tag = "Expr"; _variant = "Lt"; inherit l r; };
  eq = l: r: { _tag = "Expr"; _variant = "Eq"; inherit l r; };
  if_ = cond: then_: else_: { _tag = "Expr"; _variant = "If"; inherit cond then_ else_; };
  let_ = name: val: body: { _tag = "Expr"; _variant = "Let"; inherit name val body; };
  lam = param: body: { _tag = "Expr"; _variant = "Lam"; inherit param body; };
  app = fn: arg: { _tag = "Expr"; _variant = "App"; inherit fn arg; };

  # Value constructors
  VNum = n: { _tag = "Value"; _variant = "VNum"; inherit n; };
  VBool = b: { _tag = "Value"; _variant = "VBool"; inherit b; };
  VClosure = param: body: env: { _tag = "Value"; _variant = "VClosure"; inherit param body env; };

  # Effects
  lookup = name: send "lookup" name;
  getEnv = send "getEnv" null;
  fail = msg: send "fail" msg;

  eval = expr:
    if expr._variant == "Num" then pure (VNum expr.n)
    else if expr._variant == "Bool" then pure (VBool expr.b)
    else if expr._variant == "Var" then
      bind (lookup expr.name)
        (v:
          if v == null then fail "undefined: ${expr.name}"
          else pure v)
    else if expr._variant == "Add" then
      bind (eval expr.l)
        (l: bind (eval expr.r) (r:
          if l._variant == "VNum" && r._variant == "VNum"
          then pure (VNum (l.n + r.n))
          else fail "type error: Add expects numbers"))
    else if expr._variant == "Sub" then
      bind (eval expr.l)
        (l: bind (eval expr.r) (r:
          if l._variant == "VNum" && r._variant == "VNum"
          then pure (VNum (l.n - r.n))
          else fail "type error: Sub expects numbers"))
    else if expr._variant == "Mul" then
      bind (eval expr.l)
        (l: bind (eval expr.r) (r:
          if l._variant == "VNum" && r._variant == "VNum"
          then pure (VNum (l.n * r.n))
          else fail "type error: Mul expects numbers"))
    else if expr._variant == "Lt" then
      bind (eval expr.l)
        (l: bind (eval expr.r) (r:
          if l._variant == "VNum" && r._variant == "VNum"
          then pure (VBool (l.n < r.n))
          else fail "type error: Lt expects numbers"))
    else if expr._variant == "Eq" then
      bind (eval expr.l)
        (l: bind (eval expr.r) (r:
          if l._variant == "VNum" && r._variant == "VNum"
          then pure (VBool (l.n == r.n))
          else if l._variant == "VBool" && r._variant == "VBool"
          then pure (VBool (l.b == r.b))
          else fail "type error: Eq expects matching types"))
    else if expr._variant == "If" then
      bind (eval expr.cond)
        (c:
          if c._variant == "VBool"
          then if c.b then eval expr.then_ else eval expr.else_
          else fail "type error: If expects boolean")
    else if expr._variant == "Lam" then
      bind (getEnv) (env: pure (VClosure expr.param expr.body env))
    else if expr._variant == "Let" then
      bind (getEnv)
        (env:
          # For lambdas, construct closure directly to avoid deepSeq forcing recursive ref
          if expr.val._variant == "Lam" then
            let
              extendedEnv = env // { ${expr.name} = closure; };
              closure = VClosure expr.val.param expr.val.body extendedEnv;
            in
            send "local" { env = extendedEnv; comp = eval expr.body; }
          else
          # Non-lambda: evaluate value first, then bind
            bind (eval expr.val) (val:
              send "local" { env = env // { ${expr.name} = val; }; comp = eval expr.body; }))
    else if expr._variant == "App" then
      bind (eval expr.fn)
        (fn: bind (eval expr.arg) (arg:
          if fn._variant == "VClosure"
          then send "local" { env = fn.env // { ${fn.param} = arg; }; comp = eval fn.body; }
          else fail "type error: App expects function"))
    else fail "unknown variant: ${expr._variant}";

  mkHandler = env: {
    lookup = { param, state }: { resume = state.env.${param} or null; inherit state; };
    getEnv = { param, state }: { resume = state.env; inherit state; };
    local = { param, state }:
      let result = handle { handlers = mkHandler param.env; state = { env = param.env; }; } param.comp;
      in if result ? error then { abort = result; inherit state; }
      else { resume = result.value; inherit state; };
    fail = { param, state }: { abort = { error = param; }; inherit state; };
  };

  run = expr:
    let result = handle { handlers = mkHandler { }; state = { env = { }; }; } (eval expr);
    in if result ? error then throw "eval error: ${result.error}" else result.value;

  lang = { inherit num bool var add mul sub lt eq if_ let_ lam app; };

in
rec {
  __example = {
    title = "Expression Interpreter";
    description = "A small expression language interpreted with lookup, scoped environment, and failure effects.";
    introduction = ''
      This example implements a strict expression language with arithmetic,
      booleans, let bindings, lambdas, application, and recursive bindings.
      The evaluator emits effects for environment lookup, local scope, and
      failure; handlers decide how those requests run.

      The same module also exports scalable expression generators used by the
      benchmark suite.
    '';
    sections = [
      {
        title = "Expression syntax";
        prose = ''
          Expressions are plain tagged Nix attrsets. Constructors keep the
          evaluator independent from any parser or source format.
        '';
        code = ''
          num = n: { _tag = "Expr"; _variant = "Num"; inherit n; };
          add = l: r: { _tag = "Expr"; _variant = "Add"; inherit l r; };
          lam = param: body: { _tag = "Expr"; _variant = "Lam"; inherit param body; };
          app = fn: arg: { _tag = "Expr"; _variant = "App"; inherit fn arg; };
        '';
        tests = [
          "arithmeticComputes"
          "lambdaApplicationComputes"
        ];
      }
      {
        title = "Handler boundary";
        prose = ''
          Variable lookup, scoped execution, and failure are effects. Recursive
          bindings work by building a closure whose environment refers back to
          itself, while the handler owns the actual environment map.
        '';
        code = ''
          lookup = name: send "lookup" name;
          getEnv = send "getEnv" null;
          fail = msg: send "fail" msg;

          run = expr:
            let result = handle {
              handlers = mkHandler { };
              state = { env = { }; };
            } (eval expr);
            in if result ? error then throw "eval error: ''${result.error}" else result.value;
        '';
        tests = [
          "recursiveFibComputes"
          "nestedLetsCompute"
        ];
      }
      {
        title = "Benchmark generators";
        prose = ''
          `exprs.nix` generates large recursive and nested expressions. The
          benchmark suite imports these generators from `examples/interp`.
        '';
        code = ''
          interp.exprs.benchmarks.fib10
          interp.exprs.benchmarks.lets500
          interp.exprs.benchmarks.sum1000
        '';
        tests = [ ];
      }
    ];
  };

  inherit eval run lang;
  inherit num bool var add mul sub lt eq if_ let_ lam app;
  inherit VNum VBool VClosure;
  exprs = import ./exprs.nix lang;

  arithmeticComputes =
    run (add (num 2) (mul (num 3) (num 4))) == VNum 14;

  lambdaApplicationComputes =
    run (app (lam "x" (add (var "x") (num 1))) (num 41)) == VNum 42;

  recursiveFibComputes =
    run exprs.benchmarks.fib10 == VNum 55;

  nestedLetsCompute =
    run (exprs.mkNestedLets 10) == VNum 9;
}
