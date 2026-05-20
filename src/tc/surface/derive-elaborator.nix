{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  C = fx.tc.check;
  E = fx.tc.eval;
  M = fx.tc.elaborate.meta;

  applySection = ornament: term:
    if ornament == null then term
    else ornament.section term;

  checkedTypeVal = expectedType:
    let
      tyRaw = H.elab expectedType;
      tyResult = C.runCheck (C.checkTypeLevel C.emptyCtx tyRaw);
    in
    {
      result = tyResult;
      value = E.eval [ ] (if builtins.isAttrs tyResult && tyResult ? error then tyRaw else tyResult.term);
    };

  metaCheck = { surface, hoasTerm, tm, expectedType, position }:
    let
      ty = checkedTypeVal expectedType;
      hasMeta = self.containsSurfaceMeta tm || self.containsImplicitMeta tm;
      r =
        if hasMeta then
          let checked = M.runElab H.unit (M.elabCheck C.emptyCtx tm ty.value);
          in {
            result = checked.value;
            state = checked.state;
          }
        else {
          result = C.runCheck (C.check C.emptyCtx tm ty.value);
          state = null;
        };
    in
    if builtins.isAttrs ty.result && ty.result ? error
    then ty.result
    else
      self.finalizeSurfaceElab {
        result = r.result;
        state = r.state;
        term = hoasTerm;
        inherit surface position;
      };

  deriveElaborator = args:
    let
      surface = args.surface or (throw "deriveElaborator: missing surface");
      ornament = args.ornament or null;
      elaborateTerm = { term, expectedType ? null, position ? null }:
        let
          root = self.withSurfaceContext {
            term = applySection ornament term;
            inherit expectedType position;
          };
          tm =
            if expectedType == null
            then H.elab root
            else H.elaborate 0 root;
        in
        if builtins.isAttrs tm && tm ? error
        then tm
        else if expectedType == null
        then
          self.finalizeSurfaceElab
            {
              result = tm;
              term = root;
              inherit surface position;
            }
        else
          self.finalizeSurfaceElab {
            result = H.checkHoas expectedType root;
            state = null;
            term = root;
            inherit surface position;
          };
    in
    {
      inherit surface ornament;
      registry = surface.registry or self.empty;
      elaborate = elaborateTerm;
    };

  elaborate = args:
    let
      derived = deriveElaborator {
        surface = args.surface or (throw "surface.elaborate: missing surface");
        ornament = args.ornament or null;
      };
    in
    derived.elaborate {
      term = args.term or (throw "surface.elaborate: missing term");
      expectedType = args.expectedType or null;
      position = args.position or null;
    };
in
{
  scope = {
    deriveElaborator = api.leaf {
      value = deriveElaborator;
      description = "Derive an elaborator entry point from a surface specification and optional ornament section. Expected type and source position are threaded into surface handlers.";
      signature = "{ surface, ornament? } -> { registry, elaborate }";
    };
    elaborate = api.leaf {
      value = elaborate;
      description = "Elaborate one surface term, optionally checking it against an expected HOAS type and source position.";
      signature = "{ surface, term, expectedType?, position?, ornament? } -> Tm | Error";
    };
  };

  tests = { };
}
