# nix-effects documentation example tests
#
# Evaluates the code blocks from book/src/getting-started.md to catch
# broken examples before users hit them.
{ lib, fx }:

let
  # -- Test 1: "Your first type" (TargetClass example) --
  targetClassExample =
    let
      inherit (fx.types) String refined;
      TargetClass = refined "TargetClass" String
        (x: builtins.elem x [ "module" "file" "package" "check" ]);
      ok = TargetClass.check "module";
      bad = TargetClass.check "fleet";
      result = fx.run (TargetClass.validate "fleet")
        fx.effects.typecheck.collecting [];
    in
      ok == true
      && bad == false
      && builtins.isList result.state
      && builtins.length result.state > 0;

  # -- Test 2: "Your first dependent type" (DepRecord + TargetClass) --
  depRecordExample =
    let
      inherit (fx.types) Bool String ListOf DepRecord refined;
      TargetClass = refined "TargetClass" String
        (x: builtins.elem x [ "module" "file" "package" "check" ]);
      AspectDecl = DepRecord [
        { name = "generated"; type = Bool; }
        { name = "target"; type = self:
            if self.generated then TargetClass else String; }
        { name = "requires"; type = _: ListOf String; }
      ];
      ok = AspectDecl.checkFlat {
        generated = true;
        target = "module";
        requires = [ "toolchain" ];
      };
      bad = AspectDecl.checkFlat {
        generated = true;
        target = "fleet";
        requires = [ ];
      };
    in
      ok == true && bad == false;

  # -- Test 3: "Your first effect" (state doubling) --
  stateEffectExample =
    let
      inherit (fx) pure bind run;
      inherit (fx.effects) get put;
      doubleState = bind get (s: bind (put (s * 2)) (_: pure s));
      result = run doubleState fx.effects.state.handler 21;
    in
      result.value == 21 && result.state == 42;

  # -- Test 4: "A first generated datatype" --
  generatedDatatypeExample =
    let
      H = fx.types.hoas;
      Aspect = H.datatype "Aspect" [
        (H.con "aspect" [
          (H.field "name" H.string)
          (H.field "target" H.string)
          (H.field "requires" (H.listOf H.string))
        ])
      ];
    in
      Aspect ? D
      && Aspect ? T
      && Aspect ? aspect
      && Aspect ? _dtypeMeta;

  # -- Test 5: Verified aspect validator --
  verifiedAspectExample =
    let
      H = fx.types.hoas;
      v = fx.types.verified;

      AspectDecl = H.record [
        { name = "name";     type = H.string; }
        { name = "target";   type = H.string; }
        { name = "requires"; type = H.listOf H.string; }
      ];

      targets =
        H.cons H.string (v.str "module")
          (H.cons H.string (v.str "file")
            (H.cons H.string (v.str "package")
              (H.cons H.string (v.str "check") (H.nil H.string))));

      validateAspect = v.verify (H.forall "a" AspectDecl (_: H.bool))
        (v.fn "a" AspectDecl (a:
          v.strElem (v.field AspectDecl "target" a) targets));
    in
      validateAspect {
        name = "workspace-shell";
        target = "module";
        requires = [ "toolchain" ];
      }
      && !(validateAspect {
        name = "workspace-aspect";
        target = "fleet";
        requires = [ ];
      });

  # -- Test 6: API surface sanity ("What's in the box") --
  apiSurfaceSanity =
    fx ? pure && fx ? bind && fx ? send && fx ? map && fx ? seq
    && fx ? run && fx ? handle
    && fx ? adapt && fx ? adaptHandlers
    && fx ? types && fx ? effects && fx ? stream;

  # -- Test 7: API docs skip semantic data inside module wrappers --
  apiDocsSkipsPlainWrapperData =
    let
      raw = fx.api.mk {
        doc = "root";
        value = rec {
          data = { inherit data; };
          child = fx.api.mk {
            doc = "child";
            value = 1;
          };
        };
      };
      docs = fx.api.extractDocs raw;
    in
      docs.doc == "root"
      && docs.child.doc == "child"
      && !(docs ? data);

in {
  inherit targetClassExample depRecordExample stateEffectExample
          generatedDatatypeExample verifiedAspectExample apiSurfaceSanity
          apiDocsSkipsPlainWrapperData;

  allPass = targetClassExample && depRecordExample && stateEffectExample
            && generatedDatatypeExample && verifiedAspectExample && apiSurfaceSanity
            && apiDocsSkipsPlainWrapperData;
}
