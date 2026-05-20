# fx.tc.generic — datatype-generic reflection helpers.
#
# Public export assembly for description-backed generic programming.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.generic: datatype-generic reflection over levitated descriptions — desc/datatype/value/derive helpers plus the algebraic/functional ornaments surface.";
  doc = ''
    # fx.tc.generic — Generic Programming

    Reflection over levitated descriptions and datatype macro outputs.
    Datatype consumers should use this layer instead of raw `_dtypeMeta`.
    Generic algebraic ornament helpers check algebra descriptors against
    `generic.desc.shape`; the supported fragment is ret/arg/rec/plus.
    Ornament validation exposes total structured diagnostics for expected
    surface errors; semantic ornament maps remain pure over validated inputs.
    Functional ornaments expose manual sections for canonical
    base-to-ornamented construction; synthesis is layered on later.
    The first synthesis layer accepts `{ base; spec; synth; }`, reuses the
    ordinary ornament spec, and requires explicit builders for inserted fields.
    Proof-marked inserted fields use `prove` or `synth.constructors.<name>.proofs`
    and report unresolved proof obligations as structured diagnostics.
    Declared measures feed algebraic/measure-derived inserted fields through
    the synthesis builder context and produce missing-measure obligations.
    Function transport lifts base producers and transforms through canonical
    functional output sections while existing pullback remains forget-then-run.
  '';
  value = {
    desc = api.namespace {
      value = {
        inherit (self)
          evalDesc descView foldDesc foldDescM paraDM foldDescWithPath
          mapDesc deepEqualDesc children shape
          isRet isArg isRec isPi isPlus;
      };
      description = "desc: views and folds over levitated descriptions — `descView` peels one layer, `foldDesc` recurses, `mapDesc` rewrites, predicates split by constructor.";
      doc = ''
        # generic.desc — description views and folds

        A uniform interface to levitated descriptions
        (`Desc I k`) that hides the encoder details behind a small
        algebra of views, folds, and predicates. Every entry accepts
        either HOAS or evaluated `Val` descriptions — `evalDesc`
        normalises to `Val` idempotently.

        `descView` returns a one-step semantic view exposing the outer
        constructor as both an integer `idx` (0=ret, 1=arg, 2=rec, 3=pi,
        4=plus) and a human-readable `kind` string, alongside the
        constructor-specific fields (`I`, `k`, `j`, `sTy`, `tFn`, `sub`,
        `A`, `B`, plus optional `label`/`conLabel` sidecar metadata).

        `foldDesc` is the catamorphism: pass per-constructor handler
        functions, each receiving a record with the recursed sub-values
        already materialised. `foldDescM` is the monadic dual — each
        handler returns a `Computation R` and the combinator binds
        sub-results before invoking the matching case; `paraDM` is the
        paramorphic variant that additionally exposes the original
        sub-description `Val` at each recursive site (for callers that
        consult kernel-level shape without paying for a monadic
        descent). `foldDescWithPath` mirrors `foldDescM` and threads a
        `[fx.diag.positions]` chain extended at each descent so handlers
        can construct positionally-blamed errors directly from inside
        the fold. `mapDesc` is the structural map — handlers return
        either replacement HOAS, an explicit `{ _replaceChildren = …; }`
        payload, or a `Val` for direct substitution; identity mappers
        reconstruct definitionally-equal outputs via the canonical
        encoder chain.

        `deepEqualDesc` decides definitional equality by delegating to
        `fx.tc.conv.conv`; presentation labels (`_label`, `_conLabel`)
        are conv-irrelevant. `children`, `shape`, and the `isRet` /
        `isArg` / `isRec` / `isPi` / `isPlus` predicates round out the
        introspection surface for callers that want lightweight
        structural queries without writing a full fold.
      '';
    };

    datatype = api.namespace {
      value = {
        inherit (self)
          isDatatype normalizeMetadata datatypeInfo instantiate
          constructors fields constructorByName constructorByIx
          targetIndex fieldType fieldRole;
      };
      description = "datatype: normalise + lookup over `_dtypeMeta` — extract canonical constructor / field lists, resolve dependent field types, instantiate polymorphic parameters.";
      doc = ''
        # generic.datatype — datatype metadata canonicalisation

        Operates on the `_dtypeMeta` attrset attached to every datatype
        produced by `H.datatype` / `H.datatypeI` / `H.datatypeP`, and on
        `H.app`-spines whose head carries `_dtypeMeta` (instantiated
        polymorphic datatypes). `datatypeInfo` is the canonical entry:
        it normalises a raw meta or applies `meta.instantiate` to the
        spine args before returning a fully-defaulted record (`indexed`,
        `params`, `paramArgs`, `indexTy`, plus both `constructors` and
        the legacy `cons` alias).

        Lookup helpers stay close to caller intent: `constructors`,
        `fields`, `constructorByName`, and `constructorByIx` accept
        either pre-normalised meta or a raw `DataSpec`. Mismatched
        names and out-of-range indices throw with descriptive
        messages; nothing fails silently.

        Field-level resolution threads `prev` — the record of
        previously-materialised dependent-field values — so
        `fieldType field prev` returns the kernel HOAS type for both
        concrete fields (`field.type`) and dependent fields
        (`field.typeFn prev`). `targetIndex con prev` resolves a
        constructor's target index in the datatype's index type the
        same way. `fieldRole` exposes the optional `role` annotation
        used by generic derivations to distinguish payload from
        proof-bearing fields.
      '';
    };

    value = api.namespace {
      value = {
        inherit (self)
          view review toConstructorRecord fromConstructorRecord
          fold mapChildren;
      };
      description = "value: bidirectional views over generated datatypes — `view`/`review` swap HOAS and Nix constructor records; `fold` and `mapChildren` operate generically.";
      doc = ''
        # generic.value — value views over generated datatypes

        Two-way conversion between HOAS values and Nix
        constructor-records, plus generic structural traversal. The
        type argument accepts either an HOAS type directly or a
        datatype-output record carrying `.T`; everything else is
        normalised by `typeOf` internally.

        `view` is the HOAS-or-Nix → tagged-record direction:
        record/variant datatypes return `{ _con = "name"; …fields }`,
        primitives flatten to their native Nix form. The function is
        idempotent on values already in HOAS form. `review` is the
        inverse, kernel-elaborating a Nix value back to HOAS via
        `Elab.elaborateValue`. `toConstructorRecord` and
        `fromConstructorRecord` are intent-named aliases preferred in
        datatype-generic code.

        `fold` consumes a `{ <ctor> = Fields -> R; default? }` map and
        dispatches on `_con`; `recAt` fields are recursively folded
        before being passed in, all other fields appear raw. Missing
        constructors fall through to `cases.default constructor` or
        throw. `mapChildren` rewrites a single layer: each `recAt`
        field is replaced by `childMapper field child`; non-recursive
        fields pass through unchanged. The result is normalised by
        `view` so it round-trips with `review`.
      '';
    };

    derive = api.namespace {
      value = {
        inherit (self)
          typeDescriptor deriveDescriptor deriveSchema deriveDocs
          deriveDeps deriveFold;
      };
      description = "derive: structured artifacts from datatype metadata — type descriptors, JSON-Schema, docs scaffolds, fold scaffolds, and node-and-edge dependency graphs.";
      doc = ''
        # generic.derive — derived artifacts

        Generic, codegen-friendly summaries of a datatype's shape.
        Each helper consumes a `DataSpec` (or pre-normalised meta) and
        produces a pure-data record that downstream tooling — schema
        validators, doc renderers, codegen, dependency analysers —
        can consume without re-walking the kernel HOAS.

        `typeDescriptor` projects an arbitrary HOAS or `Val` type to
        `{ kind; … }` with a finite tag set covering primitives
        (`nat`/`bool`/`int`/`string`/`float`/`attrs`/`path`/`function`/`any`/`unit`/`universe`),
        algebraic forms (`list { elem }`, `sum { left; right }`,
        `datatype { name; args? }`), recursive sites (`recursive`),
        and unknown fallthrough (`hoas { tag }`).

        `deriveDescriptor` is the base artefact: name, constructors,
        per-field records with kind / index / level / role / source /
        proof / recursive-index / branch-index / dependent-type /
        type-descriptor. `deriveSchema` projects to
        JSON-Schema-flavoured `{ title; oneOf }`. `deriveDocs`
        re-shapes for Markdown / HTML rendering. `deriveFold` produces
        the fold-skeleton record for code generators.

        `deriveDeps` walks a constructor record, emitting a
        `{ nodes; edges }` graph that records constructor descents
        (`recAt` recursion sites), role-tagged dependency fields
        (matched against a fixed role policy), and proof-bearing
        fields. The output is consumable by the generic graph
        renderer and by build-time dependency analysers.
      '';
    };

    check = api.namespace {
      value = {
        inherit (self) deriveCheck deriveElaborate checkWithGuard;
      };
      description = "check: canonical typed walker over the HOAS algebra — one fold at two carriers (unit for validation, HOAS for elaboration), plus refinement-guard composition.";
      doc = ''
        # generic.check — canonical typed walker

        The single polymorphic fold over the full HOAS type algebra,
        parameterised by an `Algebra A`. Two canonical algebras live
        alongside it: `unitAlg` returns `null` at every node and is
        used for validation (the walker emits `typeCheck` effects on
        failure); `hoasAlg` constructs the corresponding HOAS term at
        every node and is used for elaboration. Validation and
        elaboration are not two functors — they are one fold
        instantiated at two carriers.

        `deriveCheck` and `deriveElaborate` thread `unitAlg` /
        `hoasAlg` respectively. Both accept `(ty, path, value)` and
        return a `Computation A`; the walker owns shape inspection,
        `_htag` dispatch, `fx.kernel` effect emissions, path
        threading, and the dependent-Σ snd-type derivation via an
        internal strict-handler trampoline on fst. Algebras own
        per-shape success-case construction and the field-walker (so
        `unitAlg` matches the legacy `f.type`-only traversal while
        `hoasAlg` threads `prev` through `fieldType` for
        dependent-field resolution).

        `checkWithGuard` composes `deriveCheck` with a refinement
        predicate: shape-check via the unit walker first, predicate
        second (the two cannot run in parallel — the predicate's
        domain is exactly the values that pass shape). When the
        eventual Σ-with-Decide-snd encoding lands, this special case
        collapses into `deriveCheck` over Σ-types and the helper
        deletes.

        Failure reasons carry one of `shape-mismatch`, `missing-field`,
        `extra-field`, `predicate-failed`, or `deferred-pi`, routed by
        handlers under `fx.effects.typecheck.*`.
      '';
    };

    checkD = api.namespace {
      value = {
        inherit (self) checkD checkDAt inferD inferDAt;
      };
      description = "checkD: generic bidirectional checker for Desc payloads — validates terms against `interpD level I D X i` by walking the description.";
    };

    ornaments = api.namespace {
      value = {
        inherit (self)
          ornament forget forgetHoas compose algOrn
          algSupportedFragment algShape algShapeDiagnostics checkAlgShape
          pullbackHoas liftFold pullback checkSpec
          functional validateFunctional tryFunctional diagnoseFunctional
          validateFunctionalLaws diagnoseFunctionalLaws composeFunctional
          functionalSection functionalTargetIndex
          functionalBuildIndexed functionalBuild
          liftProducerIndexed liftProducer
          liftTransformIndexed liftTransform
          validateSpec tryOrnament diagnoseSpec
          validateAlgOrn tryAlgOrn diagnoseAlgOrn
          lift;
        section = self.functionalSection;
        buildIndexed = self.functionalBuildIndexed;
        build = self.functionalBuild;
      };
      description = "ornaments: algebraic + functional ornament constructions over generated datatypes — spec validation, fold/producer/transform lifting, and forgetful maps.";
      doc = ''
        # generic.ornaments — ornament constructions

        Three families of ornament construction over kernel
        descriptions: raw structural ornaments (`ornament`,
        `compose`, `forget`, `forgetHoas`, `pullback`,
        `pullbackHoas`), algebraic ornaments derived from algebras
        over the supported fragment (`algOrn`, `algShape`,
        `algSupportedFragment`, `algShapeDiagnostics`,
        `checkAlgShape`, `liftFold`), and functional ornaments for
        lifting producers / transforms through canonical output
        sections (`functional`, `functionalSection`,
        `functionalTargetIndex`, `functionalBuildIndexed` /
        `functionalBuild`, `liftProducerIndexed` / `liftProducer`,
        `liftTransformIndexed` / `liftTransform`,
        `composeFunctional`).

        Validation is uniform across families: every constructor has
        a `validate` / `try` / `diagnose` triple
        (`validateSpec` / `tryOrnament` / `diagnoseSpec`,
        `validateAlgOrn` / `tryAlgOrn` / `diagnoseAlgOrn`,
        `validateFunctional` / `tryFunctional` / `diagnoseFunctional`,
        plus the law-level `validateFunctionalLaws` /
        `diagnoseFunctionalLaws`). `validate*` throws on rejection
        with a structured diagnostic, `try*` returns
        `{ success; value | diagnostic }`, `diagnose*` always returns
        the diagnostic record. The supported algebraic fragment is
        `[ "ret" "arg" "rec" "pi" "plus" ]`.

        Convenience aliases `section`, `targetIndex`, `buildIndexed`,
        and `build` re-export the corresponding `functional*` entries
        for callers writing in the functional-ornament idiom.
      '';
    };

    inherit (self) path;
  };
  tests = partTests;
}
