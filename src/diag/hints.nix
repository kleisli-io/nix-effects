# Hint resolver for diagnostic Errors.
#
# Pairs a suffix of the blame path with a Detail-classified pattern
# and maps it to a structured Hint record. Keys are position-first;
# no kernel-rule strings appear as keys or in hint text, so rule
# retirement never invalidates hints.
#
# Lookup:
#
#   resolve : Error -> Hint | null
#
# Walks the single-child chain from the given Error to the leaf,
# classifies the leaf's Detail pattern, and returns the hint
# registered under the *longest* matching leaf-anchored suffix of
# the path's position tags. Returns null when no entry matches or
# when the Error lacks a position (unwrapped leaf).
#
# Key syntax: `"<pos1>.<pos2>...<posN>::<pattern>"`. The N position
# tags must match the last N elements of the blame path, in order.
# Longest matching suffix wins; existing 1-position keys continue to
# work as tail-of-length-1 matches.
#
# A Hint is `{ _tag = "Hint"; text; category; severity; docLink; }`.
# The `_tag` keeps it terminal for `api.extractValue`; all other
# fields are plain data consumable by renderers, LSPs, docs, and
# linters. Severity is `"error"` at this layer. `docLink` resolves
# to a dedicated per-key page on `docs.kleisli.io` of the form
# `/nix-effects/diag-hints/<slug>`; the slug matches the docs-site
# markdown renderer's slug for the key, so one fetch lands an agent
# on focused, single-key content.
#
# Chain walking is stack-safe by construction: direct recursion up to
# `fastPathLimit` frames, then a `builtins.genericClosure` worklist
# that WHNF-forces the next Error node at each step. `deepSeq` is
# unsafe on recursive Error payloads; WHNF suffices because each step
# only reads `err.children` (one hop).
{ lib, fx, api, ... }:
let
  fastPathLimit = 500;

  # Base URL of the per-key Hint pages on the public docs hub. Each
  # Hint key gets its own page at `${docBase}/${slugify key}`; the
  # corresponding `.md` file is emitted by
  # `book/gen/docs-content.nix:diagHintsEntries` and is exposed as a
  # per-key resource by any external consumer that scans the layout.
  # Slug rule matches the heading-id slugifier of the rendering hub so
  # the URL path segment also serves as an in-page anchor on overview
  # pages that reference the key.
  docBase = "https://docs.kleisli.io/nix-effects/diag-hints";

  # Slugify a hint key the same way kleisli-content's markdown renderer
  # slugifies heading text: lowercase, then replace any character not in
  # [a-z0-9-] with `-`, then collapse consecutive dashes. We avoid the
  # generic char-loop (slow under Nix) by using a fixed replacement
  # table covering the alphabet that actually appears in Hint keys
  # (alnum plus `:`, `.`, `_`, ` `).
  slugify = text:
    let
      lowered = lib.toLower text;
      replaced = builtins.replaceStrings
        [ "::" ":" "." "_" " " ]
        [ "-" "-" "-" "-" "-" ]
        lowered;
      collapse = s:
        let s' = builtins.replaceStrings [ "--" ] [ "-" ] s;
        in if s' == s then s else collapse s';
    in
    collapse replaced;

  # Structured hint constructor. `_tag = "Hint"` stops api.extractValue
  # from recursing into the record (matches the Layer ADT's discipline).
  # `severity` exists so promoting a hint to a warning is an additive
  # override. `docLink` is set to the section root here and overridden
  # per-entry below with `${docBase}/${slugify key}`.
  mkHint = category: text: {
    _tag = "Hint";
    inherit category text;
    severity = "error";
    docLink = docBase;
  };

  exampleCodeFor = key: hint:
    let
      parts = lib.splitString "::" key;
      pattern = builtins.elemAt parts 1;
      codeByKey = {
        "DArgSort::universe-mismatch" = ''
          # Bad: description argument sorts must stay in U0.
          descArg (u 1) (_: descRet tt)

          # Better: keep the argument sort small.
          descArg (u 0) (_: descRet tt)
        '';
        "DArgBody::not-a-desc" = ''
          # Bad: the body returns an ordinary term.
          descArg nat (_: natLit 0)

          # Better: the body returns a description.
          descArg nat (_: descRet tt)
        '';
        "DPiSort::universe-mismatch" = ''
          # Bad: descPi's domain sort is too large.
          descPi (u 1) f (_: descRet tt)

          # Better: use a small domain sort.
          descPi (u 0) f (_: descRet tt)
        '';
        "DPiBody::not-a-desc" = ''
          # Bad: the dependent body returns a term.
          descPi nat f (_: natLit 0)

          # Better: the dependent body returns a Desc.
          descPi nat f (_: descRet tt)
        '';
        "DRetIndex::type-mismatch" = ''
          # Bad: the return index is not in the Desc index type.
          descRet wrongIndex

          # Better: return at an index of the declared index type.
          descRet expectedIndex
        '';
        "DRecIndex::type-mismatch" = ''
          # Bad: the recursive position points at the wrong index type.
          descRec wrongIndex tailDesc

          # Better: recurse at an index from the Desc index type.
          descRec expectedIndex tailDesc
        '';
        "DRecTail::not-a-desc" = ''
          # Bad: the tail after a recursive position is a term.
          descRec i (natLit 0)

          # Better: continue with another description.
          descRec i (descRet i)
        '';
        "PiDom::not-a-type" = ''
          # Bad: a Pi domain must be a type, not a term.
          pi (natLit 0) (_: nat)

          # Better: put a type in the domain.
          pi nat (_: nat)
        '';
        "PiCod::not-a-type" = ''
          # Bad: the codomain family returns a term.
          pi nat (_: natLit 0)

          # Better: the codomain family returns a type.
          pi nat (_: nat)
        '';
        "AnnType::not-a-type" = ''
          # Bad: the annotation is a term.
          ann (natLit 0) (natLit 1)

          # Better: annotate with a type.
          ann (natLit 0) nat
        '';
        "MuDesc::not-a-desc" = ''
          # Bad: mu expects a Desc, not a term.
          mu nat (natLit 0)

          # Better: construct the Desc explicitly.
          mu nat (descRet zero)
        '';
        "Scrut::type-mismatch" = ''
          # Bad: the eliminator is used on a scrutinee of the wrong type.
          natElim motive zero succCase true_

          # Better: use a scrutinee with the eliminator's type.
          natElim motive zero succCase (natLit 3)
        '';
        "Motive::not-a-function" = ''
          # Bad: an eliminator motive is a bare type.
          natElim nat zero succCase n

          # Better: make the motive a function from the scrutinee.
          natElim (x: nat) zero succCase n
        '';
        "JType::not-a-type" = ''
          # Bad: J's type argument is a term.
          J (natLit 0) motive refl x y p

          # Better: J's type argument is the type of both endpoints.
          J nat motive refl x y p
        '';
        "DPiFn::not-a-function" = ''
          # Bad: the index selector is not a function.
          descPi nat expectedIndex (_: descRet expectedIndex)

          # Better: provide a selector from the domain into the index type.
          descPi nat (x: expectedIndex) (_: descRet expectedIndex)
        '';
        "DPiFn::type-mismatch" = ''
          # Bad: the selector domain does not match the declared sort.
          descPi nat (s: stringIndex) (_: descRet stringIndex)

          # Better: the selector consumes the same sort descPi declares.
          descPi nat (n: natIndex n) (_: descRet (natIndex n))
        '';
        "DPlusL::not-a-desc" = ''
          # Bad: the left summand is not a description.
          descPlus (natLit 0) rightDesc

          # Better: both summands are descriptions.
          descPlus (descRet tt) rightDesc
        '';
        "DPlusR::not-a-desc" = ''
          # Bad: the right summand is not a description.
          descPlus leftDesc (natLit 0)

          # Better: both summands are descriptions.
          descPlus leftDesc (descRet tt)
        '';
        "AnnTerm::type-mismatch" = ''
          # Bad: the annotated term does not inhabit the annotation.
          ann true_ nat

          # Better: the term matches the annotation.
          ann (natLit 1) nat
        '';
        "AppHead::not-a-function" = ''
          # Bad: the application head is not a function.
          app (natLit 0) (natLit 1)

          # Better: apply a lambda or another Pi-typed term.
          app (lam "x" nat (x: x)) (natLit 1)
        '';
        "AppArg::type-mismatch" = ''
          # Bad: the argument does not match the function domain.
          app (lam "x" nat (x: x)) true_

          # Better: pass an argument from the domain.
          app (lam "x" nat (x: x)) (natLit 1)
        '';
        "MuIndex::type-mismatch" = ''
          # Bad: the constructor index has the wrong type.
          con wrongIndex payload

          # Better: construct at an index from the declared index type.
          con expectedIndex payload
        '';
        "MuPayload::type-mismatch" = ''
          # Bad: the payload does not match the constructor description.
          con expectedIndex wrongPayload

          # Better: build a payload matching the description at that index.
          con expectedIndex expectedPayload
        '';
        "OpaqueType::not-a-function" = ''
          # Bad: an opaque lambda annotation must be a Pi type.
          opaqueLam nat body

          # Better: annotate it with a function type.
          opaqueLam (pi nat (_: nat)) body
        '';
        "OpaqueType::type-mismatch" = ''
          # Bad: the opaque lambda domain disagrees with the expected domain.
          opaqueLam (pi bool (_: nat)) body

          # Better: align the declared domain with the expected Pi domain.
          opaqueLam (pi nat (_: nat)) body
        '';
        "Motive::not-a-type" = ''
          # Bad: the motive returns a term.
          motive = x: natLit 0

          # Better: the motive returns a type.
          motive = x: nat
        '';
        "JType::type-mismatch" = ''
          # Bad: J's type argument does not match the endpoints.
          J bool motive refl zero zero p

          # Better: use the endpoints' shared type.
          J nat motive refl zero zero p
        '';
        "Field::inhabitation-failed" = ''
          # Bad: the field value has the wrong shape.
          User.validate { name = 42; }

          # Better: use a value inhabiting the field type.
          User.validate { name = "alice"; }
        '';
        "Field::refinement-failed" = ''
          # Bad: the field has the right base type but fails its predicate.
          User.validate { age = -1; }

          # Better: satisfy the refinement predicate.
          User.validate { age = 42; }
        '';
        "Elem::inhabitation-failed" = ''
          # Bad: a list element does not inhabit the element type.
          IntList.validate [ 1 "two" 3 ]

          # Better: every element inhabits the element type.
          IntList.validate [ 1 2 3 ]
        '';
        "Elem::refinement-failed" = ''
          # Bad: one element fails the element refinement.
          PositiveList.validate [ 1 -2 3 ]

          # Better: every element satisfies the refinement.
          PositiveList.validate [ 1 2 3 ]
        '';
        "Tag::inhabitation-failed" = ''
          # Bad: the variant payload does not inhabit the branch type.
          Result.validate { tag = "Ok"; value = false; }

          # Better: the payload matches the selected branch.
          Result.validate { tag = "Ok"; value = 200; }
        '';
        "Tag::refinement-failed" = ''
          # Bad: the variant payload fails the branch refinement.
          Port.validate { tag = "Tcp"; value = -1; }

          # Better: the payload satisfies the branch refinement.
          Port.validate { tag = "Tcp"; value = 443; }
        '';
        "Case::type-mismatch" = ''
          # Bad: one case branch returns the wrong type.
          caseOf scrutinee { left = x: true_; right = y: natLit 0; }

          # Better: all branches return the motive's type.
          caseOf scrutinee { left = x: natLit 1; right = y: natLit 0; }
        '';
        "SigmaFst::inhabitation-failed" = ''
          # Bad: the first component does not inhabit fst's type.
          pair "not-a-nat" proof

          # Better: fst inhabits its declared type.
          pair (natLit 3) proof
        '';
        "SigmaSnd::inhabitation-failed" = ''
          # Bad: the second component does not inhabit snd's dependent type.
          pair (natLit 3) "not-a-proof"

          # Better: snd inhabits the type determined by fst.
          pair (natLit 3) proofFor3
        '';
        "SigmaFst::refinement-failed" = ''
          # Bad: fst has the right base type but fails its refinement.
          pair (-1) proof

          # Better: fst satisfies the refinement.
          pair 1 proof
        '';
        "SigmaSnd::refinement-failed" = ''
          # Bad: snd fails the refinement depending on fst.
          pair 3 (-1)

          # Better: snd satisfies the dependent refinement.
          pair 3 4
        '';
        "LevelSucPred::type-mismatch" = ''
          # Bad: suc expects a Level.
          levelSuc nat

          # Better: pass a level expression.
          levelSuc level0
        '';
        "LevelMaxLhs::type-mismatch" = ''
          # Bad: max's left operand is not a Level.
          levelMax nat level0

          # Better: both operands are levels.
          levelMax level0 level1
        '';
        "LevelMaxRhs::type-mismatch" = ''
          # Bad: max's right operand is not a Level.
          levelMax level0 nat

          # Better: both operands are levels.
          levelMax level0 level1
        '';
        "ULevel::type-mismatch" = ''
          # Bad: U expects a Level argument.
          u nat

          # Better: pass a level.
          u level0
        '';
        "Motive.PiDom::not-a-type" = ''
          # Bad: the motive's Pi domain is a term.
          motive = pi (natLit 0) (_: u 0)

          # Better: the motive's Pi domain is a type.
          motive = pi nat (_: u 0)
        '';
        "::unhandled-lam" = ''
          # Bad: a lambda reaches inference without an expected Pi type.
          infer emptyCtx (lam "x" nat (x: x))

          # Better: annotate it so checking mode knows the Pi type.
          infer emptyCtx (ann (lam "x" nat (x: x)) (pi nat (_: nat)))
        '';
        "::unhandled-pair" = ''
          # Bad: a pair reaches inference without an expected Sigma type.
          infer emptyCtx (pair (natLit 1) true_)

          # Better: annotate it with the Sigma type it should inhabit.
          infer emptyCtx (ann (pair (natLit 1) true_) (sigma "x" nat (_: bool)))
        '';
        "::unhandled-tt" = ''
          # Bad: tt reaches inference without an expected Unit type.
          infer emptyCtx tt

          # Better: annotate tt or check it against unit.
          infer emptyCtx (ann tt unit)
        '';
        "::unhandled-boot-inl" = ''
          # Bad: inl does not determine the right summand by itself.
          infer emptyCtx (inl (natLit 1))

          # Better: annotate the intended sum type.
          infer emptyCtx (ann (inl (natLit 1)) (sum nat bool))
        '';
        "::unhandled-boot-inr" = ''
          # Bad: inr does not determine the left summand by itself.
          infer emptyCtx (inr true_)

          # Better: annotate the intended sum type.
          infer emptyCtx (ann (inr true_) (sum nat bool))
        '';
        "::unhandled-boot-refl" = ''
          # Bad: refl does not determine the equality type by itself.
          infer emptyCtx refl

          # Better: annotate the equality being proven.
          infer emptyCtx (ann refl (eq nat zero zero))
        '';
        "::unhandled-other" = ''
          # Bad: an introduction form reaches inference without context.
          infer emptyCtx introForm

          # Better: annotate the expected type at the boundary.
          infer emptyCtx (ann introForm expectedType)
        '';
      };
      codeByPattern = {
        "universe-mismatch" = ''
          # Bad: this slot requires a smaller universe.
          descArg (u 1) (_: descRet tt)

          # Better: use the expected universe level.
          descArg (u 0) (_: descRet tt)
        '';
        "not-a-desc" = ''
          # Bad: this slot requires a description.
          descArg nat (_: natLit 0)

          # Better: return a Desc.
          descArg nat (_: descRet tt)
        '';
        "not-a-type" = ''
          # Bad: this slot requires a type.
          pi (natLit 0) (_: nat)

          # Better: supply a type.
          pi nat (_: nat)
        '';
        "not-a-function" = ''
          # Bad: this slot requires a function.
          app (natLit 0) (natLit 1)

          # Better: supply a Pi-typed term.
          app (lam "x" nat (x: x)) (natLit 1)
        '';
        "not-a-pair" = ''
          # Bad: projection requires a pair.
          fst (natLit 0)

          # Better: project from a pair.
          fst (pair (natLit 0) true_)
        '';
        "type-mismatch" = ''
          # Bad: the term does not match the expected type.
          ann true_ nat

          # Better: make the term inhabit the expected type.
          ann (natLit 0) nat
        '';
        "inhabitation-failed" = ''
          # Bad: a value does not inhabit the expected type.
          Record.validate { age = "old"; }

          # Better: use a value with the expected shape.
          Record.validate { age = 42; }
        '';
        "refinement-failed" = ''
          # Bad: the base type matches, but the predicate fails.
          positive.validate (-1)

          # Better: satisfy the predicate.
          positive.validate 1
        '';
        "unhandled-lam" = codeByKey."::unhandled-lam";
        "unhandled-pair" = codeByKey."::unhandled-pair";
        "unhandled-tt" = codeByKey."::unhandled-tt";
        "unhandled-boot-inl" = codeByKey."::unhandled-boot-inl";
        "unhandled-boot-inr" = codeByKey."::unhandled-boot-inr";
        "unhandled-boot-refl" = codeByKey."::unhandled-boot-refl";
        "unhandled-other" = codeByKey."::unhandled-other";
      };
    in
    codeByKey.${key} or codeByPattern.${pattern} or ''
      # Bad: this term violates the hint's expected structure.
      checkHoas expectedType badTerm

      # Better: provide a term that matches the expected structure.
      checkHoas expectedType correctedTerm
    '';

  positionExprForTag = tag:
    if tag == "Field" then ''(P.Field "example")''
    else if tag == "Elem" then "(P.Elem 0)"
    else if tag == "Tag" then ''(P.Tag "Example")''
    else if tag == "Case" then ''(P.Case "example")''
    else "P.${tag}";

  leafExprForPattern = pattern:
    if pattern == "universe-mismatch" then ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "universe level mismatch";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      }
    ''
    else if pattern == "not-a-desc" then ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "expected a Desc";
        expected = { tag = "VDesc"; };
        got = { tag = "VUnit"; };
      }
    ''
    else if pattern == "not-a-type" then ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "expected a type";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VUnit"; };
      }
    ''
    else if pattern == "not-a-function" then ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "expected a function";
        expected = { tag = "VPi"; };
        got = { tag = "VUnit"; };
      }
    ''
    else if pattern == "not-a-pair" then ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "expected a pair";
        expected = { tag = "VSigma"; };
        got = { tag = "VUnit"; };
      }
    ''
    else if pattern == "inhabitation-failed" then ''
      E.mkGenericError {
        value = "bad";
        msg = "value does not inhabit the generated type";
      }
    ''
    else if pattern == "refinement-failed" then ''
      E.mkGenericError {
        value = (-1);
        guard = { predicate = "x >= 0"; };
        msg = "refinement failed";
      }
    ''
    else if lib.strings.hasPrefix "unhandled-" pattern then
      let
        shape = lib.strings.removePrefix "unhandled-" pattern;
        termTag = if shape == "other" then "mystery" else shape;
      in
      ''
        E.mkKernelError {
          rule = "docs-example";
          msg = "no inference rule for this introduction form";
          expected = null;
          got = null;
          term = { tag = "${termTag}"; };
        }
      ''
    else ''
      E.mkKernelError {
        rule = "docs-example";
        msg = "type mismatch";
        expected = { tag = "VUnit"; };
        got = { tag = "VString"; };
      }
    '';

  wrapErrorExpr = positions: leafName:
    builtins.foldl'
      (inner: tag: "E.nestUnder ${positionExprForTag tag} (${inner})")
      leafName
      (lib.reverseList positions);

  exampleSourceFor = key:
    let
      parts = lib.splitString "::" key;
      posSpec = builtins.elemAt parts 0;
      pattern = builtins.elemAt parts 1;
      positions =
        if posSpec == ""
        then [ "Sub" ]
        else lib.splitString "." posSpec;
      leafExpr = leafExprForPattern pattern;
      errorExpr = wrapErrorExpr positions "leaf";
    in
    ''
      { fx, key }:
      let
        E = fx.diag.error;
        P = fx.diag.positions;
        H = fx.diag.hints;
        leaf = ${leafExpr};
        error = ${errorExpr};
        hint = H.resolve error;
        expectedHint = builtins.getAttr key H.hints;
      in
      {
        inherit key;
        ok = hint == expectedHint;
        resolvedText = if hint == null then null else hint.text;
        resolvedDocLink = if hint == null then null else hint.docLink;
      }
    '';

  hintExampleFor = key: hint:
    let
      parts = lib.splitString "::" key;
      posSpec = builtins.elemAt parts 0;
      pattern = builtins.elemAt parts 1;
      hintToken =
        if posSpec == ""
        then "Hint::${pattern}"
        else "Hint::${key}";
      positionText =
        if posSpec == ""
        then "an introduction form in inference position"
        else
          let
            positions = lib.splitString "." posSpec;
            lastPosition = lib.last positions;
            parentPositions = lib.init positions;
          in
          if parentPositions == [ ]
          then "the `" + lastPosition + "` position"
          else "the `" + lastPosition + "` position under `" + lib.concatStringsSep "." parentPositions + "`";
      issueText = {
        "universe-mismatch" = "uses a universe level that is too large for that slot";
        "not-a-desc" = "uses an ordinary term where the checker needs a Desc";
        "not-a-type" = "uses a term or value where the checker needs a type";
        "not-a-function" = "uses a non-function where the checker needs a Pi-typed term";
        "not-a-pair" = "uses a non-pair where the checker needs a Sigma-typed term";
        "type-mismatch" = "supplies a term whose type does not match the expected type";
        "inhabitation-failed" = "contains a value that does not inhabit the generated type";
        "refinement-failed" = "contains a value that fails the refinement predicate";
        "unhandled-lam" = "a lambda is in inference mode without an expected Pi type";
        "unhandled-pair" = "a pair is in inference mode without an expected Sigma type";
        "unhandled-tt" = "`tt` is in inference mode without an expected Unit type";
        "unhandled-boot-inl" = "`inl` is in inference mode without an expected Sum type";
        "unhandled-boot-inr" = "`inr` is in inference mode without an expected Sum type";
        "unhandled-boot-refl" = "`refl` is in inference mode without an expected equality type";
        "unhandled-other" = "an introduction form is in inference mode without enough expected type information";
      }.${pattern} or "violates the expected structure at that position";
      subjectText =
        if posSpec == ""
        then issueText
        else "${positionText} ${issueText}";
      source = exampleSourceFor key;
    in
    {
      prose = "`${hintToken}` means ${subjectText}. The example shows the failing form first, then one way to give the checker the missing structure.";
      code = exampleCodeFor key hint;
      inherit source;
    };

  # One-sentence per-hint summary used by the docs-site renderer as
  # `description` front-matter (consumed by `/llms.txt`, JSON-LD, and
  # `<meta name="description">`). Front-loads the hint key, then takes
  # the first sentence of `text` verbatim. Schema-disciplined text
  # never contains `.nix`/`U.0`/etc., so splitting on `.` reliably
  # isolates the first sentence.
  #
  # No silent truncation: if a hint's first sentence plus the framing
  # overflows the 160-char budget, the `hints-descriptions-fit-budget`
  # test fails and the source `text` must be shortened (split into two
  # sentences at a natural clause boundary). Silent post-hoc truncation
  # is the failure mode the docs-site summaries originally exhibited —
  # this gate prevents it from recurring.
  hintDescription = key: text:
    let
      firstSentence = builtins.head (lib.splitString "." text);
    in
    "${key} — ${firstSentence}.";

  # Category taxonomy. Every hint entry's category must be one of these;
  # the `hints-categories-in-taxonomy` test enforces the closed set.
  taxonomy = [
    "universe"
    "sort"
    "description"
    "arity"
    "indexing"
    "inhabitation"
    "refinement"
    "elimination"
    "type-mismatch"
    "shape"
  ];

  # Walk the children[0] chain; return the list of positions from
  # root to leaf (or to the first branching node). Fast-path recursion
  # up to fastPathLimit, then genericClosure.
  chainPositions = err: chainFast [ ] err 0;

  chainFast = acc: err: depth:
    if builtins.length err.children != 1
    then acc
    else if depth >= fastPathLimit
    then chainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in chainFast (acc ++ [ edge.position ]) edge.error (depth + 1);

  chainSlow = acc0: err0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _acc = acc0; _err = err0; }];
        operator = st:
          if builtins.length st._err.children != 1 then [ ]
          else
            let
              edge = builtins.elemAt st._err.children 0;
              nextErr = edge.error;
              newAcc = st._acc ++ [ edge.position ];
            in
            [{
              key = builtins.seq nextErr
                (builtins.seq newAcc (st.key + 1));
              _acc = newAcc;
              _err = nextErr;
            }];
      };
    in
    (lib.last steps)._acc;

  # Reach the endpoint (the first node with !=1 children). Same split.
  chainEndpoint = err: endpointFast err 0;

  endpointFast = err: depth:
    if builtins.length err.children != 1 then err
    else if depth >= fastPathLimit then endpointSlow err
    else endpointFast (builtins.elemAt err.children 0).error (depth + 1);

  endpointSlow = err0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _err = err0; }];
        operator = st:
          if builtins.length st._err.children != 1 then [ ]
          else
            let nextErr = (builtins.elemAt st._err.children 0).error;
            in [{
              key = builtins.seq nextErr (st.key + 1);
              _err = nextErr;
            }];
      };
    in
    (lib.last steps)._err;

  # Classify a leaf Error's Detail into a short pattern string. The
  # classifier is conservative: it reads only the Detail fields set
  # by mkKernelError / mkGenericError at emission sites. Unrecognised
  # shapes return "type-mismatch" (generic kernel) or "generic".
  #
  # Rules emit `expected` / `got` in one of three shapes:
  #   * kernel values   — tags `VU`, `VPi`, `VSigma`, `VDesc`
  #   * quoted terms    — tags `U`, `pi`, `sigma`, `desc` (after Q.quote)
  #   * literal markers — `{ tag = "U"; }`, `{ tag = "pi"; }` (surface hints)
  # The `isX` predicates accept all three so a single classifier covers
  # every emission path.
  tagOf = v: v.tag or null;
  levelOf = v: v.level or null;

  isU = v: let t = tagOf v; in t == "VU" || t == "U";
  isDesc = v: let t = tagOf v; in t == "VDesc" || t == "desc";
  isPi = v: let t = tagOf v; in t == "VPi" || t == "pi";
  isSigma = v: let t = tagOf v; in t == "VSigma" || t == "sigma";

  classify = err:
    if err.layer.tag == "Kernel" then classifyKernel err.detail
    else if err.layer.tag == "Contract" then "refinement-failed"
    else classifyGeneric err.detail;

  # Recognised intro-form tags handled by the unhandled-shape family.
  # Tags outside this set collapse to "unhandled-other" so the renderer
  # always resolves a hint via the shape category.
  unhandledShapeTags = [
    "lam"
    "pair"
    "tt"
    "boot-inl"
    "boot-inr"
    "boot-refl"
  ];

  classifyKernel = d:
    let
      tt = d.term.tag or null;
      shaped = d.expected == null && d.got == null && tt != null;
    in
    if shaped then
      if builtins.elem tt unhandledShapeTags
      then "unhandled-${tt}"
      else "unhandled-other"
    else if isU d.expected && isU d.got && levelOf d.expected != levelOf d.got
    then "universe-mismatch"
    else if isU d.expected && !(isU d.got) then "not-a-type"
    else if isDesc d.expected && !(isDesc d.got) then "not-a-desc"
    else if isPi d.expected && !(isPi d.got) then "not-a-function"
    else if isSigma d.expected && !(isSigma d.got) then "not-a-pair"
    else "type-mismatch";

  classifyGeneric = d:
    if d.guard != null then "refinement-failed"
    else "inhabitation-failed";

  # Hint table. Keys are "<Position.tag>::<pattern>" strings built
  # from the leaf Position and the Detail-classified pattern. Values
  # are Hint records (see mkHint). No kernel-rule strings appear in
  # keys or text; text is position-semantic.
  #
  # Each entry's `docLink` is rewritten below to point at the per-key
  # page `/nix-effects/diag-hints/<slug>`, computed by `slugify`
  # so the URL path segment matches the file name emitted by
  # `book/gen/docs-content.nix:diagHintsEntries`.
  hintsByKey = {
    "DArgSort::universe-mismatch" = mkHint "universe"
      "the sort position of `arg` must live in U(0); descriptions only carry small types. Pass `u 0`, or factor the dependency through `descRec` / `descPi` if a larger type is genuinely needed.";
    "DArgBody::not-a-desc" = mkHint "description"
      "the body of `arg` must produce a description (Desc I), not an ordinary value. Build one with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "DPiSort::universe-mismatch" = mkHint "universe"
      "the sort position of `pi` must live in U(0); `descPi` takes a small domain. Use `u 0`, or encode the dependency through an index instead of the Pi domain.";
    "DPiBody::not-a-desc" = mkHint "description"
      "the body of `pi` must produce a description for each input, not a plain term. Return a Desc I via `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "DRetIndex::type-mismatch" = mkHint "indexing"
      "the index position of `ret` must match the Desc's declared index type. Supply a term of that index type, or redefine the enclosing `μ I ...` over the index you actually have.";
    "DRecIndex::type-mismatch" = mkHint "indexing"
      "the index position of `rec` must match the Desc's declared index type. Pass a term of that index type, or adjust the enclosing `μ I ...` to match.";
    "DRecTail::not-a-desc" = mkHint "description"
      "the tail position of `rec` must itself be a description, not an ordinary term. Continue the spine with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "PiDom::not-a-type" = mkHint "sort"
      "the domain of Π must be a type (live in some U(k)), not a term or value. Supply a type expression like `nat`, `bool`, `u 0`, or a user-defined datatype.";
    "PiCod::not-a-type" = mkHint "sort"
      "the codomain family of Π must return a type for each argument, not an ordinary value. Provide a function whose body inhabits some `U k`.";
    "AnnType::not-a-type" = mkHint "sort"
      "the annotation position must be a type (live in some U(k)), not a term. Write a type expression such as `nat`, `bool`, `u 0`, or a user-defined datatype.";
    "MuDesc::not-a-desc" = mkHint "description"
      "the description argument of μ must be a Desc I term, not an ordinary value. Construct it with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "Scrut::type-mismatch" = mkHint "elimination"
      "the scrutinee's type must match the eliminator's expected shape. Annotate the scrutinee via `ann`, or switch to the eliminator that matches its inferred type.";
    "Motive::not-a-function" = mkHint "arity"
      "the motive must be a function from the scrutinee's type into a type, not a bare type or value. Supply a one-argument function whose body lives in some `U k`.";
    "JType::not-a-type" = mkHint "sort"
      "the type parameter of `J` must be a type (live in some U(k)), not a term. Pass a type expression like `nat`, `u 0`, or the type shared by J's two endpoints.";
    "DPiFn::not-a-function" = mkHint "arity"
      "the index selector `f` of `pi` must be a function `S -> I`";
    "DPiFn::type-mismatch" = mkHint "indexing"
      "the index selector's domain must match the declared sort `S`";
    "DPlusL::not-a-desc" = mkHint "description"
      "the left summand of `plus` must be a description (Desc I)";
    "DPlusR::not-a-desc" = mkHint "description"
      "the right summand of `plus` must be a description at the same index type as the left summand";
    "AnnTerm::type-mismatch" = mkHint "type-mismatch"
      "the annotated term does not match its declared type";
    "AppHead::not-a-function" = mkHint "arity"
      "the head of an application must have a function type (Pi)";
    "AppArg::type-mismatch" = mkHint "type-mismatch"
      "the argument does not match the function's domain";
    "MuIndex::type-mismatch" = mkHint "indexing"
      "the index passed to `con` must have the description's index type";
    "MuPayload::type-mismatch" = mkHint "indexing"
      "the payload of `con` must inhabit the description's interpretation at the given index";
    "OpaqueType::not-a-function" = mkHint "arity"
      "the annotation on an opaque lambda must be a Pi type";
    "OpaqueType::type-mismatch" = mkHint "type-mismatch"
      "the opaque lambda's declared domain does not match the expected domain";
    "Motive::not-a-type" = mkHint "sort"
      "an eliminator's motive must return a type (live in some U(k))";
    "JType::type-mismatch" = mkHint "type-mismatch"
      "the type parameter of `J` must match the type of its two endpoints";
    "Field::inhabitation-failed" = mkHint "inhabitation"
      "the field's value does not inhabit the declared field type";
    "Field::refinement-failed" = mkHint "refinement"
      "the field's value violates the field type's refinement predicate";
    "Elem::inhabitation-failed" = mkHint "inhabitation"
      "the element does not inhabit the list's element type";
    "Elem::refinement-failed" = mkHint "refinement"
      "the element violates the element type's refinement predicate";
    "Tag::inhabitation-failed" = mkHint "inhabitation"
      "the variant's payload does not inhabit the branch type";
    "Tag::refinement-failed" = mkHint "refinement"
      "the variant's payload violates the branch type's refinement predicate";
    "Case::type-mismatch" = mkHint "elimination"
      "this case-body's inferred type does not match the type the eliminator's motive requires";
    "SigmaFst::inhabitation-failed" = mkHint "inhabitation"
      "the first component does not inhabit the declared `fst` type";
    "SigmaSnd::inhabitation-failed" = mkHint "inhabitation"
      "the second component does not inhabit the dependent `snd` type";
    "SigmaFst::refinement-failed" = mkHint "refinement"
      "the first component violates the `fst` type's refinement predicate";
    "SigmaSnd::refinement-failed" = mkHint "refinement"
      "the second component violates the `snd` type's refinement predicate";
    "LevelSucPred::type-mismatch" = mkHint "universe"
      "the predecessor of `suc` must be a Level";
    "LevelMaxLhs::type-mismatch" = mkHint "universe"
      "the left operand of `max` must be a Level";
    "LevelMaxRhs::type-mismatch" = mkHint "universe"
      "the right operand of `max` must be a Level";
    "ULevel::type-mismatch" = mkHint "universe"
      "the level argument of `U` must be a Level";

    # -- Multi-hop entries. Match on a leaf-anchored suffix of the
    # blame path; longest-match wins against the single-position keys.
    "Motive.PiDom::not-a-type" = mkHint "sort"
      "the motive's domain must be a type (live in some U(k)). The motive receives the scrutinee's type as its domain and returns a type; supply a concrete type such as `nat`, `u 0`, or the datatype being eliminated.";

    # -- Unhandled term shapes. The kernel's `infer` rule produces these
    # when a bidirectional intro form reaches it without a check-direction
    # annotation supplying the expected type. Entries with empty position
    # prefix match any blame-path tail; they are tried last (lowest
    # priority) so longer-prefix matches still win.
    "::unhandled-lam" = mkHint "shape"
      "this lambda has no inference rule — its domain and codomain types are not determined by its syntax. Annotate with `ann (lam …) (pi A B)` to drive checking, or place it where the surrounding rule already supplies an expected Pi type.";
    "::unhandled-pair" = mkHint "shape"
      "this pair has no inference rule — its component types are not determined by its syntax. Annotate with `ann (pair …) (sigma A B)` to drive checking, or place it where the surrounding rule already supplies an expected Sigma type.";
    "::unhandled-tt" = mkHint "shape"
      "the unit value `tt` has no inference rule — there is exactly one type it can inhabit. The kernel still asks for an annotation to keep inference syntax-directed. Use `ann tt unit` at the use site, or check `tt` against an expected `unit` type.";
    "::unhandled-boot-inl" = mkHint "shape"
      "the left injection `inl x` has no inference rule — the sum type's right summand is not determined by the syntax of `x` alone. Annotate with `ann (inl x) (sum A B)` to fix the expected sum, or place it where checking already provides one.";
    "::unhandled-boot-inr" = mkHint "shape"
      "the right injection `inr y` has no inference rule — the sum type's left summand is not determined by the syntax of `y` alone. Annotate with `ann (inr y) (sum A B)` to fix the expected sum, or place it where checking already provides one.";
    "::unhandled-boot-refl" = mkHint "shape"
      "`refl` has no inference rule — the type of the equated endpoint is not determined by its syntax. Annotate with `ann refl (eq A x x)`, or use `refl` where the surrounding rule already supplies an expected equality type.";
    "::unhandled-other" = mkHint "shape"
      "this intro form has no inference rule — its type is not determined by its syntax alone. Either annotate the term with `ann <term> <type>` to switch the kernel into checking mode, or move it inside a context where an expected type is already known.";
  };

  # Final hint table: rewrite each entry's docLink to its dedicated
  # per-key page. The slug is computed by the same rule that
  # `book/gen/docs-content.nix` uses to name the `.md` file, so the URL
  # dereferences to the focused per-key markdown page in one fetch.
  # Per-key docLink. Wildcard keys ("::pattern") slugify on the pattern
  # alone — the empty position spec would otherwise yield a leading
  # dash and a confusing URL segment.
  slugForKey = key:
    if lib.strings.hasPrefix "::" key
    then slugify (lib.strings.removePrefix "::" key)
    else slugify key;

  # `srcPosition` is captured against `hintsByKey` so the position
  # tracks the registry's source line, not this mapAttrs callback's
  # synthetic site. Renderers cross-link each per-key page back to its
  # definition for one-fetch source lookup from a Hint emission.
  hints = lib.mapAttrs
    (key: hint: hint // {
      docLink = "${docBase}/${slugForKey key}";
      description = hintDescription key hint.text;
      srcPosition = builtins.unsafeGetAttrPos key hintsByKey;
    })
    hintsByKey;

  hintExamples = lib.mapAttrs hintExampleFor hintsByKey;

  # -- Key parsing and indexing (precomputed at module load).
  #
  # Each key decomposes into `(positions, pattern)` where `positions`
  # is the list of position tags parsed from the dot-separated prefix
  # and `pattern` is the classifier suffix after `::`. The index
  # `hintsByPattern` groups keys by pattern with each bucket sorted
  # descending by positions-length so `resolve` iterates candidates
  # longest-first and stops at the first tail-match.
  parseKey = k:
    let
      parts = lib.splitString "::" k;
      pattern = builtins.elemAt parts 1;
      posSpec = builtins.elemAt parts 0;
      # An empty position spec marks a wildcard: the entry matches any
      # non-empty blame chain. Wildcards sort last (length 0) so they
      # only fire when no longer-prefix candidate matches.
      positions = if posSpec == "" then [ ] else lib.splitString "." posSpec;
    in
    {
      inherit positions pattern;
      length = builtins.length positions;
      key = k;
    };

  parsedKeys = map parseKey (builtins.attrNames hints);

  hintsByPattern =
    let
      grouped = lib.groupBy (m: m.pattern) parsedKeys;
      sortDesc = ms: lib.sort (a: b: a.length > b.length) ms;
    in
    lib.mapAttrs (_: sortDesc) grouped;

  # Entry point. Returns the Hint record registered under the longest
  # leaf-anchored suffix of the blame path that classifies matches,
  # or null when no entry matches.
  resolve = err:
    let
      positions = chainPositions err;
      n = builtins.length positions;
    in
    if n == 0 then null
    else
      let
        leaf = chainEndpoint err;
        pattern = classify leaf;
        candidates = hintsByPattern.${pattern} or [ ];
        # Lazy suffix: materialise only k tags on demand. For the
        # 5000-deep bench workload with 1-position candidates this
        # allocates a single-element list after one elemAt.
        tailTags = k:
          builtins.genList
            (i: (builtins.elemAt positions (n - k + i)).tag)
            k;
        firstMatch = ms:
          if ms == [ ] then null
          else
            let m = builtins.head ms;
            in if m.length == 0
            then hints.${m.key}
            else if m.length <= n && tailTags m.length == m.positions
            then hints.${m.key}
            else firstMatch (builtins.tail ms);
      in
      firstMatch candidates;

  # Build-chain helper for the stack-safety stress test. Matches the
  # pattern used in pretty.nix's tests.
  leafUMismatch = fx.diag.error.mkKernelError {
    rule = "check";
    msg = "type mismatch";
    expected = { tag = "VU"; level = 0; };
    got = { tag = "VU"; level = 1; };
  };

  chain5000 =
    builtins.foldl'
      (inner: _:
        fx.diag.error.nestUnder fx.diag.positions.DArgSort inner
      )
      leafUMismatch
      (lib.range 1 5000);

in
(api.namespace {
  description = "fx.diag.hints: closed registry mapping blame-path-suffix keys to Hint records; `resolve` walks an Error's chain inward and returns the longest-suffix match.";
  doc = ''
    Hint resolver for diagnostic Errors.

    Exports:
      resolve  : Error -> Hint | null
      classify : Error -> String
      hints    : { <key> = Hint; }

    A Hint is `{ _tag = "Hint"; text; category; severity; docLink; }`.
    The `_tag` marker keeps it terminal for `api.extractValue`, and
    the remaining fields are plain data consumable by renderers,
    LSPs, docs, and linters. Severity is `"error"` at this layer;
    `docLink` resolves to a dedicated per-key page on
    `docs.kleisli.io` of the form
    `/nix-effects/diag-hints/<slug>`, where `<slug>` matches the
    docs-site heading-id slugification rule applied to the key.
    Each per-key page is also exposed as an MCP resource at
    `docs://kleisli/nix-effects/diag-hints/<slug>`, so a compiler
    Hint dereferences to focused agent-readable content in one
    fetch.

    Keys encode a leaf-anchored suffix of the blame path plus the
    classifier pattern: `"<pos1>.<pos2>...<posN>::<pattern>"`. A key
    matches when its positions equal the last N tags of the blame
    path; `resolve` returns the hint under the longest matching
    suffix. Single-position keys are the 1-hop special case. Hint
    text is position-semantic: no kernel-rule strings, no source-file
    references.

    Chain walking recurses directly up to ${toString fastPathLimit}
    frames, then falls through to a `builtins.genericClosure` slow
    path that WHNF-forces the next node.
  '';
  tests = {
    # -- resolve: happy-path hits covering the required ≥7 hints. --
    "resolve-DArgSort-universe-mismatch" = {
      expr = resolve (fx.diag.error.nestUnder
        fx.diag.positions.DArgSort
        leafUMismatch);
      expected = hints."DArgSort::universe-mismatch";
    };
    "resolve-DPiSort-universe-mismatch" = {
      expr = resolve (fx.diag.error.nestUnder
        fx.diag.positions.DPiSort
        leafUMismatch);
      expected = hints."DPiSort::universe-mismatch";
    };
    "resolve-DArgBody-not-a-desc" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-arg";
            msg = "type mismatch";
            expected = { tag = "VDesc"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DArgBody
          leaf);
      expected = hints."DArgBody::not-a-desc";
    };
    "resolve-AnnType-not-a-type" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "ann";
            msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.AnnType
          leaf);
      expected = hints."AnnType::not-a-type";
    };
    "resolve-PiDom-not-a-type" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "pi-dom";
            msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VBool"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.PiDom
          leaf);
      expected = hints."PiDom::not-a-type";
    };
    "resolve-MuDesc-not-a-desc" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "mu";
            msg = "type mismatch";
            expected = { tag = "VDesc"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.MuDesc
          leaf);
      expected = hints."MuDesc::not-a-desc";
    };
    "resolve-Motive-not-a-function" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "elim";
            msg = "motive must be Π";
            expected = { tag = "VPi"; };
            got = { tag = "VU"; level = 0; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.Motive
          leaf);
      expected = hints."Motive::not-a-function";
    };

    # -- resolve: misses return null without error. --
    "resolve-unwrapped-leaf-returns-null" = {
      expr = resolve leafUMismatch;
      expected = null;
    };
    "resolve-unknown-position-returns-null" = {
      expr = resolve (fx.diag.error.nestUnder
        fx.diag.positions.AppArg
        leafUMismatch);
      expected = null;
    };

    # -- classify: kernel patterns --
    "classify-universe-mismatch" = {
      expr = classify leafUMismatch;
      expected = "universe-mismatch";
    };
    "classify-not-a-type" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VUnit"; };
      });
      expected = "not-a-type";
    };
    "classify-not-a-desc" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "VDesc"; };
        got = { tag = "VUnit"; };
      });
      expected = "not-a-desc";
    };
    "classify-not-a-function" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "VPi"; };
        got = { tag = "VU"; level = 0; };
      });
      expected = "not-a-function";
    };
    "classify-not-a-pair" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "VSigma"; };
        got = { tag = "VUnit"; };
      });
      expected = "not-a-pair";
    };
    # Term-shape emissions (from Q.quote) must classify identically to
    # value-shape emissions so real kernel errors surface hints.
    "classify-term-shape-universe-mismatch" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "U"; level = 0; };
        got = { tag = "U"; level = 3; };
      });
      expected = "universe-mismatch";
    };
    "classify-term-shape-not-a-type" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "U"; level = 0; };
        got = { tag = "nat"; };
      });
      expected = "not-a-type";
    };
    "classify-term-shape-not-a-desc" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "desc"; };
        got = { tag = "nat"; };
      });
      expected = "not-a-desc";
    };
    "classify-term-shape-not-a-function" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "pi"; };
        got = { tag = "U"; level = 0; };
      });
      expected = "not-a-function";
    };
    "classify-term-shape-not-a-pair" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r";
        msg = "m";
        expected = { tag = "sigma"; };
        got = { tag = "nat"; };
      });
      expected = "not-a-pair";
    };
    "resolve-term-shape-DArgSort-universe" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "check";
            msg = "type mismatch";
            expected = { tag = "U"; level = 0; };
            got = { tag = "U"; level = 2; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DArgSort
          leaf);
      expected = hints."DArgSort::universe-mismatch";
    };
    "resolve-term-shape-PiDom-not-a-type" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType";
            msg = "expected a type";
            expected = { tag = "U"; level = 0; };
            got = { tag = "nat"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.PiDom
          leaf);
      expected = hints."PiDom::not-a-type";
    };
    "resolve-term-shape-Motive-not-a-function" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "elim";
            msg = "motive must be Π";
            expected = { tag = "pi"; };
            got = { tag = "U"; level = 0; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.Motive
          leaf);
      expected = hints."Motive::not-a-function";
    };

    "classify-refinement-failed" = {
      expr = classify (fx.diag.error.mkGenericError {
        value = 17;
        guard = { predicate = "x > 18"; };
        msg = "refinement failed";
      });
      expected = "refinement-failed";
    };
    "classify-inhabitation-failed" = {
      expr = classify (fx.diag.error.mkGenericError {
        value = "bad";
        msg = "value does not inhabit description";
      });
      expected = "inhabitation-failed";
    };
    "classify-contract-routes-to-refinement-failed" = {
      expr = classify (fx.diag.error.mkContractError {
        value = (-1);
        guard = { predicate = "x > 0"; };
        msg = "contract failed";
      });
      expected = "refinement-failed";
    };
    "classify-unhandled-shape-pair" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "infer";
        msg = "no inference rule for term shape pair";
        expected = null;
        got = null;
        term = { tag = "pair"; };
      });
      expected = "unhandled-pair";
    };
    "classify-unhandled-shape-other-fallback" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "infer";
        msg = "no inference rule for term shape mystery";
        expected = null;
        got = null;
        term = { tag = "mystery"; };
      });
      expected = "unhandled-other";
    };
    "classify-unhandled-shape-tt" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "infer";
        msg = "no inference rule for term shape tt";
        expected = null;
        got = null;
        term = { tag = "tt"; };
      });
      expected = "unhandled-tt";
    };

    # -- Hint-table discipline: no rule-file substrings anywhere. --
    "hints-table-covers-at-least-seven-entries" = {
      expr = builtins.length (builtins.attrNames hints) >= 7;
      expected = true;
    };
    "hints-keys-have-no-rule-file-substrings" = {
      expr =
        let
          forbidden = [ "infer.nix" "check.nix" "type.nix" "rule" ];
          keys = builtins.attrNames hints;
        in
        builtins.all
          (k: builtins.all
            (bad: !(lib.strings.hasInfix bad k))
            forbidden)
          keys;
      expected = true;
    };
    "hints-text-references-no-rule-files" = {
      expr =
        let
          forbidden = [
            "infer.nix"
            "check.nix"
            "type.nix"
            "check/"
            "src/"
          ];
          values = builtins.attrValues hints;
        in
        builtins.all
          (v: builtins.all
            (bad: !(lib.strings.hasInfix bad v.text))
            forbidden)
          values;
      expected = true;
    };

    # -- Schema discipline: every entry is a Hint record. --
    "hints-every-entry-has-Hint-schema" = {
      expr =
        let
          values = builtins.attrValues hints;
          wellFormed = v:
            builtins.isAttrs v
            && (v._tag or null) == "Hint"
            && builtins.isString (v.text or null)
            && builtins.isString (v.category or null)
            && builtins.isString (v.severity or null)
            && builtins.isString (v.docLink or null);
        in
        builtins.all wellFormed values;
      expected = true;
    };
    "hints-runtime-records-do-not-carry-doc-examples" = {
      expr =
        builtins.all
          (v: !(v ? example) && !(v ? prose) && !(v ? code) && !(v ? source))
          (builtins.attrValues hints);
      expected = true;
    };
    "hint-examples-cover-every-entry" = {
      expr = builtins.attrNames hintExamples == builtins.attrNames hints;
      expected = true;
    };
    "hint-examples-have-prose-code-and-source" = {
      expr =
        let
          values = builtins.attrValues hintExamples;
          wellFormed = v:
            builtins.isString (v.prose or null)
            && v.prose != ""
            && builtins.isString (v.code or null)
            && v.code != ""
            && builtins.isString (v.source or null)
            && v.source != "";
        in
        builtins.all wellFormed values;
      expected = true;
    };
    "hint-examples-source-is-executable" = {
      expr =
        let
          run = key:
            let
              ex = hintExamples.${key};
              result = import (builtins.toFile "diag-hint-example-${slugForKey key}.nix" ex.source) {
                inherit fx key;
              };
            in
            result.ok == true
            && result.key == key
            && builtins.isString result.resolvedText
            && lib.strings.hasPrefix docBase result.resolvedDocLink;
        in
        builtins.all run (builtins.attrNames hintExamples);
      expected = true;
    };
    "hint-examples-keep-executable-source-private" = {
      expr =
        builtins.all
          (v:
            lib.strings.hasInfix "{ fx, key }:" v.source
            && lib.strings.hasInfix "ok = hint == expectedHint;" v.source
            && !(lib.strings.hasInfix "{ fx, key }:" v.code)
            && !(lib.strings.hasInfix "fx.diag.hints.resolve" v.code))
          (builtins.attrValues hintExamples);
      expected = true;
    };
    "hint-examples-do-not-render-wildcards-with-four-colons" = {
      expr =
        builtins.all
          (v: !(lib.strings.hasInfix "Hint::::" v.prose))
          (builtins.attrValues hintExamples);
      expected = true;
    };
    "hint-examples-avoid-internal-shape-wording" = {
      expr =
        builtins.all
          (v: !(lib.strings.hasInfix "diagnostic shape" v.prose))
          (builtins.attrValues hintExamples);
      expected = true;
    };

    # -- Taxonomy discipline: every category is a taxonomy member. --
    "hints-categories-in-taxonomy" = {
      expr =
        let
          values = builtins.attrValues hints;
          allowed = cat: builtins.elem cat taxonomy;
        in
        builtins.all (v: allowed v.category) values;
      expected = true;
    };

    # -- Description budget: every per-key description fits in ≤160
    # chars without silent truncation. When this fails, shorten the
    # offending hint's `text` by splitting its first sentence at a
    # natural clause boundary — the description renderer takes the
    # text up to the first `.`, so inserting an earlier period is the
    # principled cut.
    "hints-descriptions-fit-budget" = {
      expr =
        let
          values = builtins.attrValues hints;
        in
        builtins.all
          (v: builtins.stringLength v.description <= 160)
          values;
      expected = true;
    };

    # -- Doc-link discipline: every entry points at the docs site. --
    "hints-docLinks-resolve-to-docs-site" = {
      expr =
        let values = builtins.attrValues hints;
        in builtins.all
          (v: lib.strings.hasPrefix "https://docs.kleisli.io/" v.docLink)
          values;
      expected = true;
    };

    # -- Path coherence: every docLink decomposes as
    # `${docBase}/${slugForKey key}`. Wildcard keys ("::pattern") slug
    # off the pattern alone to avoid leading-dash URL segments.
    "hints-docLinks-have-matching-per-key-path" = {
      expr =
        let
          check = key: hint:
            hint.docLink == "${docBase}/${slugForKey key}";
        in
        builtins.all
          (key: check key hints.${key})
          (builtins.attrNames hints);
      expected = true;
    };

    # -- Key syntax: every key parses to either a wildcard (empty
    # positions list, intentional fallback) or a non-empty positions
    # list with non-empty position tags. Guards against accidental
    # double-dots (`"A..B::pat"`) and stray empty mid-prefixes.
    "hints-keys-parse-valid-positions" = {
      expr = builtins.all
        (m: m.length == 0
          || (m.length >= 1
          && builtins.all (p: p != "") m.positions))
        parsedKeys;
      expected = true;
    };

    # -- Stack-safety stress: resolve on a 5000-deep chain. --
    "resolve-5000-deep-chain" = {
      expr = resolve chain5000;
      expected = hints."DArgSort::universe-mismatch";
    };

    # -- Multi-hop resolve: longest suffix wins over the 1-hop leaf. --
    "resolve-multi-hop-Motive-PiDom-wins-over-PiDom" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType";
            msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
          chain = fx.diag.error.nestUnder fx.diag.positions.Motive
            (fx.diag.error.nestUnder fx.diag.positions.PiDom leaf);
        in
        resolve chain;
      expected = hints."Motive.PiDom::not-a-type";
    };
    "resolve-multi-hop-falls-back-to-leaf-PiDom" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType";
            msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.PiDom
          leaf);
      expected = hints."PiDom::not-a-type";
    };
    # A 3-hop chain whose outer positions have no multi-hop entry must
    # still resolve via the longest matching suffix — here the 2-hop
    # `Motive.PiDom::not-a-type`. Any 3-hop prefix key would win over it
    # if registered; absent that, the 2-hop key is the longest match.
    "resolve-multi-hop-3-hop-longest-suffix-wins" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType";
            msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
          chain =
            fx.diag.error.nestUnder fx.diag.positions.AppArg
              (fx.diag.error.nestUnder fx.diag.positions.Motive
                (fx.diag.error.nestUnder fx.diag.positions.PiDom leaf));
        in
        resolve chain;
      expected = hints."Motive.PiDom::not-a-type";
    };

    # -- resolve: Kernel-layer positions. --
    "resolve-DPiFn-not-a-function" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-pi";
            msg = "f must have type S -> I";
            expected = { tag = "VPi"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DPiFn
          leaf);
      expected = hints."DPiFn::not-a-function";
    };
    "resolve-DPiFn-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-pi";
            msg = "domain mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DPiFn
          leaf);
      expected = hints."DPiFn::type-mismatch";
    };
    "resolve-DPlusL-not-a-desc" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-plus";
            msg = "A must be Desc";
            expected = { tag = "VDesc"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DPlusL
          leaf);
      expected = hints."DPlusL::not-a-desc";
    };
    "resolve-DPlusR-not-a-desc" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-plus";
            msg = "B must be Desc";
            expected = { tag = "VDesc"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.DPlusR
          leaf);
      expected = hints."DPlusR::not-a-desc";
    };
    "resolve-AnnTerm-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "ann";
            msg = "term does not match annotation";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.AnnTerm
          leaf);
      expected = hints."AnnTerm::type-mismatch";
    };
    "resolve-AppHead-not-a-function" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "app";
            msg = "expected function type";
            expected = { tag = "VPi"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.AppHead
          leaf);
      expected = hints."AppHead::not-a-function";
    };
    "resolve-AppArg-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "app";
            msg = "arg mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.AppArg
          leaf);
      expected = hints."AppArg::type-mismatch";
    };
    "resolve-MuIndex-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-con";
            msg = "target index mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.MuIndex
          leaf);
      expected = hints."MuIndex::type-mismatch";
    };
    "resolve-MuPayload-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "desc-con";
            msg = "payload mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.MuPayload
          leaf);
      expected = hints."MuPayload::type-mismatch";
    };
    "resolve-OpaqueType-not-a-function" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "opaque-lam";
            msg = "annotation must be Pi";
            expected = { tag = "VPi"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.OpaqueType
          leaf);
      expected = hints."OpaqueType::not-a-function";
    };
    "resolve-OpaqueType-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "opaque-lam";
            msg = "domain mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.OpaqueType
          leaf);
      expected = hints."OpaqueType::type-mismatch";
    };
    "resolve-Motive-not-a-type" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkMotive";
            msg = "motive must return a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.Motive
          leaf);
      expected = hints."Motive::not-a-type";
    };
    "resolve-JType-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "j";
            msg = "type mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.JType
          leaf);
      expected = hints."JType::type-mismatch";
    };

    # -- resolve: Generic-layer positions and eliminator case-bodies. --
    "resolve-Field-inhabitation-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = 42;
            msg = "field is not a String";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Field "name")
          leaf);
      expected = hints."Field::inhabitation-failed";
    };
    "resolve-Field-refinement-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = 17;
            guard = { predicate = "x > 18"; };
            msg = "refinement failed";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Field "age")
          leaf);
      expected = hints."Field::refinement-failed";
    };
    "resolve-Elem-inhabitation-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = "bad";
            msg = "element is not an Int";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Elem 3)
          leaf);
      expected = hints."Elem::inhabitation-failed";
    };
    "resolve-Elem-refinement-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = (-5);
            guard = { predicate = "x >= 0"; };
            msg = "refinement failed";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Elem 0)
          leaf);
      expected = hints."Elem::refinement-failed";
    };
    "resolve-Tag-inhabitation-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = 42;
            msg = "payload does not inhabit branch type";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Tag "Some")
          leaf);
      expected = hints."Tag::inhabitation-failed";
    };
    "resolve-Tag-refinement-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = 3;
            guard = { predicate = "x > 10"; };
            msg = "refinement failed";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Tag "Big")
          leaf);
      expected = hints."Tag::refinement-failed";
    };
    "resolve-Case-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "elim";
            msg = "case body mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Case "succ")
          leaf);
      expected = hints."Case::type-mismatch";
    };
    "resolve-SigmaFst-inhabitation-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = "bad";
            msg = "fst does not inhabit";
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.SigmaFst
          leaf);
      expected = hints."SigmaFst::inhabitation-failed";
    };
    "resolve-SigmaSnd-inhabitation-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = "bad";
            msg = "snd does not inhabit";
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.SigmaSnd
          leaf);
      expected = hints."SigmaSnd::inhabitation-failed";
    };
    "resolve-SigmaFst-refinement-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = (-1);
            guard = { predicate = "x >= 0"; };
            msg = "refinement";
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.SigmaFst
          leaf);
      expected = hints."SigmaFst::refinement-failed";
    };
    "resolve-SigmaSnd-refinement-failed" = {
      expr =
        let
          leaf = fx.diag.error.mkGenericError {
            value = (-1);
            guard = { predicate = "x >= 0"; };
            msg = "refinement";
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.SigmaSnd
          leaf);
      expected = hints."SigmaSnd::refinement-failed";
    };

    # -- resolve: Level-sort positions. --
    "resolve-LevelSucPred-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "level-suc";
            msg = "pred must be Level";
            expected = { tag = "VLevel"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.LevelSucPred
          leaf);
      expected = hints."LevelSucPred::type-mismatch";
    };
    "resolve-LevelMaxLhs-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "level-max";
            msg = "lhs must be Level";
            expected = { tag = "VLevel"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.LevelMaxLhs
          leaf);
      expected = hints."LevelMaxLhs::type-mismatch";
    };
    "resolve-LevelMaxRhs-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "level-max";
            msg = "rhs must be Level";
            expected = { tag = "VLevel"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.LevelMaxRhs
          leaf);
      expected = hints."LevelMaxRhs::type-mismatch";
    };
    "resolve-ULevel-type-mismatch" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "U";
            msg = "level argument must be Level";
            expected = { tag = "VLevel"; };
            got = { tag = "VUnit"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.ULevel
          leaf);
      expected = hints."ULevel::type-mismatch";
    };

    # -- resolve: unhandled-shape family routes through the wildcard
    # bucket regardless of leaf position, so the catch-all infer
    # failure always surfaces a shape-aware hint.
    "resolve-unhandled-pair-under-Sub" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "infer";
            msg = "no inference rule for term shape pair";
            expected = null;
            got = null;
            term = { tag = "pair"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.Sub
          leaf);
      expected = hints."::unhandled-pair";
    };
    "resolve-unhandled-tt-under-AppHead" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "infer";
            msg = "no inference rule for term shape tt";
            expected = null;
            got = null;
            term = { tag = "tt"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.AppHead
          leaf);
      expected = hints."::unhandled-tt";
    };
    "resolve-unhandled-other-fallback" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "infer";
            msg = "no inference rule for term shape mystery";
            expected = null;
            got = null;
            term = { tag = "mystery"; };
          };
        in
        resolve (fx.diag.error.nestUnder
          fx.diag.positions.Sub
          leaf);
      expected = hints."::unhandled-other";
    };
    # -- resolve: Contract-layer leaf with refinement guard routes
    # through the Field::refinement-failed key when nested under Field,
    # confirming Contract dispatch shares hints with Generic refinement.
    "resolve-Contract-refinement-failed-under-Field" = {
      expr =
        let
          leaf = fx.diag.error.mkContractError {
            value = (-1);
            guard = { predicate = "x >= 0"; };
            msg = "contract failed";
          };
        in
        resolve (fx.diag.error.nestUnder
          (fx.diag.positions.Field "age")
          leaf);
      expected = hints."Field::refinement-failed";
    };
  };

  value = {
    resolve = api.leaf {
      value = resolve;
      description = "resolve: walk a blame path inward from leaf to root, returning the `Hint` under the longest matching suffix-key — the canonical lookup for surfacing position-semantic guidance on a kernel `Error`.";
      signature = "resolve : Error -> Hint | null";
    };
    classify = api.leaf {
      value = classify;
      description = "classify: derive the classifier pattern string from an `Error`'s detail and leaf position — yields the right-hand side of suffix-keys consumed by `resolve` (e.g. `\"universe-mismatch\"`).";
      signature = "classify : Error -> String";
    };
    hints = api.leaf {
      value = hints;
      description = "hints: the closed `{ key = Hint }` registry indexed by `<pos1>.<pos2>...<posN>::<pattern>` keys; each value carries `text`, `category`, `severity`, `docLink` to the per-key `/nix-effects/diag-hints/<slug>` page.";
    };
    mkHint = api.leaf {
      value = mkHint;
      description = "mkHint: structured `Hint` constructor from a `category` and `text` — sets `_tag = \"Hint\"` (terminal for `extractValue`), `severity = \"error\"`, and the default `docLink` pointing at the diag-hints section root.";
      signature = "mkHint : Category -> String -> Hint";
    };
    taxonomy = api.leaf {
      value = taxonomy;
      description = "taxonomy: closed list of allowed `Hint.category` values (`\"universe\"`, `\"sort\"`, `\"description\"`, `\"arity\"`, `\"indexing\"`, `\"inhabitation\"`, …); enforced by the `hints-categories-in-taxonomy` test.";
    };

  };
}) // {
  docs = {
    examples = hintExamples;
  };
}
