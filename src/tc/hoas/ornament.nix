# First-class ornaments over levitated descriptions.
{ self, fx, api, ... }:

let
  isOrn = x:
    builtins.isAttrs x && (x._ornTag or null) == "orn";

  levelOf = D:
    if builtins.isAttrs D && D ? k then D.k else 0;

  idErase = I:
    self.ann
      (self.lam "i" I (i: i))
      (self.forall "_" I (_: I));

  mkOrn = { I, J, erase, baseD, node, level ? levelOf baseD, meta ? { } }:
    { _ornTag = "orn"; inherit I J erase baseD node level meta; };

  isAlg = x:
    builtins.isAttrs x && (x._algOrnTag or null) == "alg";

  isFunctionalOrn = x:
    builtins.isAttrs x && (x._functionalOrnTag or null) == "functional-ornament";

  isLeafOrn = x:
    builtins.isAttrs x && (x._leafOrnTag or null) == "leaf-ornament";

  mkDiagnostic = { code, path ? [ ], message, text ? message }:
    { inherit code path message text; severity = "error"; };

  diagnosticText = d:
    d.text or d.message;

  ensureOrn = label: O:
    if isOrn O then O
    else throw "hoas.${label}: expected ornament";

  ensureAlg = label: alg:
    if isAlg alg then alg
    else throw "hoas.${label}: expected algebraic ornament descriptor";

  ensureFunctionalOrn = label: F:
    if isFunctionalOrn F then F
    else throw "hoas.${label}: expected functional ornament";

  ensureOrnLike = label: x:
    if isFunctionalOrn x then x.ornament else ensureOrn label x;

  functionalDiagnostic = code: path: message:
    mkDiagnostic {
      inherit code path message;
      text = "hoas.functionalOrnament: ${message}";
    };

  functionalFieldDiagnostic = code: field: message:
    functionalDiagnostic code [ "functionalOrnament" field ] message;

  functionalOrnamentDiagnosticRecords = args:
    if !(builtins.isAttrs args) then
      [ (functionalDiagnostic "functional.invalid-spec" [ "functionalOrnament" ] "expected attrset spec") ]
    else
      (if !(args ? ornament) then
        [ (functionalFieldDiagnostic "functional.missing-ornament" "ornament" "functional ornament needs `ornament`") ]
      else if !(isOrn args.ornament) then
        [ (functionalFieldDiagnostic "functional.invalid-ornament" "ornament" "functional ornament `ornament` must be an ornament") ]
      else [ ])
      ++ (if !(args ? chooseIndex) then
        [ (functionalFieldDiagnostic "functional.missing-choose-index" "chooseIndex" "functional ornament needs `chooseIndex`") ]
      else if !(builtins.isFunction args.chooseIndex) then
        [ (functionalFieldDiagnostic "functional.invalid-choose-index" "chooseIndex" "functional ornament `chooseIndex` must be a function") ]
      else [ ])
      ++ (if !(args ? section) then
        [ (functionalFieldDiagnostic "functional.missing-section" "section" "functional ornament needs `section`") ]
      else if !(builtins.isFunction args.section) then
        [ (functionalFieldDiagnostic "functional.invalid-section" "section" "functional ornament `section` must be a function") ]
      else [ ])
      ++ (if args ? indexProof && !(builtins.isFunction args.indexProof) then
        [ (functionalFieldDiagnostic "functional.invalid-index-proof" "indexProof" "functional ornament `indexProof` must be a function") ]
      else [ ]);

  validateFunctionalOrnament = args:
    let diagnostics = functionalOrnamentDiagnosticRecords args; in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; }
    else { ok = false; inherit diagnostics; };

  functionalOrnamentDiagnostics = args:
    map diagnosticText (functionalOrnamentDiagnosticRecords args);

  functionalOrnament = args:
    let
      validation = validateFunctionalOrnament args;
    in
    if !(validation.ok) then
      throw (builtins.concatStringsSep "\n" (map diagnosticText validation.diagnostics))
    else {
      _functionalOrnTag = "functional-ornament";
      ornament = ensureOrn "functionalOrnament" args.ornament;
      chooseIndex = args.chooseIndex;
      indexProof = args.indexProof or (_i: _x: self.bootRefl);
      section = args.section;
      laws = args.laws or { };
      meta = args.meta or { };
    };

  tryFunctionalOrnament = args:
    let validation = validateFunctionalOrnament args; in
    if validation.ok then validation // { value = functionalOrnament args; }
    else validation;

  ornSection = F:
    (ensureFunctionalOrn "ornSection" F).section;

  ornTargetIndex = F:
    (ensureFunctionalOrn "ornTargetIndex" F).chooseIndex;

  ornIndexProof = F:
    (ensureFunctionalOrn "ornIndexProof" F).indexProof;

  ornBuild = F: i: baseValue:
    (ornSection F) i baseValue;

  functionalLawDiagnostic = code: name: message:
    mkDiagnostic {
      inherit code message;
      path = [ "functionalOrnament" "laws" name ];
      text = "hoas.functionalOrnament: law '${name}': ${message}";
    };

  functionalLawChecks = F:
    let
      laws = (ensureFunctionalOrn "validateFunctionalLaws" F).laws;
    in
    if laws ? checks && builtins.isAttrs laws.checks then laws.checks else { };

  functionalLawDiagnosticRecords = F:
    let
      checked = ensureFunctionalOrn "validateFunctionalLaws" F;
      checks = functionalLawChecks checked;
      checkOne = name: check:
        let
          result = builtins.tryEval (if builtins.isFunction check then check checked else check);
        in
        if !(result.success) then
          [ (functionalLawDiagnostic "functional.law-eval-failed" name "law check failed to evaluate") ]
        else if result.value == true then
          [ ]
        else
          [ (functionalLawDiagnostic "functional.law-failed" name "law check failed") ];
    in
    builtins.concatLists (builtins.attrValues (builtins.mapAttrs checkOne checks));

  functionalLawDiagnostics = F:
    map diagnosticText (functionalLawDiagnosticRecords F);

  validateFunctionalLaws = F:
    let diagnostics = functionalLawDiagnosticRecords F; in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; }
    else { ok = false; inherit diagnostics; };

  checkFunctionalLaws = F:
    let validation = validateFunctionalLaws F; in
    if validation.ok then F
    else throw (builtins.concatStringsSep "\n" (map diagnosticText validation.diagnostics));

  functionalCompose = outer: inner:
    let
      fOuter = ensureFunctionalOrn "functionalCompose" outer;
      fInner = ensureFunctionalOrn "functionalCompose" inner;
      section = i: baseValue:
        let
          mid = fInner.chooseIndex i baseValue;
          innerValue = fInner.section i baseValue;
        in
        fOuter.section mid innerValue;
      chooseIndex = i: baseValue:
        let
          mid = fInner.chooseIndex i baseValue;
          innerValue = fInner.section i baseValue;
        in
        fOuter.chooseIndex mid innerValue;
    in
    functionalOrnament {
      ornament = compose fOuter.ornament fInner.ornament;
      chooseIndex = chooseIndex;
      indexProof = _i: _baseValue: self.bootRefl;
      section = section;
      laws = {
        checks = { };
        composed = true;
      };
      meta = {
        kind = "compose";
        outer = fOuter;
        inner = fInner;
      };
    };

  # Leaf functional ornaments: refinements of primitive HOAS type
  # formers (`_htag ≠ "mu"`) carrying Nix-meta `forget` / `section`.
  # Dagand–McBride 2014 (JFP) functional ornaments specialised to the
  # case where the underlying type former is primitive.
  leafDiagnostic = code: path: message:
    mkDiagnostic {
      inherit code path message;
      text = "hoas.leafOrnament: ${message}";
    };

  leafFieldDiagnostic = code: field: message:
    leafDiagnostic code [ "leafOrnament" field ] message;

  primitiveIsMu = p:
    builtins.isAttrs p && (p._htag or null) == "mu";

  primitiveIsOrnamentLike = p:
    isOrn p || isFunctionalOrn p || isLeafOrn p;

  leafOrnamentDiagnosticRecords = args:
    if !(builtins.isAttrs args) then
      [ (leafDiagnostic "leaf.invalid-spec" [ "leafOrnament" ] "expected attrset spec") ]
    else
      (if !(args ? primitive) then
        [ (leafFieldDiagnostic "leaf.missing-primitive" "primitive" "leaf ornament needs `primitive`") ]
      else if !(builtins.isAttrs args.primitive && args.primitive ? _htag) then
        [ (leafFieldDiagnostic "leaf.invalid-primitive" "primitive" "leaf ornament `primitive` must be a HOAS type former with an `_htag` field") ]
      else if primitiveIsMu args.primitive then
        [ (leafFieldDiagnostic "leaf.invalid-primitive" "primitive" "leaf ornament `primitive` must be a primitive HOAS type former, not a μ-encoded type; use ornament/functionalOrnament for μ-encoded bases") ]
      else if primitiveIsOrnamentLike args.primitive then
        [ (leafFieldDiagnostic "leaf.invalid-primitive" "primitive" "leaf ornament `primitive` must be a raw type former, not an already-ornamented value") ]
      else [ ])
      ++ (if !(args ? forget) then
        [ (leafFieldDiagnostic "leaf.missing-forget" "forget" "leaf ornament needs `forget`") ]
      else if !(builtins.isFunction args.forget) then
        [ (leafFieldDiagnostic "leaf.invalid-forget" "forget" "leaf ornament `forget` must be a function (Refined → Base) at the Nix-meta level") ]
      else [ ])
      ++ (if !(args ? section) then
        [ (leafFieldDiagnostic "leaf.missing-section" "section" "leaf ornament needs `section`") ]
      else if !(builtins.isFunction args.section) then
        [ (leafFieldDiagnostic "leaf.invalid-section" "section" "leaf ornament `section` must be a function (Base → Refined) at the Nix-meta level") ]
      else [ ])
      ++ (if args ? sectionProof && !(builtins.isFunction args.sectionProof) then
        [ (leafFieldDiagnostic "leaf.invalid-section-proof" "sectionProof" "leaf ornament `sectionProof` must be a function") ]
      else [ ]);

  leafOrnamentDiagnostics = args:
    map diagnosticText (leafOrnamentDiagnosticRecords args);

  validateLeafOrnament = args:
    let diagnostics = leafOrnamentDiagnosticRecords args; in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; }
    else { ok = false; inherit diagnostics; };

  leafOrnament = args:
    let
      validation = validateLeafOrnament args;
    in
    if !(validation.ok) then
      throw (builtins.concatStringsSep "\n" (map diagnosticText validation.diagnostics))
    else {
      _leafOrnTag = "leaf-ornament";
      primitive = args.primitive;
      forget = args.forget;
      section = args.section;
      sectionProof = args.sectionProof or (_x: true);
      meta = args.meta or { };
    };

  tryLeafOrnament = args:
    let validation = validateLeafOrnament args; in
    if validation.ok then validation // { value = leafOrnament args; }
    else validation;

  ensureLeafOrn = label: x:
    if isLeafOrn x then x
    else throw "hoas.${label}: expected leaf ornament";

  thunkOrnament = inner:
    leafOrnament {
      primitive = self.thunk inner;
      forget = fx.state.thunk.forceThunk;
      section = fx.state.thunk.mkThunk;
      sectionProof = _x: true;
      meta = {
        name = "Thunk";
        baseHtag = "thunk";
        inner = inner;
      };
    };

  descArgLike = I: k: maybeL: S: body:
    if maybeL == null
    then self.descArg I k S body
    else self.descArgAt I maybeL k S body;

  descPiLike = I: k: maybeL: S: f: tail:
    if maybeL == null
    then self.piI I k S f tail
    else self.piIAt I maybeL k S f tail;

  retTransport = O: i: d:
    let
      node = O.node;
      eqToBaseAt = x: self.bootEq O.I node.baseIndex (self.app O.erase x);
      motive =
        self.lam "x" O.J (x:
          self.lam "_e" (self.bootEq O.J node.j x) (_:
            eqToBaseAt x));
    in
    self.bootJ O.J node.j motive node.proof i d;

  ornDescRaw = O:
    let
      orn = ensureOrn "ornDesc" O;
      node = orn.node;
      k = orn.level;
    in
    if node.tag == "ret" then
      self.retI orn.J k node.j
    else if node.tag == "argKeep" then
      descArgLike orn.J k (node.l or null) node.S
        (s: ornDesc (node.body s))
    else if node.tag == "argKeepSub" then
      descArgLike orn.J k (node.l or null) node.S
        (s: ornDesc (node.body s))
    else if node.tag == "argInsert" then
      descArgLike orn.J k (node.l or null) node.S
        (s: ornDesc (node.body s))
    else if node.tag == "rec" then
      self.recI orn.J k node.j (ornDesc node.tail)
    else if node.tag == "piKeep" then
      descPiLike orn.J k (node.l or null) node.S node.ornF (ornDesc node.tail)
    else if node.tag == "plus" then
      self.plusI orn.J k (ornDesc node.left) (ornDesc node.right)
    else if node.tag == "compose" then
      ornDescRaw node.outer
    else
      throw "hoas.ornDesc: unknown ornament node '${node.tag}'";

  ornDesc = O:
    let orn = ensureOrn "ornDesc" O; in
    self.ann (ornDescRaw orn) (self.descIAt orn.level orn.J);

  ornMu = O: j:
    let orn = ensureOrn "ornMu" O; in
    self.muI orn.J (ornDesc orn) j;

  recPayload = O: i: d: ih: ctx:
    let
      node = O.node;
      src = self.app O.erase node.j;
      dst = node.baseIndex;
      recTy = ctx.baseMuAt;
      recTransport =
        let
          motive =
            self.lam "i'" O.I (i':
              self.lam "_e" (self.bootEq O.I dst i') (_:
                self.forall "_" (recTy i') (_: recTy dst)));
          identity = self.lam "x" (recTy dst) (x: x);
        in
        self.app (self.bootJ O.I dst motive identity src node.proof) (self.fst_ ih);
      subTail = forgetPayload node.tail i (self.snd_ d) (self.snd_ ih) ctx;
    in
    self.pair recTransport subTail;

  piBranchTransport = O: node: ctx: s: h:
    let
      src = self.app O.erase (self.app node.ornF s);
      dst = self.app node.baseF s;
      recTy = ctx.baseMuAt;
      motive =
        self.lam "i'" O.I (i':
          self.lam "_e" (self.bootEq O.I dst i') (_:
            self.forall "_" (recTy i') (_: recTy dst)));
      identity = self.lam "x" (recTy dst) (x: x);
    in
    self.app (self.bootJ O.I dst motive identity src (node.proof s)) h;

  piPayload = O: node: ih: ctx:
    self.ann
      (self.lam "s" node.S (s:
        piBranchTransport O node ctx s (self.app (self.fst_ ih) s)))
      (self.forall "_" node.S (s:
        ctx.baseMuAt (self.app node.baseF s)));

  plusPayload = O: i: d: ih: ctx:
    let
      node = O.node;
      left = node.left;
      right = node.right;
      leftD = ornDesc left;
      rightD = ornDesc right;
      ornD = ornDesc O;
      baseD = O.baseD;
      jBase = self.app O.erase i;
      leftTy = self.interpD O.level O.J leftD ctx.ornMuFam i;
      rightTy = self.interpD O.level O.J rightD ctx.ornMuFam i;
      baseLeftTy = self.interpD O.level O.I left.baseD ctx.baseMuFam jBase;
      baseRightTy = self.interpD O.level O.I right.baseD ctx.baseMuFam jBase;
      resultTy = self.interpD O.level O.I baseD ctx.baseMuFam jBase;
      allFor = payload:
        self.allD O.level O.J ornD 0 ctx.ornMuFam ctx.motive i payload;
      branchMotive =
        self.lam "payload" (self.bootSum leftTy rightTy) (payload:
          self.forall "_" (allFor payload) (_: resultTy));
      onLeft =
        self.lam "a" leftTy (a:
          self.lam "h" (allFor (self.bootInl leftTy rightTy a)) (h:
            self.bootInl baseLeftTy baseRightTy
              (forgetPayload left i a h ctx)));
      onRight =
        self.lam "b" rightTy (b:
          self.lam "h" (allFor (self.bootInr leftTy rightTy b)) (h:
            self.bootInr baseLeftTy baseRightTy
              (forgetPayload right i b h ctx)));
    in
    self.app (self.bootSumElim leftTy rightTy branchMotive onLeft onRight d) ih;

  # Leaf-ornament subs carry Nix-meta `forget`. Their forward
  # type and base type differ structurally (e.g. `thunk T → T`)
  # and the HOAS evaluator has no primitive that crosses that
  # boundary. The proof-side here is a typed identity stub at
  # the refined type; the operational forget is supplied by the
  # meta-level walker in `generic/ornaments.nix`.
  argKeepSubHoasField = node: fieldValue:
    if isOrn node.sub then
      let
        subOrn = node.sub;
        subJ = subOrn.J;
        idx =
          if isUnitTy subJ then self.ttPrim
          else throw "hoas.ornForget: μ-ornament sub at argKeepSub requires unit index; got non-unit ${subJ._htag or "<unknown>"}";
      in
      self.app (self.app (ornForget subOrn) idx) fieldValue
    else if isLeafOrn node.sub then fieldValue
    else throw "hoas.ornForget: argKeepSub sub must be a raw or leaf ornament";

  forgetPayload = O: i: d: ih: ctx:
    let
      orn = ensureOrn "ornForget" O;
      node = orn.node;
    in
    if node.tag == "ret" then
      retTransport orn i d
    else if node.tag == "argKeep" then
      self.pair (self.fst_ d)
        (forgetPayload (node.body (self.fst_ d)) i (self.snd_ d) ih ctx)
    else if node.tag == "argKeepSub" then
      self.pair (argKeepSubHoasField node (self.fst_ d))
        (forgetPayload (node.body (self.fst_ d)) i (self.snd_ d) ih ctx)
    else if node.tag == "argInsert" then
      forgetPayload (node.body (self.fst_ d)) i (self.snd_ d) ih ctx
    else if node.tag == "rec" then
      recPayload orn i d ih ctx
    else if node.tag == "piKeep" then
      self.pair (piPayload orn node ih ctx)
        (forgetPayload node.tail i (self.snd_ d) (self.snd_ ih) ctx)
    else if node.tag == "plus" then
      plusPayload orn i d ih ctx
    else
      throw "hoas.ornForget: unsupported ornament node '${node.tag}'";

  directForget = O:
    let
      ornD = ornDesc O;
      muFam = self.lam "j" O.J (j: self.muI O.J ornD j);
      baseMuAt = i: self.muI O.I O.baseD i;
      baseMuFam = self.lam "i" O.I (i: self.muI O.I O.baseD i);
      motive =
        self.lam "j" O.J (j:
          self.lam "_" (self.muI O.J ornD j) (_:
            self.muI O.I O.baseD (self.app O.erase j)));
      step =
        self.lam "j" O.J (j:
          self.lam "d" (self.interpD O.level O.J ornD muFam j) (d:
            self.lam "ih" (self.allD O.level O.J ornD 0 muFam motive j d) (ih:
              self.descCon O.baseD (self.app O.erase j)
                (forgetPayload O j d ih {
                  ornMuFam = muFam;
                  inherit baseMuAt baseMuFam motive;
                }))));
    in
    self.ann
      (self.lam "j" O.J (j:
        self.lam "x" (self.muI O.J ornD j) (x:
          self.descInd ornD motive step j x)))
      (self.forall "j" O.J (j:
        self.forall "_" (self.muI O.J ornD j) (_:
          self.muI O.I O.baseD (self.app O.erase j))));

  composeForget = O:
    let
      outer = O.node.outer;
      inner = O.node.inner;
    in
    self.ann
      (self.lam "j" outer.J (j:
        self.lam "x" (self.muI outer.J (ornDesc outer) j) (x:
          self.app
            (self.app (ornForget inner) (self.app outer.erase j))
            (self.app (self.app (ornForget outer) j) x))))
      (self.forall "j" outer.J (j:
        self.forall "_" (self.muI outer.J (ornDesc outer) j) (_:
          self.muI inner.I inner.baseD
            (self.app inner.erase (self.app outer.erase j)))));

  ornForget = O:
    let orn = ensureOrn "ornForget" O; in
    if orn.node.tag == "compose" then composeForget orn else directForget orn;

  ornPullback = O: resultTy: baseFn:
    let
      orn = ensureOrn "ornPullback" O;
      ornD = ornDesc orn;
      forget = ornForget orn;
    in
    self.ann
      (self.lam "j" orn.J (j:
        self.lam "x" (self.muI orn.J ornD j) (x:
          self.app
            (self.app baseFn (self.app orn.erase j))
            (self.app (self.app forget j) x))))
      (self.forall "j" orn.J (j:
        self.forall "_" (self.muI orn.J ornD j) (_:
          resultTy (self.app orn.erase j))));

  ornLiftFold = O: resultTy: baseFold:
    ornPullback O resultTy baseFold;

  ornLiftProducer = F: baseFn: i: baseInput:
    let functional = ensureFunctionalOrn "ornLiftProducer" F; in
    ornBuild functional i (self.app baseFn baseInput);

  ornLiftTransform = args: outputIndex: inputIndex: ornamentedInput:
    let
      input = ensureOrnLike "ornLiftTransform.input" args.input;
      output = ensureFunctionalOrn "ornLiftTransform.output" args.output;
      baseInput =
        self.app
          (self.app (ornForget input) inputIndex)
          ornamentedInput;
    in
    ornBuild output outputIndex (self.app args.fn baseInput);

  idNode = I: D:
    if !(builtins.isAttrs D) || !(D ? _htag) then
      throw "hoas.ornId: expected syntactic HOAS description"
    else if D._htag == "ann" then
      idNode I D.term
    else if D._htag == "desc-ret-enc" then
      {
        tag = "ret";
        j = D.j;
        proof = self.bootRefl;
        baseIndex = D.j;
      }
    else if D._htag == "desc-arg-enc" then
      {
        tag = "argKeep";
        S = D.S;
        l = D.l or null;
        body = s: ornId I (D.body s);
      }
    else if D._htag == "desc-rec-enc" then
      {
        tag = "rec";
        j = D.j;
        proof = self.bootRefl;
        baseIndex = D.j;
        tail = ornId I D.D;
      }
    else if D._htag == "desc-pi-enc" then
      {
        tag = "piKeep";
        S = D.S;
        baseF = D.f;
        ornF = D.f;
        proof = _: self.bootRefl;
        l = D.l or null;
        tail = ornId I D.D;
      }
    else if D._htag == "desc-plus-enc" then
      {
        tag = "plus";
        left = ornId I D.A;
        right = ornId I D.B;
      }
    else
      throw "hoas.ornId: unsupported description form '${D._htag}'";

  ornId = I: D:
    mkOrn {
      inherit I;
      J = I;
      erase = idErase I;
      baseD = D;
      level = levelOf D;
      node = idNode I D;
    };

  compose = outer: inner:
    let
      o2 = ensureOrn "ornCompose" outer;
      o1 = ensureOrn "ornCompose" inner;
    in
    mkOrn {
      I = o1.I;
      J = o2.J;
      baseD = o1.baseD;
      level = o1.level;
      erase =
        self.ann
          (self.lam "j" o2.J (j: self.app o1.erase (self.app o2.erase j)))
          (self.forall "_" o2.J (_: o1.I));
      node = { tag = "compose"; outer = o2; inner = o1; };
    };

  mkAlg = tag: payload:
    { _algOrnTag = "alg"; inherit tag; } // payload;

  descLabel = D:
    if D._htag == "ann" then descLabel D.term
    else if D._htag == "desc-ret-enc" then "descRet"
    else if D._htag == "desc-arg-enc" then "descArg"
    else if D._htag == "desc-rec-enc" then "descRec"
    else if D._htag == "desc-plus-enc" then "descPlus"
    else if D._htag == "desc-pi-enc" then "descPi"
    else D._htag or "unknown";

  algTag = alg:
    if isAlg alg then alg.tag else "non-algebra";

  algDiagnostic = code: path: message:
    mkDiagnostic {
      inherit code path message;
      text = "hoas.algOrn: path ${path}: ${message}";
    };

  algMismatchMessage = expected: D: got:
    "expected ${expected} algebra for ${descLabel D}, got ${got}";

  algMismatch = path: expected: D: got:
    "hoas.algOrn: path ${path}: ${algMismatchMessage expected D got}";

  algMismatchDiagnostic = path: expected: D: got:
    algDiagnostic "algOrn.shape-mismatch" path
      (algMismatchMessage expected D got);

  sampleAlgBodyResult = path: body:
    let r = builtins.tryEval (body self.ttPrim);
    in if r.success then { ok = true; value = r.value; diagnostics = [ ]; }
    else {
      ok = false;
      diagnostics = [
        (algDiagnostic "algOrn.sample-failed" path
          "algebra body could not be sampled for shape checking")
      ];
    };

  sampleAlgBody = path: body:
    let r = sampleAlgBodyResult path body;
    in if r.ok then r.value
    else throw (builtins.concatStringsSep "\n" (map diagnosticText r.diagnostics));

  algPiBranchFn = cfg: path: D: node:
    if node ? ornF then node.ornF
    else if node ? branch then node.branch
    else if node ? branchIndex then
      self.ann
        (self.lam "s" D.S (s: node.branchIndex s))
        (self.forall "_" D.S (_: cfg.J))
    else if node ? branchIdxFn then
      self.ann
        (self.lam "s" D.S (s: node.branchIdxFn s))
        (self.forall "_" D.S (_: cfg.J))
    else if isUnitTy cfg.J then unitBranch D.S
    else throw "hoas.algOrn: path ${path}: descPi keep algebra needs `branchIndex`";

  algPiProof = node:
    if node ? proof then node.proof else _: self.bootRefl;

  # Shape-check an algebra against its target description, collecting every
  # mismatch as a diagnostic record (empty on success). The walk is a
  # pre-order traversal of the description: each form either emits one
  # terminal diagnostic (mismatch / unsupported / sample failure) or descends
  # into its children with no emission of its own, so the flat record list is
  # exactly the left-to-right concatenation of the leaf emissions. The
  # traversal runs on a `genericClosure` cons-stack rather than host recursion,
  # so its depth scales with memory, not the call stack.
  algShapeDiagnosticRecordsAt = path: D: alg:
    let
      # Push a frame list so frame 0 becomes the new head, preserving the
      # left-to-right pre-order of the original recursion.
      pushAll = frames: s:
        let n = builtins.length frames;
        in builtins.foldl'
          (st: i: { head = builtins.elemAt frames (n - 1 - i); tail = st; })
          s
          (builtins.genList (x: x) n);
      # One traversal step: a `{ path; D; alg }` frame yields the diagnostics
      # emitted here plus the child frames to descend into. `ret` on a matching
      # algebra emits nothing and has no children.
      step = frame:
        let
          path = frame.path;
          D = frame.D;
          alg = frame.alg;
          node = if isAlg alg then alg else null;
          got = algTag alg;
        in
        if D._htag == "ann" then { emit = [ ]; children = [ (frame // { D = D.term; }) ]; }
        else if D._htag == "desc-ret-enc" then
          if node == null || node.tag != "ret"
          then { emit = [ (algMismatchDiagnostic path "ret" D got) ]; children = [ ]; }
          else { emit = [ ]; children = [ ]; }
        else if D._htag == "desc-arg-enc" then
          if node == null || node.tag != "arg"
          then { emit = [ (algMismatchDiagnostic path "arg" D got) ]; children = [ ]; }
          else
            let sampled = sampleAlgBodyResult path node.body; in
            if !sampled.ok then { emit = sampled.diagnostics; children = [ ]; }
            else { emit = [ ]; children = [ { path = "${path}.arg"; D = D.body self.ttPrim; alg = sampled.value; } ]; }
        else if D._htag == "desc-rec-enc" then
          if node == null || node.tag != "rec"
          then { emit = [ (algMismatchDiagnostic path "rec" D got) ]; children = [ ]; }
          else
            let sampled = sampleAlgBodyResult path node.body; in
            if !sampled.ok then { emit = sampled.diagnostics; children = [ ]; }
            else { emit = [ ]; children = [ { path = "${path}.rec"; D = D.D; alg = sampled.value; } ]; }
        else if D._htag == "desc-plus-enc" then
          if node == null || node.tag != "plus"
          then { emit = [ (algMismatchDiagnostic path "plus" D got) ]; children = [ ]; }
          else { emit = [ ]; children = [
            { path = "${path}.left"; D = D.A; alg = node.left; }
            { path = "${path}.right"; D = D.B; alg = node.right; }
          ]; }
        else if D._htag == "desc-pi-enc" then
          if node == null || node.tag != "pi"
          then { emit = [ (algMismatchDiagnostic path "pi" D got) ]; children = [ ]; }
          else { emit = [ ]; children = [ { path = "${path}.pi"; D = D.D; alg = node.body; } ]; }
        else
          {
            emit = [
              (algDiagnostic "algOrn.unsupported-description" path
                "unsupported description form '${descLabel D}'")
            ];
            children = [ ];
          };
      closure = builtins.genericClosure {
        startSet = [ { key = 0; stack = pushAll [ { inherit path D alg; } ] null; acc = [ ]; } ];
        operator = item:
          if item.stack == null then [ ]
          else
            let
              s = step item.stack.head;
              # Force the accumulator each step: a lazily-threaded `++` chain
              # would defer an n-deep force back onto the host stack.
              nextAcc = item.acc ++ s.emit;
            in builtins.seq nextAcc [{
              key = item.key + 1;
              stack = pushAll s.children item.stack.tail;
              acc = nextAcc;
            }];
      };
      final = builtins.head (builtins.filter (it: it.stack == null) closure);
    in final.acc;

  algShapeDiagnosticsAt = path: D: alg:
    map diagnosticText (algShapeDiagnosticRecordsAt path D alg);

  algNode = cfg: path: D: alg:
    let
      node = ensureAlg "algOrn" alg;
      build = path_: D_: alg_: algOrnAt cfg path_ D_ alg_;
      l = D.l or null;
    in
    if D._htag == "ann" then algNode cfg path D.term node
    else if D._htag == "desc-ret-enc" then
      if node.tag != "ret" then
        throw (algMismatch path "ret" D node.tag)
      else {
        tag = "ret";
        j = cfg.pack D.j node.result;
        proof = cfg.proof D.j node.result;
        baseIndex = D.j;
      }
    else if D._htag == "desc-arg-enc" then
      if node.tag != "arg" then
        throw (algMismatch path "arg" D node.tag)
      else {
        tag = "argKeep";
        S = D.S;
        inherit l;
        body = s: build "${path}.arg" (D.body s) (node.body s);
      }
    else if D._htag == "desc-rec-enc" then
      if node.tag != "rec" then
        throw (algMismatch path "rec" D node.tag)
      else {
        tag = "argInsert";
        S = cfg.resultTy D.j;
        l = node.level or null;
        body = r:
          mkOrn {
            inherit (cfg) I J erase level;
            baseD = D;
            meta = cfg.meta;
            node = {
              tag = "rec";
              j = cfg.pack D.j r;
              proof = cfg.proof D.j r;
              baseIndex = D.j;
              tail = build "${path}.rec" D.D (node.body r);
            };
          };
      }
    else if D._htag == "desc-plus-enc" then
      if node.tag != "plus" then
        throw (algMismatch path "plus" D node.tag)
      else {
        tag = "plus";
        left = build "${path}.left" D.A node.left;
        right = build "${path}.right" D.B node.right;
      }
    else if D._htag == "desc-pi-enc" then
      if node.tag != "pi" then
        throw (algMismatch path "pi" D node.tag)
      else {
        tag = "piKeep";
        S = D.S;
        baseF = D.f;
        ornF = algPiBranchFn cfg path D node;
        proof = algPiProof node;
        inherit l;
        tail = build "${path}.pi" D.D node.body;
      }
    else
      throw "hoas.algOrn: path ${path}: unsupported description form '${descLabel D}'";

  algOrnAt = cfg: path: D: alg:
    mkOrn {
      inherit (cfg) I J erase level meta;
      baseD = D;
      node = algNode cfg path D alg;
    };

  algOrnDiagnosticRecords = args:
    let D = args.D or args.baseD; in
    algShapeDiagnosticRecordsAt "root" D args.algebra;

  algOrnDiagnostics = args:
    map diagnosticText (algOrnDiagnosticRecords args);

  validateAlgOrn = args:
    let diagnostics = algOrnDiagnosticRecords args; in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; }
    else { ok = false; inherit diagnostics; };

  tryAlgOrn = args:
    let validation = validateAlgOrn args; in
    if validation.ok then validation // { value = algOrn args; }
    else validation;

  algOrn = args:
    let
      I = args.I or self.unitPrim;
      J = args.J;
      D = args.D or args.baseD;
      erase = args.erase;
      resultTy = args.resultTy or (_: J);
      pack = args.pack or (_: result: result);
      proof = args.proof or (_: _: self.bootRefl);
      level = args.level or levelOf D;
      meta = (args.meta or { }) // {
        kind = "algebraic";
        algebra = args.algebra;
      };
      cfg = { inherit I J erase resultTy pack proof level meta; };
      errors = algOrnDiagnostics args;
    in
    if errors != [ ] then throw (builtins.concatStringsSep "\n" errors)
    else algOrnAt cfg "root" D args.algebra;

  unitErase = idErase self.unitPrim;

  withOrnSource = source: h:
    if builtins.isAttrs h then h // { _ornSource = source; } else h;

  namesOf = xs: map (x: x.name) xs;

  duplicateNames = xs:
    (builtins.foldl'
      (acc: x:
        if builtins.elem x acc.seen
        then acc // { duplicates = acc.duplicates ++ [ x ]; }
        else acc // { seen = acc.seen ++ [ x ]; })
      { seen = [ ]; duplicates = [ ]; }
      xs).duplicates;

  ornamentCtx = base: spec:
    {
      datatype = base.name or "<anonymous>";
      ornament = spec.name or "${base.name or "<anonymous>"}Orn";
    };

  ornamentCtxText = ctx:
    "hoas.ornament: datatype '${ctx.datatype}' ornament '${ctx.ornament}'"
    + (if ctx ? constructor then " constructor '${ctx.constructor}'" else "")
    + (if ctx ? field then " field '${ctx.field}'" else "");

  ornamentMsg = ctx: msg:
    "${ornamentCtxText ctx}: ${msg}";

  ornamentPath = ctx:
    [ "datatype:${ctx.datatype or "<unknown>"}" "ornament:${ctx.ornament or "<unknown>"}" ]
    ++ (if ctx ? constructor then [ "constructor:${ctx.constructor}" ] else [ ])
    ++ (if ctx ? field then [ "field:${ctx.field}" ] else [ ]);

  ornamentDiagnostic = code: ctx: message:
    mkDiagnostic {
      inherit code message;
      path = ornamentPath ctx;
      text = ornamentMsg ctx message;
    };

  fieldCtx = ctx: name:
    ctx // { field = name; };

  constructorCtx = ctx: name:
    ctx // { constructor = name; };

  fieldSpecInfo = ctx: spec:
    if spec ? insert && spec ? keep then {
      kind = "invalid";
      name = spec.insert;
      errors = [ (ornamentDiagnostic "ornament.field-conflict" (fieldCtx ctx spec.insert) "field spec must not contain both `keep` and `insert`") ];
    }
    else if spec ? insert then {
      kind = "insert";
      name = spec.insert;
      errors = [ ];
    }
    else if spec ? keep && spec ? sub then {
      kind = "keepSub";
      name = spec.keep;
      errors = [ ];
    }
    else if spec ? keep then {
      kind = "keep";
      name = spec.keep;
      errors = [ ];
    }
    else {
      kind = "invalid";
      name = "<unknown>";
      errors = [ (ornamentDiagnostic "ornament.field-missing-action" ctx "field spec must contain `keep` or `insert`") ];
    };

  # Hint used to surface obvious sub-ornament/kept-field type
  # mismatches at spec-build time. Derived constructors like
  # `thunkOrnament inner` thread the base-side type through
  # `meta.inner`; absent the hint, deep agreement is left for
  # runtime to catch.
  subBaseHint = sub:
    if !(isLeafOrn sub) then null
    else if sub ? meta
      && builtins.isAttrs sub.meta
      && sub.meta ? inner
      && builtins.isAttrs sub.meta.inner
      && sub.meta.inner ? _htag
    then sub.meta.inner._htag
    else null;

  outputFieldDiagnostics = ctx: specs:
    let
      infos = map (fieldSpecInfo ctx) specs;
      names = builtins.filter (n: n != null && n != "<unknown>")
        (map (i: i.name) infos);
      duplicates = duplicateNames names;
    in
    (builtins.concatMap (i: i.errors) infos)
    ++ (map
      (name:
        ornamentDiagnostic "ornament.duplicate-output-field" (fieldCtx ctx name) "duplicate output field")
      duplicates);

  fieldOrderDiagnostics = cfg: ctx: baseFields: specs:
    if specs == [ ] then
      if baseFields == [ ] then [ ]
      else [ (ornamentDiagnostic "ornament.missing-keep" (fieldCtx ctx (builtins.head baseFields).name) "missing keep for base field") ]
    else
      let
        spec = builtins.head specs;
        rest = builtins.tail specs;
        info = fieldSpecInfo ctx spec;
      in
      info.errors ++ (
        if info.kind == "insert" then
          (if spec ? type then [ ] else [ (ornamentDiagnostic "ornament.missing-insert-type" (fieldCtx ctx info.name) "inserted field needs a type") ])
          ++ fieldOrderDiagnostics cfg ctx baseFields rest
        else if info.kind == "keep" then
          if baseFields == [ ] then
            [ (ornamentDiagnostic "ornament.keep-after-fields" (fieldCtx ctx info.name) "keep has no remaining base field") ]
          else
            let
              base = builtins.head baseFields;
              restBase = builtins.tail baseFields;
              baseNames = namesOf baseFields;
              ctxField = fieldCtx ctx info.name;
              indexedRecError =
                if base.kind == "recAt" && !(spec ? index) && !(spec ? idxFn) && !(isUnitTy cfg.J)
                then [ (ornamentDiagnostic "ornament.missing-recursive-index" ctxField "indexed recursive keep needs `index`") ]
                else [ ];
              indexedPiError =
                if isPiFieldKind base.kind
                && !(spec ? branchIndex)
                && !(spec ? branchIdxFn)
                && !(!cfg.reindexed && (base.kind == "piAt" || base.kind == "piDAt"))
                && !(isUnitTy cfg.J)
                then [ (ornamentDiagnostic "ornament.missing-branch-index" ctxField "indexed pi keep needs `branchIndex`") ]
                else [ ];
            in
            if !(builtins.elem info.name baseNames) then
              [ (ornamentDiagnostic "ornament.unknown-field" ctxField "unknown kept base field") ]
              ++ fieldOrderDiagnostics cfg ctx baseFields rest
            else if base.name != info.name then
              [ (ornamentDiagnostic "ornament.out-of-order-keep" ctxField "keep is out of order; expected field '${base.name}'") ]
              ++ fieldOrderDiagnostics cfg ctx baseFields rest
            else if !(base.kind == "data" || base.kind == "recAt" || isPiFieldKind base.kind) then
              [ (ornamentDiagnostic "ornament.unsupported-keep-kind" ctxField "unsupported keep kind '${base.kind}'") ]
              ++ fieldOrderDiagnostics cfg ctx restBase rest
            else
              indexedRecError ++ indexedPiError
              ++ fieldOrderDiagnostics cfg ctx restBase rest
        else if info.kind == "keepSub" then
          if baseFields == [ ] then
            [ (ornamentDiagnostic "ornament.keep-after-fields" (fieldCtx ctx info.name) "keep has no remaining base field") ]
          else
            let
              base = builtins.head baseFields;
              restBase = builtins.tail baseFields;
              baseNames = namesOf baseFields;
              ctxField = fieldCtx ctx info.name;
              subOk = isOrn spec.sub || isLeafOrn spec.sub || isFunctionalOrn spec.sub;
              hint = subBaseHint spec.sub;
              baseHtag = base.type._htag or null;
              subErrors =
                if !subOk then
                  [ (ornamentDiagnostic "ornament.sub-not-ornament" ctxField "keep+sub `sub` must be a raw, leaf, or functional ornament") ]
                else if hint != null && baseHtag != null && hint != baseHtag then
                  [ (ornamentDiagnostic "ornament.sub-type-mismatch" ctxField "sub-ornament base type '${hint}' disagrees with kept field type '${baseHtag}'") ]
                else [ ];
            in
            if !(builtins.elem info.name baseNames) then
              [ (ornamentDiagnostic "ornament.unknown-field" ctxField "unknown kept base field") ]
              ++ fieldOrderDiagnostics cfg ctx baseFields rest
            else if base.name != info.name then
              [ (ornamentDiagnostic "ornament.out-of-order-keep" ctxField "keep is out of order; expected field '${base.name}'") ]
              ++ fieldOrderDiagnostics cfg ctx baseFields rest
            else if base.kind != "data" then
              [ (ornamentDiagnostic "ornament.unsupported-keep-kind" ctxField "keep+sub currently only supports `data`-kinded fields, got '${base.kind}'") ]
              ++ fieldOrderDiagnostics cfg ctx restBase rest
            else
              subErrors ++ fieldOrderDiagnostics cfg ctx restBase rest
        else [ ]
      );

  constructorDiagnostics = cfg: ctx: c: conSpec:
    let
      cctx = constructorCtx ctx c.name;
      fields = conSpec.fields or [ ];
      targetErrors =
        if cfg.resultIndexed && !(conSpec ? target) && !(isUnitTy cfg.J)
        then [ (ornamentDiagnostic "ornament.missing-constructor-target" cctx "indexed constructor needs `target`") ]
        else [ ];
    in
    targetErrors
    ++ outputFieldDiagnostics cctx fields
    ++ fieldOrderDiagnostics cfg cctx c.fields fields;

  ornamentDiagnosticRecords = base: spec:
    if !(builtins.isAttrs base && base ? _cons && base ? T && base ? D) then
      [
        (mkDiagnostic {
          code = "ornament.invalid-base";
          path = [ "ornament" ];
          message = "expected monomorphic generated DataSpec";
          text = "hoas.ornament: expected monomorphic generated DataSpec";
        })
      ]
    else if !(spec ? constructors) then
      [ (ornamentDiagnostic "ornament.missing-constructors" (ornamentCtx base spec) "spec requires `constructors`") ]
    else
      let
        ctx = ornamentCtx base spec;
        cfg = indexedCfg base spec;
        baseCons = base._cons;
        specCons = spec.constructors;
        baseNames = namesOf baseCons;
        specNames = builtins.attrNames specCons;
        missing = builtins.filter (n: !(builtins.hasAttr n specCons)) baseNames;
        unknown = builtins.filter (n: !(builtins.elem n baseNames)) specNames;
        constructorErrors =
          builtins.concatMap
            (c:
              if builtins.hasAttr c.name specCons
              then constructorDiagnostics cfg ctx c (builtins.getAttr c.name specCons)
              else [ ])
            baseCons;
      in
      (map (name: ornamentDiagnostic "ornament.missing-constructor" ctx "missing constructor arm '${name}'") missing)
      ++ (map (name: ornamentDiagnostic "ornament.unknown-constructor" ctx "unknown constructor arm '${name}'") unknown)
      ++ constructorErrors;

  ornamentDiagnostics = base: spec:
    map diagnosticText (ornamentDiagnosticRecords base spec);

  validateOrnament = base: spec:
    let diagnostics = ornamentDiagnosticRecords base spec; in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; }
    else { ok = false; inherit diagnostics; };

  tryOrnament = base: spec:
    let validation = validateOrnament base spec; in
    if validation.ok then validation // { value = ornamentDatatype base spec; }
    else validation;

  fieldSpecKind = spec:
    if spec ? insert && spec ? keep then
      throw "hoas.ornament: field spec must not contain both `keep` and `insert`"
    else if spec ? insert then "insert"
    else if spec ? keep && spec ? sub then "keepSub"
    else if spec ? keep then "keep"
    else throw "hoas.ornament: field spec must contain `keep` or `insert`";

  findByName = label: xs: name:
    let
      go = rest:
        if rest == [ ] then null
        else
          let x = builtins.head rest; in
          if x.name == name then x else go (builtins.tail rest);
      found = go xs;
    in
    if found == null then throw "${label}: unknown name '${name}'" else found;

  fieldType = f:
    if f.kind == "data" then f.type
    else throw "hoas.ornament: field '${f.name}' has unsupported keep kind '${f.kind}'";

  fieldMetadata = f:
    (if f ? role then { inherit (f) role; } else { })
    // (if f ? source then { inherit (f) source; } else { })
    // (if f ? proof then { inherit (f) proof; } else { });

  mkDataField = f:
    let level = f.level or 0; in
    (if f ? eq
    then self.fieldAtWithEq level f.eq f.name f.type
    else self.fieldAt level f.name f.type)
    // fieldMetadata f;

  mkInsertedField = f:
    let
      level = f.level or 0;
      name = f.insert;
    in
    if !(f ? type) then
      throw "hoas.ornament: inserted field '${name}' needs a type"
    else
      (if f ? eq
      then self.fieldAtWithEq level f.eq name f.type
      else self.fieldAt level name f.type)
      // fieldMetadata f;

  isUnitTy = T:
    builtins.isAttrs T && (T._htag or null) == "unit";

  isPiFieldKind = kind:
    kind == "pi" || kind == "piD" || kind == "piAt" || kind == "piDAt";

  branchD = I: fields: targetIdx:
    self.conDesc I 0 { } fields targetIdx;

  unitIndexCfg = {
    I = self.unitPrim;
    J = self.unitPrim;
    erase = unitErase;
    resultIndexed = false;
  };

  indexedCfg = base: spec:
    let
      baseIndexed = base._dtypeMeta.indexed or false;
      I = base._dtypeMeta.indexTy or self.unitPrim;
      requested = spec.index or null;
      J =
        if requested != null then requested.J
        else if baseIndexed then I
        else self.unitPrim;
      erase =
        if requested != null then requested.erase
        else if baseIndexed then idErase I
        else unitErase;
    in
    {
      inherit I J erase;
      reindexed = requested != null;
      resultIndexed = requested != null || baseIndexed;
    };

  bindsPrev = f:
    f.kind == "data" || f.kind == "dataD";

  extendPrev = f: name: value: prev:
    if bindsPrev f then prev // { ${name} = value; } else prev;

  fieldDomain = base: basePrev:
    if base.kind == "data" then base.type
    else if base.kind == "pi" || base.kind == "piAt" then base.S
    else if base.kind == "piD" || base.kind == "piDAt" then base.SFn basePrev
    else throw "hoas.ornament: field '${base.name}' has unsupported keep kind '${base.kind}'";

  unitBranch = S:
    self.ann
      (self.lam "_" S (_: self.ttPrim))
      (self.forall "_" S (_: self.unitPrim));

  indexedBranch = I: S: branch:
    self.ann
      (self.lam "s" S (s: branch s))
      (self.forall "_" S (_: I));

  baseBranchFnFor = cfg: base: basePrev:
    let
      S = fieldDomain base basePrev;
      branch =
        if base.kind == "piAt" || base.kind == "piDAt" then
          s: base.branchIdxFn basePrev s
        else if isUnitTy cfg.I then
          _: self.ttPrim
        else
          throw "hoas.ornament: kept pi field '${base.name}' needs base branch metadata";
    in
    indexedBranch cfg.I S branch;

  ornBranchFnFor = cfg: base: spec: basePrev: ornPrev:
    let
      S = fieldDomain base basePrev;
      branch =
        if spec ? branchIndex then
          s: spec.branchIndex ornPrev s
        else if spec ? branchIdxFn then
          s: spec.branchIdxFn ornPrev s
        else if !cfg.reindexed && (base.kind == "piAt" || base.kind == "piDAt") then
          s: base.branchIdxFn ornPrev s
        else if isUnitTy cfg.J then
          _: self.ttPrim
        else
          throw "hoas.ornament: kept pi field '${base.name}' needs `branchIndex` for indexed ornament";
    in
    indexedBranch cfg.J S branch;

  piProofFor = cfg: base: spec: basePrev: ornPrev:
    let
      S = fieldDomain base basePrev;
    in
    if spec ? proof then spec.proof ornPrev
    else _: self.bootRefl;

  piBranchIndexFor = cfg: base: spec: prev: s:
    if spec ? branchIndex then spec.branchIndex prev s
    else if spec ? branchIdxFn then spec.branchIdxFn prev s
    else if !cfg.reindexed && (base.kind == "piAt" || base.kind == "piDAt") then base.branchIdxFn prev s
    else if isUnitTy cfg.J then self.ttPrim
    else throw "hoas.ornament: kept pi field '${base.name}' needs `branchIndex` for indexed ornament";

  recursiveIndexFor = cfg: base: spec: ornPrev:
    if spec ? index then spec.index ornPrev
    else if spec ? idxFn then spec.idxFn ornPrev
    else if isUnitTy cfg.J then self.ttPrim
    else throw "hoas.ornament: recursive keep '${base.name}' needs `index` for indexed ornament";

  constructorTargetFor = cfg: conName: conSpec: ornPrev:
    if conSpec ? target then conSpec.target ornPrev
    else if isUnitTy cfg.J then self.ttPrim
    else throw "hoas.ornament: constructor '${conName}' needs `target` for indexed ornament";

  proofFor = spec: ornPrev:
    if spec ? proof then spec.proof ornPrev else self.bootRefl;

  mkTailOrn = cfg: baseTarget: ornTarget: fields: specs: basePrev: ornPrev:
    mkOrn {
      inherit (cfg) I J erase;
      baseD = branchD cfg.I fields baseTarget;
      node = ornamentNodeFromFields cfg baseTarget ornTarget fields specs basePrev ornPrev;
    };

  # Refined-side HOAS type for a sub-ornament splicing at a kept
  # field position. Leaf ornaments expose their refined former via
  # `primitive`; named μ-ornaments expose it via the datatype's `T`.
  forwardTypeOf = label: sub:
    if isLeafOrn sub then sub.primitive
    else if builtins.isAttrs sub && sub ? T then sub.T
    else if isOrn sub then
      throw "${label}: raw μ-ornament has no exposed forward type; use the decorated form (datatype + ornament)"
    else
      throw "${label}: cannot determine forward type for sub-ornament";

  ornamentNodeFromFields = cfg: baseTarget: ornTarget: baseFields: specs: basePrev: ornPrev:
    if specs == [ ] then
      if baseFields == [ ] then
        {
          tag = "ret";
          j = ornTarget ornPrev;
          proof = self.bootRefl;
          baseIndex = baseTarget basePrev;
        }
      else
        throw "hoas.ornament: missing keep for base field '${(builtins.head baseFields).name}'"
    else
      let
        spec = builtins.head specs;
        restSpecs = builtins.tail specs;
        kind = fieldSpecKind spec;
      in
      if kind == "insert" then
        {
          tag = "argInsert";
          S = spec.type;
          l = spec.level or null;
          body = v:
            mkTailOrn cfg baseTarget ornTarget baseFields restSpecs basePrev
              (ornPrev // { ${spec.insert} = v; });
        }
      else if kind == "keepSub" then
        if baseFields == [ ] then
          throw "hoas.ornament: keep '${spec.keep}' has no remaining base field"
        else
          let
            base = builtins.head baseFields;
            restBase = builtins.tail baseFields;
          in
          if base.name != spec.keep then
            throw "hoas.ornament: keep '${spec.keep}' is out of order, expected '${base.name}'"
          else if base.kind != "data" then
            throw "hoas.ornament: keep+sub '${base.name}' only supports `data`-kinded fields, got '${base.kind}'"
          else
            {
              tag = "argKeepSub";
              S = forwardTypeOf "hoas.ornament" spec.sub;
              sub = spec.sub;
              l = base.level or null;
              body = v:
                mkTailOrn cfg baseTarget ornTarget restBase restSpecs
                  (extendPrev base base.name v basePrev)
                  (extendPrev base base.name v ornPrev);
            }
      else if kind == "keep" then
        if baseFields == [ ] then
          throw "hoas.ornament: keep '${spec.keep}' has no remaining base field"
        else
          let
            base = builtins.head baseFields;
            restBase = builtins.tail baseFields;
          in
          if base.name != spec.keep then
            throw "hoas.ornament: keep '${spec.keep}' is out of order, expected '${base.name}'"
          else if base.kind == "data" then
            {
              tag = "argKeep";
              S = fieldType base;
              l = base.level or null;
              body = v:
                mkTailOrn cfg baseTarget ornTarget restBase restSpecs
                  (extendPrev base base.name v basePrev)
                  (extendPrev base base.name v ornPrev);
            }
          else if base.kind == "recAt" then
            {
              tag = "rec";
              j = recursiveIndexFor cfg base spec ornPrev;
              proof = proofFor spec ornPrev;
              baseIndex = base.idxFn basePrev;
              tail = mkTailOrn cfg baseTarget ornTarget restBase restSpecs basePrev ornPrev;
            }
          else if isPiFieldKind base.kind then
            {
              tag = "piKeep";
              S = fieldDomain base basePrev;
              baseF = baseBranchFnFor cfg base basePrev;
              ornF = ornBranchFnFor cfg base spec basePrev ornPrev;
              proof = piProofFor cfg base spec basePrev ornPrev;
              l = base.level or null;
              tail = mkTailOrn cfg baseTarget ornTarget restBase restSpecs basePrev ornPrev;
            }
          else
            throw "hoas.ornament: keep '${base.name}' has unsupported kind '${base.kind}'"
      else
        throw "hoas.ornament: field spec must contain `keep` or `insert`";

  datatypeFieldFromSpec = cfg: baseFields: spec:
    let kind = fieldSpecKind spec; in
    if kind == "insert" then mkInsertedField spec
    else if kind == "keepSub" then
      let
        base = findByName "hoas.ornament" baseFields spec.keep;
      in
      if base.kind != "data" then
        throw "hoas.ornament: keep+sub '${base.name}' only supports `data`-kinded fields, got '${base.kind}'"
      else
        let
          level = base.level or 0;
          S = forwardTypeOf "hoas.ornament" spec.sub;
          field =
            if base ? eq
            then self.fieldAtWithEq level base.eq base.name S
            else self.fieldAt level base.name S;
        in
        field // fieldMetadata base // fieldMetadata spec
    else
      let
        base = findByName "hoas.ornament" baseFields spec.keep;
        meta = fieldMetadata base // fieldMetadata spec;
      in
      if base.kind == "data" then (mkDataField base) // fieldMetadata spec
      else if base.kind == "recAt" then (self.recFieldAt base.name
        (prev: recursiveIndexFor cfg base spec prev)) // meta
      else if base.kind == "pi" then
        (if isUnitTy cfg.J then self.piFieldAt (base.level or 0) base.name base.S
        else
          self.piFieldAtIndex (base.level or 0) base.name base.S
            (prev: s: piBranchIndexFor cfg base spec prev s)) // meta
      else if base.kind == "piD" then
        (if isUnitTy cfg.J then self.piFieldDAt (base.level or 0) base.name base.SFn
        else
          self.piFieldDAtIndex (base.level or 0) base.name base.SFn
            (prev: s: piBranchIndexFor cfg base spec prev s)) // meta
      else if base.kind == "piAt" then (self.piFieldAtIndex (base.level or 0) base.name base.S
        (prev: s: piBranchIndexFor cfg base spec prev s)) // meta
      else if base.kind == "piDAt" then (self.piFieldDAtIndex (base.level or 0) base.name base.SFn
        (prev: s: piBranchIndexFor cfg base spec prev s)) // meta
      else throw "hoas.ornament: keep '${base.name}' has unsupported kind '${base.kind}'";

  spineOrn = cfg: branchOrns:
    if branchOrns == [ ] then throw "hoas.ornament: empty constructor list"
    else if builtins.length branchOrns == 1 then builtins.head branchOrns
    else
      let
        left = builtins.head branchOrns;
        right = spineOrn cfg (builtins.tail branchOrns);
      in
      mkOrn {
        inherit (cfg) I J erase;
        baseD = self.plusI cfg.I 0 left.baseD right.baseD;
        node = { tag = "plus"; inherit left right; };
      };

  ornamentDatatype = base: spec:
    if !(builtins.isAttrs base && base ? _cons && base ? T && base ? D) then
      throw "hoas.ornament: expected monomorphic generated DataSpec"
    else if !(spec ? constructors) then
      throw "hoas.ornament: spec requires `constructors`"
    else
      let
        cfg = indexedCfg base spec;
        baseCons = base._cons;
        diagnostics = ornamentDiagnostics base spec;
        _validation =
          if diagnostics == [ ] then null
          else throw (builtins.concatStringsSep "\n" diagnostics);
        name = spec.name or "${base.name}Orn";
        conSpecFor = c: builtins.getAttr c.name spec.constructors;
        ornamentedCon = c:
          let
            conSpec = conSpecFor c;
            fields = conSpec.fields or [ ];
            outFields = map (datatypeFieldFromSpec cfg c.fields) fields;
          in
          if cfg.resultIndexed then
            self.conI c.name outFields
              (prev: constructorTargetFor cfg c.name conSpec prev)
          else
            self.con c.name outFields;
        branchOrn = c:
          let
            conSpec = conSpecFor c;
            fields = conSpec.fields or [ ];
            baseTarget = c.targetIdx;
            ornTarget = prev: constructorTargetFor cfg c.name conSpec prev;
          in
          mkOrn {
            inherit (cfg) I J erase;
            baseD = branchD cfg.I c.fields baseTarget;
            node = ornamentNodeFromFields cfg baseTarget ornTarget c.fields fields { } { };
          };
        dt =
          if cfg.resultIndexed
          then self.datatypeI name cfg.J (map ornamentedCon baseCons)
          else self.datatype name (map ornamentedCon baseCons);
        core = spineOrn cfg (map branchOrn baseCons);
        source = {
          datatype = base.name;
          ornament = name;
        };
        forget = withOrnSource (source // { kind = "ornament.forget"; }) (ornForget core);
        canForget0 = isUnitTy cfg.J && !(cfg.resultIndexed);
        forget0 =
          if canForget0 then
            withOrnSource (source // { kind = "ornament.forget0"; })
              (self.ann
                (self.lam "x" dt.T (x:
                  self.app (self.app forget self.ttPrim) x))
                (self.forall "_" dt.T (_: base.T)))
          else null;
      in
      builtins.seq _validation (dt // {
        ornament = core;
        inherit forget;
        _ornMeta = {
          inherit base spec core cfg;
        };
      } // (if forget0 == null then { } else { inherit forget0; }));
in
{
  scope = {
    ornI = api.leaf {
      description = "ornI: master constructor of an `Ornament` over a base description, packaging `{ I, J, erase, baseD, node }` and optional level/meta into the canonical ornament record consumed by `ornDesc` / `ornMu` / `ornForget`.";
      signature = "ornI : { I, J, erase, baseD, node, level?, meta? } -> Ornament";
      value = mkOrn;
    };
    ornDesc = api.leaf {
      description = "ornDesc: compile an `Ornament` to its annotated `Desc J` term — the levitated description of the ornamented datatype, ready for `muI` / `interpD`.";
      signature = "ornDesc : Ornament -> Tm  -- Desc J";
      value = ornDesc;
    };
    ornMu = api.leaf {
      description = "ornMu: build the ornamented `mu` at index `j`, i.e. `muI J (ornDesc O) j` — the carrier type of values living over the ornament at that index.";
      signature = "ornMu : Ornament -> Tm -> Tm  -- index in J yields kernel type";
      value = ornMu;
    };
    ornForget = api.leaf {
      description = "ornForget: produce the forgetting morphism `mu (ornDesc O) ~> mu (baseD O)`, mapping every ornamented value back to its underlying base-description value.";
      signature = "ornForget : Ornament -> Tm  -- J -> ornMu -> baseMu";
      value = ornForget;
    };
    ornPullback = api.leaf {
      description = "ornPullback: transport a base program `baseFn : I -> baseMu -> R(i)` along `ornForget`, yielding the same program over ornamented inputs at every J index.";
      signature = "ornPullback : Ornament -> (Tm -> Tm) -> Tm -> Tm  -- resultTy, baseFn -> lifted";
      value = ornPullback;
    };
    ornLiftFold = api.leaf {
      description = "ornLiftFold: alias for `ornPullback` specialised to folds — composes a base fold with `ornForget` so it runs on ornamented carriers without re-deriving the algebra.";
      signature = "ornLiftFold : Ornament -> (Tm -> Tm) -> Tm -> Tm  -- resultTy, baseFold -> lifted";
      value = ornLiftFold;
    };
    ornLiftProducer = api.leaf {
      description = "ornLiftProducer: lift a base producer `baseFn` through a functional ornament `F` — run the producer on the base input, then build the ornamented output via `F.section`.";
      signature = "ornLiftProducer : FunctionalOrnament -> (Tm -> Tm) -> Tm -> Tm -> Tm";
      value = ornLiftProducer;
    };
    ornLiftTransform = api.leaf {
      description = "ornLiftTransform: lift a base transform through paired input/output functional ornaments — forget the ornamented input, run the base transform, build the ornamented output.";
      signature = "ornLiftTransform : { input : OrnLike, output : FunctionalOrnament, fn } -> Tm -> Tm -> Tm -> Tm";
      value = ornLiftTransform;
    };
    functionalOrnament = api.leaf {
      description = "functionalOrnament: package `{ ornament, chooseIndex, section, indexProof?, laws?, meta? }` into a validated `FunctionalOrnament` record, the section/builder bundle that bridges base producers to ornamented outputs.";
      signature = "functionalOrnament : { ornament, chooseIndex, section, indexProof?, laws?, meta? } -> FunctionalOrnament";
      value = functionalOrnament;
    };
    functionalOrnamentDiagnosticRecords = api.leaf {
      description = "functionalOrnamentDiagnosticRecords: total structured diagnostics describing every missing / ill-typed field of a candidate `functionalOrnament` spec; returns `[]` when the spec is valid.";
      signature = "functionalOrnamentDiagnosticRecords : Attrs -> [Diagnostic]";
      value = functionalOrnamentDiagnosticRecords;
    };
    functionalOrnamentDiagnostics = api.leaf {
      description = "functionalOrnamentDiagnostics: human-readable strings derived from `functionalOrnamentDiagnosticRecords` for surfacing in error messages and test assertions.";
      signature = "functionalOrnamentDiagnostics : Attrs -> [String]";
      value = functionalOrnamentDiagnostics;
    };
    validateFunctionalOrnament = api.leaf {
      description = "validateFunctionalOrnament: total predicate over candidate functional-ornament specs returning `{ ok, diagnostics }`; never throws, intended for upstream `try*` and surface validators.";
      signature = "validateFunctionalOrnament : Attrs -> { ok : Bool, diagnostics : [Diagnostic] }";
      value = validateFunctionalOrnament;
    };
    tryFunctionalOrnament = api.leaf {
      description = "tryFunctionalOrnament: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the built functional ornament when `ok`, otherwise diagnostics-only.";
      signature = "tryFunctionalOrnament : Attrs -> { ok : Bool, diagnostics : [Diagnostic], value? : FunctionalOrnament }";
      value = tryFunctionalOrnament;
    };
    leafOrnament = api.leaf {
      description = "leafOrnament: constructor for a *leaf functional ornament* — a refinement of a primitive HOAS type former (one with `_htag ≠ \"mu\"`) carrying Nix-meta `forget : Refined → Base` and `section : Base → Refined`. The leaf case is the literature-faithful specialisation of Dagand–McBride 2014 (JFP) functional ornaments to type formers without a μ-encoded description. The canonical instance is `thunkOrnament`.";
      signature = "leafOrnament : { primitive : HoasType, forget : Refined -> Base, section : Base -> Refined, sectionProof? : Refined -> Bool, meta? : Attrs } -> LeafOrnament";
      value = leafOrnament;
    };
    tryLeafOrnament = api.leaf {
      description = "tryLeafOrnament: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the built leaf ornament when `ok`, otherwise diagnostics-only.";
      signature = "tryLeafOrnament : Attrs -> { ok : Bool, diagnostics : [Diagnostic], value? : LeafOrnament }";
      value = tryLeafOrnament;
    };
    validateLeafOrnament = api.leaf {
      description = "validateLeafOrnament: total predicate `{ ok, diagnostics }` over a candidate leaf-ornament spec; rejects μ-encoded primitives, already-ornamented primitives, and missing/malformed forget/section/sectionProof fields.";
      signature = "validateLeafOrnament : Attrs -> { ok : Bool, diagnostics : [Diagnostic] }";
      value = validateLeafOrnament;
    };
    leafOrnamentDiagnosticRecords = api.leaf {
      description = "leafOrnamentDiagnosticRecords: total structured diagnostics for a candidate leaf-ornament spec — codes `leaf.invalid-spec | leaf.missing-{primitive,forget,section} | leaf.invalid-{primitive,forget,section,section-proof}`.";
      signature = "leafOrnamentDiagnosticRecords : Attrs -> [Diagnostic]";
      value = leafOrnamentDiagnosticRecords;
    };
    leafOrnamentDiagnostics = api.leaf {
      description = "leafOrnamentDiagnostics: human-readable text forms of `leafOrnamentDiagnosticRecords` for surfacing in error messages and test assertions.";
      signature = "leafOrnamentDiagnostics : Attrs -> [String]";
      value = leafOrnamentDiagnostics;
    };
    isLeafOrn = api.leaf {
      description = "isLeafOrn: predicate identifying leaf functional ornaments via the `_leafOrnTag = \"leaf-ornament\"` tag.";
      signature = "isLeafOrn : Value -> Bool";
      value = isLeafOrn;
    };
    thunkOrnament = api.leaf {
      description = "thunkOrnament: derived leaf-functional-ornament constructor for `H.thunk inner` with `forget = forceThunk` and `section = mkThunk`. The functional ornament induced by `forceThunk : Thunk A → A` per Dagand–McBride 2014 (JFP), section 3, specialised to the primitive Thunk carrier from `fx.state.thunk`.";
      signature = "thunkOrnament : HoasType -> LeafOrnament";
      value = thunkOrnament;
    };
    ornSection = api.leaf {
      description = "ornSection: extract the `section` builder from a functional ornament — the function `i -> baseValue -> ornamentedValue` that realises the section morphism.";
      signature = "ornSection : FunctionalOrnament -> (Tm -> Tm -> Tm)";
      value = ornSection;
    };
    ornTargetIndex = api.leaf {
      description = "ornTargetIndex: extract the `chooseIndex` slot of a functional ornament — the function `i -> baseValue -> J` that picks the ornamented index for each base input.";
      signature = "ornTargetIndex : FunctionalOrnament -> (Tm -> Tm -> Tm)";
      value = ornTargetIndex;
    };
    ornIndexProof = api.leaf {
      description = "ornIndexProof: extract the `indexProof` slot of a functional ornament — the proof `i -> baseValue -> erase (chooseIndex i baseValue) ≡ i` certifying the section commutes with forget.";
      signature = "ornIndexProof : FunctionalOrnament -> (Tm -> Tm -> Tm)";
      value = ornIndexProof;
    };
    ornBuild = api.leaf {
      description = "ornBuild: build the ornamented value at index `i` from `baseValue` by invoking `F.section`; the canonical entry point for ornament construction from a base witness.";
      signature = "ornBuild : FunctionalOrnament -> Tm -> Tm -> Tm";
      value = ornBuild;
    };
    functionalLawDiagnosticRecords = api.leaf {
      description = "functionalLawDiagnosticRecords: run every check in `F.laws.checks`, collecting structured diagnostics for every law that fails to evaluate or returns non-`true`; total.";
      signature = "functionalLawDiagnosticRecords : FunctionalOrnament -> [Diagnostic]";
      value = functionalLawDiagnosticRecords;
    };
    functionalLawDiagnostics = api.leaf {
      description = "functionalLawDiagnostics: human-readable string forms of `functionalLawDiagnosticRecords` for surfacing law-check failures in test output and error reports.";
      signature = "functionalLawDiagnostics : FunctionalOrnament -> [String]";
      value = functionalLawDiagnostics;
    };
    validateFunctionalLaws = api.leaf {
      description = "validateFunctionalLaws: total predicate `{ ok, diagnostics }` over a functional ornament's law-check bundle; reports which checks failed without throwing.";
      signature = "validateFunctionalLaws : FunctionalOrnament -> { ok : Bool, diagnostics : [Diagnostic] }";
      value = validateFunctionalLaws;
    };
    checkFunctionalLaws = api.leaf {
      description = "checkFunctionalLaws: identity on `F` when every law-check passes, otherwise throws the concatenated diagnostic text — the assertive sibling of `validateFunctionalLaws`.";
      signature = "checkFunctionalLaws : FunctionalOrnament -> FunctionalOrnament  -- throws on failure";
      value = checkFunctionalLaws;
    };
    functionalCompose = api.leaf {
      description = "functionalCompose: compose two functional ornaments `outer` over `inner`, producing a functional ornament whose section threads through both `chooseIndex`/`section` pipelines.";
      signature = "functionalCompose : FunctionalOrnament -> FunctionalOrnament -> FunctionalOrnament";
      value = functionalCompose;
    };

    ornRet = api.leaf {
      description = "ornRet: ret-node spec for `ornI.node` — terminates an ornament arm at index `j` in J with a base-index witness `baseIndex` and proof `erase j ≡ baseIndex`.";
      signature = "ornRet : Tm -> Tm -> Tm -> { tag = \"ret\"; j; proof; baseIndex }";
      value = j: proof: baseIndex:
        { tag = "ret"; inherit j proof baseIndex; };
    };
    ornArgKeep = api.leaf {
      description = "ornArgKeep: argKeep-node spec for `ornI.node` — keeps a base `descArg S body` field unchanged in the ornament; body re-binds the same `s : S` recursively.";
      signature = "ornArgKeep : Tm -> (Tm -> OrnNode) -> { tag = \"argKeep\"; S; body }";
      value = S: body:
        { tag = "argKeep"; inherit S body; };
    };
    ornArgInsert = api.leaf {
      description = "ornArgInsert: argInsert-node spec for `ornI.node` — inserts a fresh `arg S` field absent from the base description; body binds the inserted witness recursively.";
      signature = "ornArgInsert : Tm -> (Tm -> OrnNode) -> { tag = \"argInsert\"; S; body }";
      value = S: body:
        { tag = "argInsert"; inherit S body; };
    };
    ornRec = api.leaf {
      description = "ornRec: rec-node spec for `ornI.node` — a recursive child at index `j` with proof `erase j ≡ baseIndex` and a `tail` ornament for the remainder of the constructor.";
      signature = "ornRec : Tm -> (Tm | { proof, baseIndex }) -> OrnNode -> { tag = \"rec\"; j; proof; baseIndex; tail }";
      value = j: proof: tail:
        let
          cfg =
            if builtins.isAttrs proof && proof ? proof
            then proof
            else {
              inherit proof;
              baseIndex = j;
            };
        in
        {
          tag = "rec";
          inherit j tail;
          proof = cfg.proof;
          baseIndex = cfg.baseIndex;
        };
    };
    ornPiKeep = api.leaf {
      description = "ornPiKeep: piKeep-node spec for `ornI.node` — keeps a Π-quantified field over `S`; `branch` supplies the base/ornament index functions and proof, defaulting to identity.";
      signature = "ornPiKeep : Tm -> (Tm | { baseF, ornF, proof }) -> OrnNode -> { tag = \"piKeep\"; S; tail; baseF; ornF; proof; l }";
      value = S: branch: tail:
        let
          cfg =
            if builtins.isAttrs branch && branch ? baseF && branch ? ornF
            then branch
            else {
              baseF = branch;
              ornF = branch;
              proof = _: self.bootRefl;
            };
        in
        {
          tag = "piKeep";
          inherit S tail;
          baseF = cfg.baseF;
          ornF = cfg.ornF;
          proof = cfg.proof or (_: self.bootRefl);
          l = cfg.l or null;
        };
    };
    ornPlus = api.leaf {
      description = "ornPlus: plus-node spec for `ornI.node` — sum of two ornament arms `left` and `right`, mirroring `descPlus` at the ornament level.";
      signature = "ornPlus : OrnNode -> OrnNode -> { tag = \"plus\"; left; right }";
      value = left: right:
        { tag = "plus"; inherit left right; };
    };

    algRet = api.leaf {
      description = "algRet: ret algebra — terminates an algebraic ornament arm by returning a constant `result` value for the leaf description; used over `descRet` shapes.";
      signature = "algRet : Tm -> Algebra";
      value = result: mkAlg "ret" { inherit result; };
    };
    algArg = api.leaf {
      description = "algArg: arg algebra — consumes the `descArg`'s payload via `body : s -> Algebra`, recursing into the rest of the description through the resulting algebra.";
      signature = "algArg : (Tm -> Algebra) -> Algebra";
      value = body: mkAlg "arg" { inherit body; };
    };
    algRec = api.leaf {
      description = "algRec: rec algebra — handles a `descRec` arm by giving `body : recResult -> Algebra` over the recursive child's algebra result; threads results upward.";
      signature = "algRec : (Tm -> Algebra) -> Algebra";
      value = body: mkAlg "rec" { inherit body; };
    };
    algPiKeep = api.leaf {
      description = "algPiKeep: pi-keep algebra — `body` consumes the Π-quantified branch using `branchIndex` (or full `{ branchIndex, ... }` record), generating an algebra per branch.";
      signature = "algPiKeep : (Tm | { branchIndex, ... }) -> (Tm -> Algebra) -> Algebra";
      value = branch: body:
        mkAlg "pi" ((if builtins.isAttrs branch then branch else { branchIndex = branch; }) // { inherit body; });
    };
    algPlus = api.leaf {
      description = "algPlus: plus algebra — sum of two sub-algebras, mirroring `descPlus`; routes the algebra into `left` or `right` depending on the constructor arm taken.";
      signature = "algPlus : Algebra -> Algebra -> Algebra";
      value = left: right: mkAlg "plus" { inherit left right; };
    };
    algOrn = api.leaf {
      description = "algOrn: build an `Ornament` from an algebra over a base description — indexed by the algebra's result, so each ornamented value carries its algebra trace as the J-index.";
      signature = "algOrn : { I?, J, baseD | D, erase, algebra, resultTy?, pack?, proof?, level?, meta? } -> Ornament";
      value = algOrn;
    };
    algOrnDiagnosticRecords = api.leaf {
      description = "algOrnDiagnosticRecords: total structured diagnostics describing every shape mismatch between an algebra and its target description; returns `[]` on success.";
      signature = "algOrnDiagnosticRecords : Attrs -> [Diagnostic]";
      value = algOrnDiagnosticRecords;
    };
    algOrnDiagnostics = api.leaf {
      description = "algOrnDiagnostics: human-readable text forms of `algOrnDiagnosticRecords` for inclusion in error messages and test assertions.";
      signature = "algOrnDiagnostics : Attrs -> [String]";
      value = algOrnDiagnostics;
    };
    validateAlgOrn = api.leaf {
      description = "validateAlgOrn: total predicate `{ ok, diagnostics }` over a candidate `algOrn` spec — checks every algebra arm against its description shape without throwing.";
      signature = "validateAlgOrn : Attrs -> { ok : Bool, diagnostics : [Diagnostic] }";
      value = validateAlgOrn;
    };
    tryAlgOrn = api.leaf {
      description = "tryAlgOrn: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the `algOrn`-built ornament when `ok`, otherwise diagnostics-only.";
      signature = "tryAlgOrn : Attrs -> { ok : Bool, diagnostics : [Diagnostic], value? : Ornament }";
      value = tryAlgOrn;
    };

    ornId = api.leaf {
      description = "ornId: identity ornament on `D : Desc I` — `forget` is the identity at every index; the unit of `ornCompose`. Recovers `D` as its own ornament.";
      signature = "ornId : Tm -> Tm -> Ornament  -- I, D";
      value = ornId;
    };
    ornCompose = api.leaf {
      description = "ornCompose: vertical composition of ornaments — given `inner : I -> J` and `outer : J -> K`, produce `outer ∘ inner : I -> K`; sequential refinement.";
      signature = "ornCompose : Ornament -> Ornament -> Ornament  -- outer, inner";
      value = compose;
    };
    ornament = api.leaf {
      description = "ornament: master surface — given a monomorphic generated `DataSpec` (`base`) and a constructor-by-constructor `spec`, produce the ornamented `Datatype` plus `forget` morphism.";
      signature = "ornament : DataSpec -> OrnamentSpec -> Datatype";
      value = ornamentDatatype;
    };
    ornamentDiagnosticRecords = api.leaf {
      description = "ornamentDiagnosticRecords: total structured diagnostics covering every surface error in an ornament spec — missing constructors, unknown arms, malformed fields, out-of-order keeps.";
      signature = "ornamentDiagnosticRecords : DataSpec -> OrnamentSpec -> [Diagnostic]";
      value = ornamentDiagnosticRecords;
    };
    ornamentDiagnostics = api.leaf {
      description = "ornamentDiagnostics: human-readable text forms of `ornamentDiagnosticRecords` for surfacing in error messages and test assertions.";
      signature = "ornamentDiagnostics : DataSpec -> OrnamentSpec -> [String]";
      value = ornamentDiagnostics;
    };
    validateOrnament = api.leaf {
      description = "validateOrnament: total predicate `{ ok, diagnostics }` over `(base, spec)` for the user-facing `ornament` surface; never throws.";
      signature = "validateOrnament : DataSpec -> OrnamentSpec -> { ok : Bool, diagnostics : [Diagnostic] }";
      value = validateOrnament;
    };
    tryOrnament = api.leaf {
      description = "tryOrnament: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the built ornamented datatype when `ok`, otherwise diagnostics-only.";
      signature = "tryOrnament : DataSpec -> OrnamentSpec -> { ok : Bool, diagnostics : [Diagnostic], value? : Datatype }";
      value = tryOrnament;
    };
  };

  tests =
    let
      H = self;
      Q = fx.tc.quote;
      C = fx.tc.conv;
      E = fx.tc.eval;
      # Definitional equality via the kernel's `conv`. `Q.nf == Q.nf` is
      # intensional Nix attrset equality on quoted normal forms; it
      # asserts byte-identity of the chosen Tm representative and forces
      # the entire encoded structure including bootstrap-sum sidecars and
      # lifted proof carriers. Use `semEq` whenever the assertion is
      # "these two HOAS programs are definitionally equal" — `conv` has
      # the right semantic short-cuts (`_canonRef`, `_descRef`, descView
      # semantic projection, proof/eta) and decides the kernel's actual
      # equivalence. `Q.nf == Q.nf` is reserved for genuine syntactic
      # round-trip assertions.
      semEq = lhs: rhs:
        C.conv 0 (E.eval [ ] (H.elab lhs)) (E.eval [ ] (H.elab rhs));
      baseD = H.descArg H.unitPrim 0 H.nat (_: H.descRet);
      baseT = H.mu baseD H.ttPrim;
      insertBool =
        H.ornI {
          I = H.unitPrim;
          J = H.unitPrim;
          erase = unitErase;
          baseD = baseD;
          node = H.ornArgInsert H.bool (_: H.ornId H.unitPrim baseD);
        };
      insertString =
        let d1 = H.ornDesc insertBool; in
        H.ornI {
          I = H.unitPrim;
          J = H.unitPrim;
          erase = unitErase;
          baseD = d1;
          node = H.ornArgInsert H.string (_: H.ornId H.unitPrim d1);
        };
      insertedValue =
        H.descCon (H.ornDesc insertBool) H.ttPrim
          (H.pair H.true_ (H.pair H.zero H.bootRefl));
      piVoidD =
        H.piI H.unitPrim 0 H.void
          (H.ann
            (H.lam "_" H.void (_: H.ttPrim))
            (H.forall "_" H.void (_: H.unitPrim)))
          H.descRet;
      piVoidT = H.muI H.unitPrim piVoidD H.ttPrim;
      piVoidValue =
        H.descCon piVoidD H.ttPrim
          (H.pair
            (H.lam "x" H.void (x: H.absurd piVoidT x))
            H.bootRefl);
      natToUnitErase =
        H.ann
          (H.lam "_" H.nat (_: H.ttPrim))
          (H.forall "_" H.nat (_: H.unitPrim));
      retNatToUnitOrn =
        H.ornI {
          I = H.unitPrim;
          J = H.nat;
          erase = natToUnitErase;
          baseD = H.descRet;
          node = H.ornRet H.zero H.bootRefl H.ttPrim;
        };
      listNatD =
        H.ann
          (H.plus H.descRet
            (H.descArg H.unitPrim 0 H.nat (_: H.descRec H.descRet)))
          (H.descI H.unitPrim);
      listNatLengthFold =
        let
          nilD = H.descRet;
          consD = H.descArg H.unitPrim 0 H.nat (_: H.descRec H.descRet);
          muFam = H.lam "i" H.unitPrim (i: H.muI H.unitPrim listNatD i);
          motive =
            H.lam "i" H.unitPrim (i:
              H.lam "_" (H.muI H.unitPrim listNatD i) (_: H.nat));
          step =
            H.lam "i" H.unitPrim (i:
              let
                lTy = H.interpD 0 H.unitPrim nilD muFam i;
                rTy = H.interpD 0 H.unitPrim consD muFam i;
                allFor = payload:
                  H.allD 0 H.unitPrim listNatD 0 muFam motive i payload;
              in
              H.lam "d" (H.interpD 0 H.unitPrim listNatD muFam i) (d:
                H.lam "ih" (H.allD 0 H.unitPrim listNatD 0 muFam motive i d) (ih:
                  H.app
                    (H.bootSumElim lTy rTy
                      (H.lam "payload" (H.bootSum lTy rTy) (payload:
                        H.forall "_" (allFor payload) (_: H.nat)))
                      (H.lam "nil" lTy (nil:
                        H.lam "_ih" (allFor (H.bootInl lTy rTy nil)) (_:
                          H.zero)))
                      (H.lam "cons" rTy (cons:
                        H.lam "ih" (allFor (H.bootInr lTy rTy cons)) (ih:
                          H.succ (H.fst_ ih))))
                      d)
                    ih)));
        in
        H.ann
          (H.lam "i" H.unitPrim (i:
            H.lam "xs" (H.muI H.unitPrim listNatD i) (xs:
              H.descInd listNatD motive step i xs)))
          (H.forall "i" H.unitPrim (i:
            H.forall "_" (H.muI H.unitPrim listNatD i) (_: H.nat)));
      listNatToVecOrn =
        let
          mk = baseD_: node_:
            H.ornI {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              baseD = baseD_;
              node = node_;
            };
          retAt = n:
            mk H.descRet (H.ornRet (H.succ n) H.bootRefl H.ttPrim);
          recAt = n:
            mk (H.descRec H.descRet)
              (H.ornRec n { proof = H.bootRefl; baseIndex = H.ttPrim; } (retAt n));
          keepHead = n:
            mk (H.descArg H.unitPrim 0 H.nat (_: H.descRec H.descRet))
              (H.ornArgKeep H.nat (_: recAt n));
          consBranch =
            mk (H.descArg H.unitPrim 0 H.nat (_: H.descRec H.descRet))
              (H.ornArgInsert H.nat (n: keepHead n));
          nilBranch = mk H.descRet (H.ornRet H.zero H.bootRefl H.ttPrim);
        in
        mk listNatD (H.ornPlus nilBranch consBranch);
      listNatLengthAlg =
        H.algPlus
          (H.algRet H.zero)
          (H.algArg (_x:
            H.algRec (n:
              H.algRet (H.succ n))));
      listNatToVecAlgOrn =
        H.algOrn {
          I = H.unitPrim;
          J = H.nat;
          erase = natToUnitErase;
          D = listNatD;
          algebra = listNatLengthAlg;
        };
      sigmaNatIndex = H.sigma "i" H.unitPrim (_: H.nat);
      sigmaNatErase =
        H.ann
          (H.lam "p" sigmaNatIndex (p: H.fst_ p))
          (H.forall "_" sigmaNatIndex (_: H.unitPrim));
      listNatToSigmaVecAlgOrn =
        H.algOrn {
          I = H.unitPrim;
          J = sigmaNatIndex;
          erase = sigmaNatErase;
          D = listNatD;
          resultTy = _: H.nat;
          pack = i: n: H.pair i n;
          algebra = listNatLengthAlg;
        };
      builderCountD =
        H.descArg H.unitPrim 0 H.nat (_: H.descRet);
      builderCountAlgOrn =
        H.algOrn {
          I = H.unitPrim;
          J = H.nat;
          erase = natToUnitErase;
          D = builderCountD;
          algebra = H.algArg (count: H.algRet count);
        };
      piVoidKeepAlg =
        H.algPiKeep
          {
            branchIndex = x: H.absurd H.nat x;
          }
          (H.algRet H.zero);
      vecAlgD = H.ornDesc listNatToVecAlgOrn;
      vecAlgMuFam = H.lam "n" H.nat (n: H.muI H.nat vecAlgD n);
      vecAlgLeftD = H.ornDesc listNatToVecAlgOrn.node.left;
      vecAlgRightD = H.ornDesc listNatToVecAlgOrn.node.right;
      vecAlgBranchTys = n:
        let
          left = H.interpD 0 H.nat vecAlgLeftD vecAlgMuFam n;
          right = H.interpD 0 H.nat vecAlgRightD vecAlgMuFam n;
        in
        { inherit left right; };
      vecAlgZero =
        let tys = vecAlgBranchTys H.zero; in
        H.descCon vecAlgD H.zero
          (H.bootInl tys.left tys.right H.bootRefl);
      vecAlgOne =
        let tys = vecAlgBranchTys (H.succ H.zero); in
        H.descCon vecAlgD (H.succ H.zero)
          (H.bootInr tys.left tys.right
            (H.pair H.zero
              (H.pair H.zero
                (H.pair vecAlgZero H.bootRefl))));
      baseBoolProgram =
        H.ann
          (H.lam "i" H.unitPrim (i:
            H.lam "_" (H.muI H.unitPrim baseD i) (_: H.true_)))
          (H.forall "i" H.unitPrim (i:
            H.forall "_" (H.muI H.unitPrim baseD i) (_: H.bool)));
      Box = H.datatype "OrnBoxBase" [
        (H.con "box" [ (H.field "value" H.nat) ])
      ];
      TaggedBox = H.ornament Box {
        name = "TaggedBox";
        constructors.box.fields = [
          { insert = "tag"; type = H.bool; }
          { keep = "value"; }
        ];
      };
      TaggedBoxCoreOrn =
        let
          ret =
            H.ornI {
              I = H.unitPrim;
              J = H.unitPrim;
              erase = unitErase;
              baseD = H.descRet;
              node = H.ornRet H.ttPrim H.bootRefl H.ttPrim;
            };
          keepValue =
            H.ornI {
              I = H.unitPrim;
              J = H.unitPrim;
              erase = unitErase;
              baseD = H.descArg H.unitPrim 0 H.nat (_: H.descRet);
              node = H.ornArgKeep H.nat (_: ret);
            };
        in
        H.ornI {
          I = H.unitPrim;
          J = H.unitPrim;
          erase = unitErase;
          baseD = Box.D;
          node = H.ornArgInsert H.bool (_: keepValue);
        };
      ListNatSugarBase = H.datatype "OrnListNatSugarBase" [
        (H.con "nil" [ ])
        (H.con "cons" [
          (H.field "head" H.nat)
          (H.recField "tail")
        ])
      ];
      VecFromListSugar = H.ornament ListNatSugarBase {
        name = "OrnVecFromListSugar";
        index = {
          J = H.nat;
          erase = natToUnitErase;
        };
        constructors.nil = {
          target = _: H.zero;
          fields = [ ];
        };
        constructors.cons = {
          target = prev: H.succ prev.n;
          fields = [
            { insert = "n"; type = H.nat; }
            { keep = "head"; }
            { keep = "tail"; index = prev: prev.n; }
          ];
        };
      };
      IndexedPiBase = H.datatypeI "OrnIndexedPiBase" H.bool [
        (H.conI "mk"
          [ (H.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) ]
          (_: H.true_))
      ];
      IndexedPiKept = H.ornament IndexedPiBase {
        name = "OrnIndexedPiKept";
        constructors.mk = {
          target = _: H.true_;
          fields = [
            { keep = "next"; }
          ];
        };
      };
      DiagnosticsBox = H.datatype "OrnDiagBox" [
        (H.con "box" [ (H.field "value" H.nat) ])
      ];
      DiagnosticsPair = H.datatype "OrnDiagPair" [
        (H.con "pair" [
          (H.field "left" H.nat)
          (H.field "right" H.bool)
        ])
      ];
      diagnosticNatToBoolErase =
        H.ann
          (H.lam "_" H.nat (_: H.true_))
          (H.forall "_" H.nat (_: H.bool));
      DiagnosticsIndexedPiBase = H.datatypeI "OrnDiagIndexedPiBase" H.bool [
        (H.conI "mk"
          [ (H.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) ]
          (_: H.true_))
      ];
      DiagnosticsBadKeepBase = {
        name = "OrnDiagBadKeepBase";
        T = H.muI H.unitPrim H.descRet H.ttPrim;
        D = H.descRet;
        _cons = [
          {
            name = "mk";
            index = 0;
            targetIdx = _: H.ttPrim;
            fields = [
              {
                name = "ghost";
                kind = "proof";
                index = 0;
              }
            ];
          }
        ];
        _dtypeMeta = {
          name = "OrnDiagBadKeepBase";
          indexed = false;
          indexTy = H.unitPrim;
        };
      };
      hasDiag = messages: msg: builtins.elem msg messages;
      firstDiagnostic = result: builtins.head result.diagnostics;
    in
    {
      "orn-id-desc-ret-shape" = {
        expr = semEq (H.ornDesc (H.ornId H.unitPrim H.descRet)) H.descRet;
        expected = true;
      };

      "orn-id-forget-ret-checks" = {
        expr =
          let
            O = H.ornId H.unitPrim H.descRet;
            T = H.mu H.descRet H.ttPrim;
            x = H.descCon H.descRet H.ttPrim H.bootRefl;
          in
          (H.checkHoas T (H.app (H.app (H.ornForget O) H.ttPrim) x)).tag;
        expected = "app";
      };

      "orn-law-id-forget" = {
        expr =
          let
            O = H.ornId H.unitPrim H.descRet;
            x = H.descCon H.descRet H.ttPrim H.bootRefl;
            lhs = H.app (H.app (H.ornForget O) H.ttPrim) x;
          in
          semEq lhs x;
        expected = true;
      };

      "orn-ret-forget-uses-desc-leaf-eq-orientation" = {
        expr =
          let
            O = retNatToUnitOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim H.descRet H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "orn-law-ret-eq-orientation-regression" = {
        expr =
          let
            O = retNatToUnitOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim H.descRet H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "orn-insert-desc-shape" = {
        expr = semEq (H.ornDesc insertBool)
          (H.descArg H.unitPrim 0 H.bool (_: baseD));
        expected = true;
      };

      "orn-insert-forget-drops-field" = {
        expr = (H.checkHoas baseT
          (H.app (H.app (H.ornForget insertBool) H.ttPrim) insertedValue)).tag;
        expected = "app";
      };

      "orn-plus-forget-preserves-left-choice" = {
        expr =
          let
            D = H.plus baseD H.descRet;
            O = H.ornId H.unitPrim D;
            T = H.mu D H.ttPrim;
            x = H.descCon D H.ttPrim
              (H.bootInl
                (H.interpD 0 H.unitPrim baseD
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                (H.interpD 0 H.unitPrim H.descRet
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                (H.pair H.zero H.bootRefl));
          in
          (H.checkHoas T (H.app (H.app (H.ornForget O) H.ttPrim) x)).tag;
        expected = "app";
      };

      "orn-rec-forget-recurses" = {
        expr =
          let
            D = H.plus H.descRet (H.descRec H.descRet);
            O = H.ornId H.unitPrim D;
            T = H.mu D H.ttPrim;
            zero = H.descCon D H.ttPrim
              (H.bootInl
                (H.interpD 0 H.unitPrim H.descRet
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                (H.interpD 0 H.unitPrim (H.descRec H.descRet)
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                H.bootRefl);
            succZero = H.descCon D H.ttPrim
              (H.bootInr
                (H.interpD 0 H.unitPrim H.descRet
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                (H.interpD 0 H.unitPrim (H.descRec H.descRet)
                  (H.lam "i" H.unitPrim (i: H.mu D i))
                  H.ttPrim)
                (H.pair zero H.bootRefl));
          in
          (H.checkHoas T (H.app (H.app (H.ornForget O) H.ttPrim) succZero)).tag;
        expected = "app";
      };

      "orn-id-desc-pi-shape" = {
        expr = semEq (H.ornDesc (H.ornId H.unitPrim piVoidD)) piVoidD;
        expected = true;
      };

      "orn-pi-forget-checks" = {
        expr =
          let
            O = H.ornId H.unitPrim piVoidD;
          in
          (H.checkHoas piVoidT
            (H.app (H.app (H.ornForget O) H.ttPrim) piVoidValue)).tag;
        expected = "app";
      };

      "orn-id-indexed-desc-pi-forget-checks" = {
        expr =
          let
            O = H.ornId H.bool IndexedPiBase.D;
            D = H.ornDesc O;
            forgetTy =
              H.forall "b" H.bool (b:
                H.forall "_" (H.muI H.bool D b) (_:
                  H.muI H.bool IndexedPiBase.D b));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "orn-regression-indexed-pi-forget-applies" = {
        expr =
          let
            O = H.ornId H.bool IndexedPiBase.D;
            T = H.muI H.bool IndexedPiBase.D H.true_;
            vacuous = H.lam "x" H.void (x: H.absurd T x);
            x = H.app IndexedPiBase.mk vacuous;
          in
          (H.checkHoas T
            (H.app (H.app (H.ornForget O) H.true_) x)).tag;
        expected = "app";
      };

      "orn-list-to-vec-forget-checks" = {
        expr =
          let
            O = listNatToVecOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim listNatD H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "algOrn-list-to-vec-forget-checks" = {
        expr =
          let
            O = listNatToVecAlgOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim listNatD H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "algOrn-sigma-indexed-list-to-vec-forget-checks" = {
        expr =
          let
            O = listNatToSigmaVecAlgOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "p" sigmaNatIndex (p:
                H.forall "_" (H.muI sigmaNatIndex D p) (_:
                  H.muI H.unitPrim listNatD (H.fst_ p)));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "algOrn-builder-count-forget-checks" = {
        expr =
          let
            O = builderCountAlgOrn;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim builderCountD H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "algOrn-pi-keep-forget-checks" = {
        expr =
          let
            O = H.algOrn {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              D = piVoidD;
              algebra = piVoidKeepAlg;
            };
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim piVoidD H.ttPrim));
          in
            !((H.checkHoas forgetTy (H.ornForget O)) ? error);
        expected = true;
      };

      "algOrn-pi-implicit-aggregation-rejected" = {
        expr =
          let
            result = H.validateAlgOrn {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              D = piVoidD;
              algebra = H.algRet H.zero;
            };
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code path message;
          };
        expected = {
          ok = false;
          code = "algOrn.shape-mismatch";
          path = "root";
          message = "expected pi algebra for descPi, got ret";
        };
      };

      "algOrn-pi-malformed-tail-diagnostics" = {
        expr =
          let
            result = H.validateAlgOrn {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              D = piVoidD;
              algebra = H.algPiKeep
                {
                  branchIndex = x: H.absurd H.nat x;
                }
                (H.algArg (_: H.algRet H.zero));
            };
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code path message;
          };
        expected = {
          ok = false;
          code = "algOrn.shape-mismatch";
          path = "root.pi";
          message = "expected ret algebra for descRet, got arg";
        };
      };

      "algOrn-rejects-implicit-pi-aggregation" = {
        expr = (builtins.tryEval (H.algOrn {
          I = H.unitPrim;
          J = H.nat;
          erase = natToUnitErase;
          D = piVoidD;
          algebra = H.algRet H.zero;
        }).node.tag).success;
        expected = false;
      };

      "ornPullback-checks" = {
        expr =
          let
            pulled = H.ornPullback insertBool (_: H.bool) baseBoolProgram;
          in
          (H.checkHoas H.bool
            (H.app (H.app pulled H.ttPrim) insertedValue)).tag;
        expected = "app";
      };

      "ornPullback-matches-forget-then-run" = {
        expr =
          let
            pulled = H.ornPullback insertBool (_: H.bool) baseBoolProgram;
            lhs = H.app (H.app pulled H.ttPrim) insertedValue;
            forgot = H.app (H.app (H.ornForget insertBool) H.ttPrim) insertedValue;
            rhs = H.app (H.app baseBoolProgram H.ttPrim) forgot;
          in
          semEq lhs rhs;
        expected = true;
      };

      "orn-law-pullback-coherence" = {
        expr =
          let
            pulled = H.ornPullback insertBool (_: H.bool) baseBoolProgram;
            lhs = H.app (H.app pulled H.ttPrim) insertedValue;
            forgot = H.app (H.app (H.ornForget insertBool) H.ttPrim) insertedValue;
            rhs = H.app (H.app baseBoolProgram H.ttPrim) forgot;
          in
          semEq lhs rhs;
        expected = true;
      };

      "ornLiftFold-list-length-checks" = {
        expr =
          let
            O = listNatToVecAlgOrn;
            lifted = H.ornLiftFold O (_: H.nat) listNatLengthFold;
            r = H.checkHoas H.nat
              (H.app (H.app lifted (H.succ H.zero)) vecAlgOne);
          in
          if r ? error then r.msg else r.tag;
        expected = "app";
      };

      "ornLiftFold-matches-forget-then-run" = {
        expr =
          let
            O = listNatToVecAlgOrn;
            lifted = H.ornLiftFold O (_: H.nat) listNatLengthFold;
            lhs = H.app (H.app lifted (H.succ H.zero)) vecAlgOne;
            forgot = H.app (H.app (H.ornForget O) (H.succ H.zero)) vecAlgOne;
            rhs = H.app (H.app listNatLengthFold H.ttPrim) forgot;
          in
          semEq lhs rhs;
        expected = true;
      };

      "functionalOrnament-validate-missing-section" = {
        expr =
          let
            result = H.validateFunctionalOrnament {
              ornament = insertBool;
              chooseIndex = i: _x: i;
            };
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code severity path message;
          };
        expected = {
          ok = false;
          code = "functional.missing-section";
          severity = "error";
          path = [ "functionalOrnament" "section" ];
          message = "functional ornament needs `section`";
        };
      };

      "functionalOrnament-build-section-forget-law" = {
        expr =
          let
            baseValue = H.descCon baseD H.ttPrim
              (H.pair H.zero H.bootRefl);
            F = H.functionalOrnament {
              ornament = insertBool;
              chooseIndex = i: _x: i;
              indexProof = _i: _x: H.bootRefl;
              section = i: _x:
                H.descCon (H.ornDesc insertBool) i
                  (H.pair H.true_
                    (H.pair H.zero H.bootRefl));
            };
            built = H.ornBuild F H.ttPrim baseValue;
            forgot = H.app (H.app (H.ornForget insertBool) H.ttPrim) built;
          in
          semEq forgot baseValue;
        expected = true;
      };

      "functionalOrnament-law-check-failure-diagnostic" = {
        expr =
          let
            F = H.functionalOrnament {
              ornament = insertBool;
              chooseIndex = i: _x: i;
              section = i: _x:
                H.descCon (H.ornDesc insertBool) i
                  (H.pair H.true_
                    (H.pair H.zero H.bootRefl));
              laws.checks.sectionForgetSample = false;
            };
            result = H.validateFunctionalLaws F;
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code severity path message;
          };
        expected = {
          ok = false;
          code = "functional.law-failed";
          severity = "error";
          path = [ "functionalOrnament" "laws" "sectionForgetSample" ];
          message = "law check failed";
        };
      };

      "functionalOrnament-compose-section-forget-law" = {
        expr =
          let
            baseValue = H.descCon baseD H.ttPrim
              (H.pair H.zero H.bootRefl);
            F1 = H.functionalOrnament {
              ornament = insertBool;
              chooseIndex = i: _x: i;
              indexProof = _i: _x: H.bootRefl;
              section = i: _x:
                H.descCon (H.ornDesc insertBool) i
                  (H.pair H.false_
                    (H.pair H.zero H.bootRefl));
            };
            F2 = H.functionalOrnament {
              ornament = insertString;
              chooseIndex = i: _x: i;
              indexProof = _i: _x: H.bootRefl;
              section = i: _x:
                H.descCon (H.ornDesc insertString) i
                  (H.pair (H.stringLit "tool")
                    (H.pair H.false_
                      (H.pair H.zero H.bootRefl)));
            };
            F = H.functionalCompose F2 F1;
            built = H.ornBuild F H.ttPrim baseValue;
            forgot = H.app (H.app (H.ornForget F.ornament) H.ttPrim) built;
          in
          semEq forgot baseValue;
        expected = true;
      };

      "orn-law-liftFold-coherence" = {
        expr =
          let
            O = listNatToVecAlgOrn;
            lifted = H.ornLiftFold O (_: H.nat) listNatLengthFold;
            lhs = H.app (H.app lifted (H.succ H.zero)) vecAlgOne;
            forgot = H.app (H.app (H.ornForget O) (H.succ H.zero)) vecAlgOne;
            rhs = H.app (H.app listNatLengthFold H.ttPrim) forgot;
          in
          semEq lhs rhs;
        expected = true;
      };

      "orn-law-alg-index-agrees-with-fold" = {
        expr =
          let
            O = listNatToVecAlgOrn;
            forgot = H.app (H.app (H.ornForget O) (H.succ H.zero)) vecAlgOne;
            folded = H.app (H.app listNatLengthFold H.ttPrim) forgot;
          in
          semEq folded (H.succ H.zero);
        expected = true;
      };

      "orn-compose-forget-drops-in-order" = {
        expr =
          let
            O = H.ornCompose insertString insertBool;
            T = H.mu baseD H.ttPrim;
            x = H.descCon (H.ornDesc O) H.ttPrim
              (H.pair (H.stringLit "tool")
                (H.pair H.false_ (H.pair H.zero H.bootRefl)));
            r = H.checkHoas T (H.app (H.app (H.ornForget O) H.ttPrim) x);
          in
          if r ? error then r else r.tag;
        expected = "app";
      };

      "orn-law-compose-forget" = {
        expr =
          let
            O = H.ornCompose insertString insertBool;
            x = H.descCon (H.ornDesc O) H.ttPrim
              (H.pair (H.stringLit "tool")
                (H.pair H.false_ (H.pair H.zero H.bootRefl)));
            lhs = H.app (H.app (H.ornForget O) H.ttPrim) x;
            mid = H.app (H.app (H.ornForget insertString) H.ttPrim) x;
            rhs = H.app (H.app (H.ornForget insertBool) H.ttPrim) mid;
          in
          semEq lhs rhs;
        expected = true;
      };

      "ornament-sugar-inserted-field-forget-checks" = {
        expr =
          let
            tagged = H.app (H.app TaggedBox.box H.true_) H.zero;
          in
          (H.checkHoas Box.T (H.app TaggedBox.forget0 tagged)).tag;
        expected = "app";
      };

      "orn-law-sugar-core-agreement" = {
        expr =
          semEq (H.ornDesc TaggedBox.ornament) (H.ornDesc TaggedBoxCoreOrn);
        expected = true;
      };

      "ornament-sugar-datatype-metadata" = {
        expr = {
          inherit (TaggedBox) name;
          constructors = map (c: c.name) TaggedBox._dtypeMeta.constructors;
          fields = map (f: f.name)
            ((builtins.head TaggedBox._dtypeMeta.constructors).fields);
          hasOrn = TaggedBox ? ornament;
          hasForget = TaggedBox ? forget0;
        };
        expected = {
          name = "TaggedBox";
          constructors = [ "box" ];
          fields = [ "tag" "value" ];
          hasOrn = true;
          hasForget = true;
        };
      };

      "ornament-source-map-forget0-source" = {
        expr = (H.sourceMapOf TaggedBox.forget0).hoas._ornSource;
        expected = {
          kind = "ornament.forget0";
          datatype = "OrnBoxBase";
          ornament = "TaggedBox";
        };
      };

      "ornament-source-map-indexed-forget-source" = {
        expr = (H.sourceMapOf VecFromListSugar.forget).hoas._ornSource;
        expected = {
          kind = "ornament.forget";
          datatype = "OrnListNatSugarBase";
          ornament = "OrnVecFromListSugar";
        };
      };

      "ornament-sugar-indexed-forget-checks" = {
        expr =
          let
            O = VecFromListSugar.ornament;
            D = H.ornDesc O;
            forgetTy =
              H.forall "n" H.nat (n:
                H.forall "_" (H.muI H.nat D n) (_:
                  H.muI H.unitPrim ListNatSugarBase.D H.ttPrim));
          in
            !((H.checkHoas forgetTy VecFromListSugar.forget) ? error);
        expected = true;
      };

      "ornament-sugar-indexed-metadata" = {
        expr = {
          inherit (VecFromListSugar) name;
          indexed = VecFromListSugar._dtypeMeta.indexed;
          hasForget0 = VecFromListSugar ? forget0;
          constructors = map (c: c.name) VecFromListSugar._dtypeMeta.constructors;
          consFields = map (f: f.name)
            ((builtins.elemAt VecFromListSugar._dtypeMeta.constructors 1).fields);
        };
        expected = {
          name = "OrnVecFromListSugar";
          indexed = true;
          hasForget0 = false;
          constructors = [ "nil" "cons" ];
          consFields = [ "n" "head" "tail" ];
        };
      };

      "orn-regression-sugar-reindexed-rec-forget-applies" = {
        expr =
          let
            nil = VecFromListSugar.nil;
            cons =
              H.app (H.app (H.app VecFromListSugar.cons H.zero) H.zero) nil;
            target = H.muI H.unitPrim ListNatSugarBase.D H.ttPrim;
            forgot =
              H.app (H.app VecFromListSugar.forget (H.succ H.zero)) cons;
          in
          (H.checkHoas target forgot).tag;
        expected = "app";
      };

      "ornament-sugar-indexed-pi-keep-checks" = {
        expr =
          let
            O = IndexedPiKept.ornament;
            D = H.ornDesc O;
            forgetTy =
              H.forall "b" H.bool (b:
                H.forall "_" (H.muI H.bool D b) (_:
                  H.muI H.bool IndexedPiBase.D b));
          in
            !((H.checkHoas forgetTy IndexedPiKept.forget) ? error);
        expected = true;
      };

      "orn-regression-sugar-indexed-pi-forget-applies" = {
        expr =
          let
            T = H.muI H.bool IndexedPiBase.D H.true_;
            vacuous = H.lam "x" H.void (x: H.absurd T x);
            x = H.app IndexedPiKept.mk vacuous;
          in
          (H.checkHoas T
            (H.app (H.app IndexedPiKept.forget H.true_) x)).tag;
        expected = "app";
      };

      "ornament-validate-structured-unknown-field" = {
        expr =
          let
            result = H.validateOrnament DiagnosticsBox {
              name = "BadStructuredDiag";
              constructors.box.fields = [{ keep = "missing"; }];
            };
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code severity path message text;
          };
        expected = {
          ok = false;
          code = "ornament.unknown-field";
          severity = "error";
          path = [
            "datatype:OrnDiagBox"
            "ornament:BadStructuredDiag"
            "constructor:box"
            "field:missing"
          ];
          message = "unknown kept base field";
          text = "hoas.ornament: datatype 'OrnDiagBox' ornament 'BadStructuredDiag' constructor 'box' field 'missing': unknown kept base field";
        };
      };

      "ornament-try-invalid-is-total" = {
        expr =
          let
            result = H.tryOrnament DiagnosticsBox {
              name = "BadTotalDiag";
              constructors.box.fields = [{ keep = "missing"; }];
            };
          in
          {
            inherit (result) ok;
            hasValue = result ? value;
            diagnostics = builtins.length result.diagnostics;
          };
        expected = {
          ok = false;
          hasValue = false;
          diagnostics = 2;
        };
      };

      "ornament-try-valid-builds-value" = {
        expr =
          let
            result = H.tryOrnament DiagnosticsBox {
              name = "GoodTotalDiag";
              constructors.box.fields = [{ keep = "value"; }];
            };
          in
          {
            inherit (result) ok;
            hasValue = result ? value;
            hasForget0 = result.value ? forget0;
          };
        expected = {
          ok = true;
          hasValue = true;
          hasForget0 = true;
        };
      };

      "algOrn-validate-structured-shape-mismatch" = {
        expr =
          let
            result = H.validateAlgOrn {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              D = baseD;
              algebra = H.algRet H.zero;
            };
            diagnostic = firstDiagnostic result;
          in
          {
            inherit (result) ok;
            inherit (diagnostic) code severity path message text;
          };
        expected = {
          ok = false;
          code = "algOrn.shape-mismatch";
          severity = "error";
          path = "root";
          message = "expected arg algebra for descArg, got ret";
          text = "hoas.algOrn: path root: expected arg algebra for descArg, got ret";
        };
      };

      "algOrn-try-invalid-is-total" = {
        expr =
          let
            result = H.tryAlgOrn {
              I = H.unitPrim;
              J = H.nat;
              erase = natToUnitErase;
              D = baseD;
              algebra = H.algRet H.zero;
            };
          in
          {
            inherit (result) ok;
            hasValue = result ? value;
            diagnostics = builtins.length result.diagnostics;
          };
        expected = {
          ok = false;
          hasValue = false;
          diagnostics = 1;
        };
      };

      "ornDesc-invalid-node-still-throws" = {
        expr =
          let
            bad = H.ornI {
              I = H.unitPrim;
              J = H.unitPrim;
              erase = unitErase;
              baseD = H.descRet;
              node = { tag = "invalid-internal-node"; };
            };
          in
          (builtins.tryEval (builtins.deepSeq (H.elab (H.ornDesc bad)) true)).success;
        expected = false;
      };

      "ornament-diagnostics-missing-constructor-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsBox {
            name = "BadMissingConstructor";
            constructors = { };
          })
          "hoas.ornament: datatype 'OrnDiagBox' ornament 'BadMissingConstructor': missing constructor arm 'box'";
        expected = true;
      };

      "ornament-diagnostics-unknown-constructor-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsBox {
            name = "BadUnknownConstructor";
            constructors.box.fields = [{ keep = "value"; }];
            constructors.missing.fields = [ ];
          })
          "hoas.ornament: datatype 'OrnDiagBox' ornament 'BadUnknownConstructor': unknown constructor arm 'missing'";
        expected = true;
      };

      "ornament-diagnostics-unknown-field-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsBox {
            name = "BadUnknownField";
            constructors.box.fields = [{ keep = "missing"; }];
          })
          "hoas.ornament: datatype 'OrnDiagBox' ornament 'BadUnknownField' constructor 'box' field 'missing': unknown kept base field";
        expected = true;
      };

      "ornament-diagnostics-duplicate-output-field-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsBox {
            name = "BadDuplicateOutput";
            constructors.box.fields = [
              { insert = "value"; type = H.bool; }
              { keep = "value"; }
            ];
          })
          "hoas.ornament: datatype 'OrnDiagBox' ornament 'BadDuplicateOutput' constructor 'box' field 'value': duplicate output field";
        expected = true;
      };

      "ornament-diagnostics-out-of-order-field-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsPair {
            name = "BadOutOfOrder";
            constructors.pair.fields = [
              { keep = "right"; }
              { keep = "left"; }
            ];
          })
          "hoas.ornament: datatype 'OrnDiagPair' ornament 'BadOutOfOrder' constructor 'pair' field 'right': keep is out of order; expected field 'left'";
        expected = true;
      };

      "ornament-diagnostics-indexed-branch-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsIndexedPiBase {
            name = "BadIndexedBranch";
            index = {
              J = H.nat;
              erase = diagnosticNatToBoolErase;
            };
            constructors.mk = {
              target = _: H.zero;
              fields = [
                { keep = "next"; }
              ];
            };
          })
          "hoas.ornament: datatype 'OrnDiagIndexedPiBase' ornament 'BadIndexedBranch' constructor 'mk' field 'next': indexed pi keep needs `branchIndex`";
        expected = true;
      };

      "ornament-diagnostics-unsupported-keep-kind-fragment" = {
        expr = hasDiag
          (H.ornamentDiagnostics DiagnosticsBadKeepBase {
            name = "BadUnsupportedKeep";
            constructors.mk.fields = [{ keep = "ghost"; }];
          })
          "hoas.ornament: datatype 'OrnDiagBadKeepBase' ornament 'BadUnsupportedKeep' constructor 'mk' field 'ghost': unsupported keep kind 'proof'";
        expected = true;
      };

      "algOrn-diagnostics-shape-mismatch-fragment" = {
        expr = hasDiag
          (H.algOrnDiagnostics {
            I = H.unitPrim;
            J = H.nat;
            erase = natToUnitErase;
            D = baseD;
            algebra = H.algRet H.zero;
          })
          "hoas.algOrn: path root: expected arg algebra for descArg, got ret";
        expected = true;
      };

      "algOrn-diagnostics-nested-shape-mismatch-fragment" = {
        expr = hasDiag
          (H.algOrnDiagnostics {
            I = H.unitPrim;
            J = H.nat;
            erase = natToUnitErase;
            D = H.descArg H.unitPrim 0 H.nat (_: H.descRec H.descRet);
            algebra = H.algArg (_:
              H.algRec (_:
                H.algArg (x: H.algRet x)));
          })
          "hoas.algOrn: path root.arg.rec: expected ret algebra for descRet, got arg";
        expected = true;
      };

      "leafOrnament-rejects-mu-base" = {
        expr = hasDiag
          (H.leafOrnamentDiagnostics {
            primitive = (H.product "Box" [ (H.field "value" H.nat) ]).T;
            forget = x: x;
            section = x: x;
          })
          "hoas.leafOrnament: leaf ornament `primitive` must be a primitive HOAS type former, not a μ-encoded type; use ornament/functionalOrnament for μ-encoded bases";
        expected = true;
      };

      "leafOrnament-roundtrip" = {
        expr =
          let
            orn = H.leafOrnament {
              primitive = H.string;
              forget = x: x;
              section = x: x;
            };
          in
          orn.forget (orn.section "hello");
        expected = "hello";
      };

      "thunkOrnament-forget-strips-thunk" = {
        expr =
          let
            drv = { type = "derivation"; name = "x"; outPath = "/nix/store/x"; };
            orn = H.thunkOrnament H.derivation;
          in
          (orn.forget (orn.section drv)).outPath;
        expected = "/nix/store/x";
      };

      "thunkOrnament-section-protects-cyclic-drv" = {
        expr =
          let
            cyclic = { type = "derivation"; name = "c"; outPath = "/nix/store/c"; }
              // { self = cyclic; };
            ornamented = (H.thunkOrnament H.derivation).section cyclic;
          in
          (builtins.tryEval (builtins.deepSeq ornamented null)).success;
        expected = true;
      };
    };

}
