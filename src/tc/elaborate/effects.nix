# Five scoped meta-effects over the descInterp FreeFx substrate.
#
# `metaEff` is a kernel-typed 5-element `H.variant`. Each op identity
# is a HOAS sum-injection over its right-nested desugaring (see
# `tc/hoas/elaborate.nix:586-601`); the Nix-host payload rides as a
# sidecar attrset on the injection term. The substrate does not type-
# check payload semantics, but the dispatch-tag space is honest and
# `kernel.send`'s `_htag` assertion accepts the op.
#
# Refs: Abel-Pientka (2011) §5 (meta-context Δ as rewrite state);
# Gundry-McBride-McKinna (2010) §6.2 (Optimist's Lemma — postponed
# constraint is a monotone wait, distinct from `typeError` as proof-
# of-unsolvability).
{ fx, lib, api, ... }:

let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;

  # Payload types are uniformly `H.unit`: payload semantics (kernel
  # `Val`s, `Tm`s, `Constraint` records) live in handler-land and
  # travel via the sidecar on the HOAS op term.
  metaEff = H.variant [
    { tag = "force"; type = H.unit; }
    { tag = "getMetas"; type = H.unit; }
    { tag = "assignMeta"; type = H.unit; }
    { tag = "emitConstraint"; type = H.unit; }
    { tag = "getConstraints"; type = H.unit; }
    { tag = "freshMeta"; type = H.unit; }
  ];

  # All meta-effects return Nix-host opaque values; kernel-level resp
  # collapses to `H.unit`.
  metaResp = H.lam "_op" metaEff (_op: H.unit);

  send_ = K.send metaEff metaResp;

  branchTypes = map (b: b.type) metaEff.branches;
  numBranches = builtins.length branchTypes;

  # Right-arm kernel type at depth i — the nested `sum` of
  # `branchTypes[i+1..n-1]`. Undefined at i = n-1 (no right arm).
  restAt = i:
    let
      suffix = lib.drop (i + 1) branchTypes;
      m = builtins.length suffix;
    in
    if m == 1 then builtins.head suffix
    else
      let last_ = builtins.elemAt suffix (m - 1); in
      builtins.foldl'
        (acc: j:
          let bt = builtins.elemAt suffix (m - 2 - j);
          in H.sum bt acc
        )
        last_
        (builtins.genList (x: x) (m - 1));

  # `injTag i v` — i `inr`-wraps then `inl` at depth i (or bare v at
  # the rightmost branch i = n-1).
  injTag = i: v:
    assert (i >= 0 && i < numBranches)
      || throw "tc.elaborate.effects.injTag: index ${toString i} out of [0, ${toString numBranches})";
    let
      Ti = builtins.elemAt branchTypes i;
      innermost =
        if i == numBranches - 1
        then v
        else H.inl v;
    in
    builtins.foldl'
      (acc: kOff:
        let
          k = i - 1 - kOff;
          Tk = builtins.elemAt branchTypes k;
        in
        H.inr acc
      )
      innermost
      (builtins.genList (x: x) i);

  # `H.inl`/`H.inr` desugar through SumDT.Left/Right application, so
  # the injection's `_htag` is `"app"`. Extra attrs survive `kernel.
  # send`'s `impureCon` wrap and are reachable at `.d.term.fst`.
  mkOp = tagIdx: opTag: payload:
    (injTag tagIdx H.tt) // { _opTag = opTag; inherit payload; };

  force = v: send_ (mkOp 0 "force" { inherit v; });

  getMetas = send_ (mkOp 1 "getMetas" { });

  assignMeta = id: tm: send_ (mkOp 2 "assignMeta" { inherit id tm; });

  emitConstraint = c: send_ (mkOp 3 "emitConstraint" { inherit c; });

  getConstraints = send_ (mkOp 4 "getConstraints" { });

  freshMeta = type: send_ (mkOp 5 "freshMeta" { inherit type; });

  # Ceremonial kernel handler: `λ_op. λ_s. tt` discharges the bridge's
  # "handler is a kernel HOAS term" obligation. Per-op semantics live
  # Nix-side in `dispatchMeta` (`runElab.nix`), which reads `op`'s
  # sidecar `_opTag` / `payload` and threads Δ through `ctx.state`.
  handle_MetaTy =
    H.forall "_op" metaEff (_op:
      H.forall "_s" H.unit (_s: H.unit));

  handle_Meta = H.ann
    (H.lam "_op" metaEff (_op:
      H.lam "_s" H.unit (_s: H.tt)))
    handle_MetaTy;

in
{
  scope = {
    metaEff = api.leaf {
      value = metaEff;
      description = "metaEff: kernel-typed effect signature for the elaborator's 5 meta-effects — 5-element `H.variant` over tags `force` / `getMetas` / `assignMeta` / `emitConstraint` / `getConstraints`. Payload types are uniformly `H.unit`; semantic payload data rides in the Nix-host sentinel attached to the `op` argument.";
      signature = "metaEff : Hoas U";
      tests = {
        "metaEff-htag" = { expr = metaEff._htag; expected = "variant"; };
        "metaEff-branch-count" = {
          expr = builtins.length metaEff.branches;
          expected = 6;
        };
        "metaEff-tags" = {
          expr = map (b: b.tag) metaEff.branches;
          expected = [ "force" "getMetas" "assignMeta" "emitConstraint" "getConstraints" "freshMeta" ];
        };
      };
    };
    metaResp = api.leaf {
      value = metaResp;
      description = "metaResp: response-type function for `metaEff` — kernel-typed `λ_op : metaEff. H.unit`. All five meta-effects return Nix-host opaque values; the kernel-level response is uniformly unit.";
      signature = "metaResp : Hoas (metaEff -> U)";
      tests = {
        "metaResp-is-lam" = { expr = metaResp._htag; expected = "lam"; };
      };
    };
    force = api.leaf {
      value = force;
      description = "force v: send-emitter requesting Δ-aware reduction of `v`. Kernel `Val`s pass through unchanged; `VMeta { id; spine; type }` is reduced via `delta[id] · spine` when `id` is solved in Δ, else returned unchanged. Response shape: `ElabVal`.";
      signature = "force : ElabVal -> Comp ElabVal";
      tests = {
        "force-emits-impure" = {
          expr = (force fx.tc.value.vTt).d._htag;
          expected = "boot-inr";
        };
        "force-op-is-hoas" = {
          expr = (force fx.tc.value.vTt).d.term.fst.a._htag;
          expected = "app";
        };
        "force-op-tag" = {
          expr = (force fx.tc.value.vTt).d.term.fst._opTag;
          expected = "force";
        };
        "force-payload-carries-value" = {
          expr = (force fx.tc.value.vTt).d.term.fst.payload.v == fx.tc.value.vTt;
          expected = true;
        };
      };
    };
    getMetas = api.leaf {
      value = getMetas;
      description = "getMetas: send-emitter reading the current meta-context Δ. Response shape: `Δ : { <metaId> = { tm; type } | null }`.";
      signature = "getMetas : Comp Delta";
      tests = {
        "getMetas-op-is-hoas" = {
          expr = getMetas.d.term.fst.a._htag;
          expected = "app";
        };
        "getMetas-op-tag" = {
          expr = getMetas.d.term.fst._opTag;
          expected = "getMetas";
        };
      };
    };
    assignMeta = api.leaf {
      value = assignMeta;
      description = "assignMeta id tm: send-emitter extending Δ with `id ↦ tm`. Wakes any watchers registered in `mentions[id]` (per Abel-Pientka, section 7) when the assignment lands. Response shape: unit.";
      signature = "assignMeta : Int -> Tm -> Comp Unit";
      tests = {
        "assignMeta-op-tag" = {
          expr = (assignMeta 0 null).d.term.fst._opTag;
          expected = "assignMeta";
        };
        "assignMeta-payload-id" = {
          expr = (assignMeta 7 "tm-stub").d.term.fst.payload.id;
          expected = 7;
        };
        "assignMeta-payload-tm" = {
          expr = (assignMeta 0 "tm-stub").d.term.fst.payload.tm;
          expected = "tm-stub";
        };
      };
    };
    emitConstraint = api.leaf {
      value = emitConstraint;
      description = "emitConstraint c: send-emitter appending `c` to the constraint queue 𝒦. Distinct from `typeError` (a type-error is proof of unsolvability; a postponed constraint is a monotone wait per Optimist's Lemma, GMM section 6.2 Lemma 4). Response shape: the allocated constraint id.";
      signature = "emitConstraint : Constraint -> Comp Int";
      tests = {
        "emitConstraint-op-tag" = {
          expr = (emitConstraint { lhs = null; rhs = null; }).d.term.fst._opTag;
          expected = "emitConstraint";
        };
      };
    };
    getConstraints = api.leaf {
      value = getConstraints;
      description = "getConstraints: send-emitter reading the current constraint queue 𝒦. Response shape: `𝒦 : [Constraint]`.";
      signature = "getConstraints : Comp [Constraint]";
      tests = {
        "getConstraints-op-tag" = {
          expr = getConstraints.d.term.fst._opTag;
          expected = "getConstraints";
        };
      };
    };
    freshMeta = api.leaf {
      value = freshMeta;
      description = "freshMeta type: allocate a new metavariable hole in Δ of the given type. Response shape: VMeta.";
      signature = "freshMeta : MetaType -> Comp VMeta";
      tests = {
        "freshMeta-op-tag" = {
          expr = (freshMeta { ctx = { }; ty = fx.tc.value.vUnit; }).d.term.fst._opTag;
          expected = "freshMeta";
        };
      };
    };
    handle_Meta = api.leaf {
      value = handle_Meta;
      description = "handle_Meta: kernel HOAS shell `λ_op. λ_s. tt` for the meta-effects bridge. Paired with `runElab`'s `dispatchMeta`, which carries the actual per-op interpretation Nix-side.";
      tests = {
        "handle_Meta-htag" = {
          expr = handle_Meta._htag;
          expected = "ann";
        };
        "handle_Meta-elaborates" = {
          expr = (builtins.tryEval (fx.tc.eval.eval [ ] (H.elab handle_Meta)).tag).value;
          expected = "VLam";
        };
      };
    };
    handle_MetaTy = api.leaf {
      value = handle_MetaTy;
      description = "handle_MetaTy: `Π(_op:metaEff). Π(_s:Unit). Unit`. Unit codomain reflects that `outputVal` carries no info for meta-effects — Δ updates and responses flow Nix-side via `dispatchMeta`.";
      tests = {
        "handle_MetaTy-well-formed" = {
          expr = !((H.inferHoas handle_MetaTy) ? error);
          expected = true;
        };
        "handle_Meta-checks-against-handle_MetaTy" = {
          expr = !((H.checkHoas handle_MetaTy handle_Meta) ? error);
          expected = true;
        };
      };
    };
  };

}
