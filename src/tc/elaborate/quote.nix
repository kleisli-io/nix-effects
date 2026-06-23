# Quotation overlay for the meta-aware elaborator.
#
# Rigid kernel values delegate to `fx.tc.quote`. `VMeta` is quoted as an
# overlay term head, then the stored elimination spine is replayed through
# the same term constructors that quote uses for `VNe`.
{ self, fx, api, ... }:

let
  Q = fx.tc.quote;
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;

  mkMeta = id: spine: { tag = "meta"; inherit id spine; };

  quote = d: v:
    if self.isVMeta v then quoteSp d (mkMeta v.id [ ]) v.spine
    else if builtins.isAttrs v && (v.tag or null) == "VNe" then
      quoteSp d (T.mkVar (Q.lvl2Ix d v.level)) v.spine
    else Q.quote d v;

  quoteSp = d: head: spine:
    builtins.foldl' (acc: elim: quoteElim d acc elim) head spine;

  quoteElim = d: head: elim:
    let t = elim.tag; in
    if t == "EApp" then T.mkApp head (quote d elim.arg)
    else if t == "EFst" then T.mkFst head
    else if t == "ESnd" then T.mkSnd head
    else if t == "EBootSumElim" then
      T.mkBootSumElim (quote d elim.left) (quote d elim.right) (quote d elim.motive)
        (quote d elim.onLeft)
        (quote d elim.onRight)
        head
    else if t == "EBootJ" then
      T.mkBootJ (quote d elim.type) (quote d elim.lhs) (quote d elim.motive)
        (quote d elim.base)
        (quote d elim.rhs)
        head
    else if t == "EStrEq" then T.mkStrEq head (quote d elim.arg)
    else if t == "EIntEq" then T.mkIntEq head (quote d elim.arg)
    else if t == "EIntLeL" then T.mkIntLe head (quote d elim.arg)
    else if t == "EIntLeR" then T.mkIntLe (quote d elim.arg) head
    else if t == "EDescInd" then
      T.mkDescInd (quote d elim.D) (quote d elim.motive) (quote d elim.step) (quote d elim.i) head
    else if t == "EInterpD" then
      T.mkInterpD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (quote d elim.X)
        (quote d elim.i)
    else if t == "EAllD" then
      T.mkAllD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (if elim.K.tag == "VLevelZero" then T.mkLevelZero else quote d elim.K)
        (quote d elim.X)
        (quote d elim.M)
        (quote d elim.i)
        (quote d elim.d)
    else if t == "EEverywhereD" then
      T.mkEverywhereD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (if elim.K.tag == "VLevelZero" then T.mkLevelZero else quote d elim.K)
        (quote d elim.X)
        (quote d elim.M)
        (quote d elim.ih)
        (quote d elim.i)
        (quote d elim.d)
    else if t == "ELiftElim" then
      T.mkLiftElim
        (if elim.l.tag == "VLevelZero" then T.mkLevelZero else quote d elim.l)
        (if elim.m.tag == "VLevelZero" then T.mkLevelZero else quote d elim.m)
        (quote d elim.eq)
        (quote d elim.A)
        head
    else if t == "ESquashElim" then
      T.mkSquashElim (quote d elim.A) (quote d elim.B) (quote d elim.f) head
    else throw "tc.elaborate.quoteElim: unknown spine tag '${t}'";

  nf = env: tm: quote (builtins.length env) (E.eval env tm);

  type0 = {
    ctx = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
    ty = V.vUnit;
  };
  meta0 = self.mkVMeta 0 [ ] type0;
in
{
  scope = {
    mkMeta = api.leaf {
      value = mkMeta;
      description = "mkMeta: overlay term head for quoted metavariables. This is not a kernel `Tm` constructor; it lives only in `fx.tc.elaborate`'s meta-aware term overlay.";
      signature = "mkMeta : Int -> [ElabTm] -> ElabTm";
      tests = {
        "mkMeta-tag" = {
          expr = (mkMeta 3 [ ]).tag;
          expected = "meta";
        };
        "mkMeta-id" = {
          expr = (mkMeta 7 [ ]).id;
          expected = 7;
        };
      };
    };
    quote = api.leaf {
      value = quote;
      description = "quote d v: meta-aware read-back. Rigid values delegate to `fx.tc.quote`; `VMeta` quotes to `mkMeta id []` with its elimination spine replayed as ordinary term eliminators.";
      signature = "quote : Depth -> ElabVal -> ElabTm";
      tests = {
        "quote-rigid-delegates" = {
          expr = (quote 0 V.vTt).tag;
          expected = "tt";
        };
        "quote-vmeta-head" = {
          expr = (quote 0 meta0).tag;
          expected = "meta";
        };
        "quote-vmeta-head-id" = {
          expr = (quote 0 (self.mkVMeta 11 [ ] type0)).id;
          expected = 11;
        };
        "quote-vmeta-app-spine" = {
          expr = (quote 0 (self.elabApp meta0 V.vTt)).tag;
          expected = "app";
        };
        "quote-vmeta-app-head" = {
          expr = (quote 0 (self.elabApp meta0 V.vTt)).fn.tag;
          expected = "meta";
        };
        "quote-vmeta-fst-spine" = {
          expr = (quote 0 (self.elabFst meta0)).tag;
          expected = "fst";
        };
      };
    };
    quoteSp = api.leaf {
      value = quoteSp;
      description = "quoteSp d head spine: fold `quoteElim` over a stored elimination spine.";
      signature = "quoteSp : Depth -> ElabTm -> [SpineEntry] -> ElabTm";
    };
    quoteElim = api.leaf {
      value = quoteElim;
      description = "quoteElim d head frame: replay one kernel spine frame against an overlay term head, recursively using meta-aware `quote` for frame payloads.";
      signature = "quoteElim : Depth -> ElabTm -> SpineEntry -> ElabTm";
    };
    nf = api.leaf {
      value = nf;
      description = "nf env tm: kernel eval followed by meta-aware quote.";
      signature = "nf : Env -> Tm -> ElabTm";
    };
  };

}
