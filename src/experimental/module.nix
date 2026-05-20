{ self, api, ... }:

api.mk {
  description = "fx.experimental: unstable surfaces under active development — currently the description-side `desc-interp` substrate where FreeFx lives as a μ-tree.";
  doc = ''
    Names, shapes, and laws under this namespace may change without
    deprecation cycles. Sub-modules are promoted out (and renamed)
    once they stabilise.
  '';
  value = {
    "desc-interp" = self."desc-interp";
  };
}
