# Live regression guard: every diag Hint's docLink resolves to HTTP 200.
# Each Hint now has its own per-key page at
# `/nix-effects/diag-hints/<slug>`, so a successful fetch is the sole
# acceptance criterion. Gated on KLEISLI_DOCS_BASE so sandboxed builds
# without network skip cleanly.
#
#   KLEISLI_DOCS_BASE=https://docs.kleisli.io \
#     nix build -f . nix.nix-effects.tests.docs-resolves --impure
{ pkgs, lib, src }:

let
  enable = builtins.getEnv "KLEISLI_DOCS_BASE" != "";

  hints = src.diag.hints.hints;
  links = lib.unique (lib.mapAttrsToList (_: h: h.docLink) hints);

  probeScript = url: ''
    status=$(curl --silent --location --output /dev/null \
              --write-out '%{http_code}' "${url}")
    if [ "$status" != "200" ]; then
      echo "FAIL ${url}: HTTP $status"
      failed=1
    else
      echo "ok   ${url}"
    fi
  '';

in
  if !enable then
    pkgs.runCommand "docs-resolves-skipped" { } ''
      printf 'skipped: set KLEISLI_DOCS_BASE to enable live docs probes\n' > $out
    ''
  else
    # FOD: pinned output hash legitimises network access in the build sandbox.
    # Probe failure exits before $out is written, so the build fails.
    pkgs.runCommand "docs-resolves" {
      nativeBuildInputs = [ pkgs.curl pkgs.cacert ];
      outputHashAlgo = "sha256";
      outputHashMode = "flat";
      outputHash = "sha256-3FG4yWwtdF3zvVWQ2ZAjCkgv0kcSNZlUjgYy/b+X/CI=";
      SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
    } ''
      set -eu
      failed=0
      ${lib.concatMapStringsSep "\n" probeScript links}
      if [ "$failed" = "1" ]; then
        echo "One or more diag Hint docLinks failed verification."
        exit 1
      fi
      printf 'ok\n' > $out
    ''
