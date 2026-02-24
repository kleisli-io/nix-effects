# Typed Derivation: formally verified service configuration
#
# A config-templated service where the MLTT kernel verifies cross-field
# invariants BEFORE the service script is generated. The key constraint:
# public-facing services (bind 0.0.0.0) must use HTTPS. The kernel proves
# this for each concrete config via Refl : Eq(Bool, policy(cfg), true).
#
# Tier 2 — the kernel computes the effective protocol: if bind is public,
#   it forces HTTPS regardless of what the config says.
# Tier 3 — the kernel constructs a proof that the full policy holds.
#   Invalid configs produce Eq(Bool, false, true) which the kernel rejects.
#
# Build the valid service:
#   nix build --impure --expr '
#     let pkgs = import <nixpkgs> {};
#         fx = import ./nix-effects { inherit (pkgs) lib; };
#     in (import ./nix-effects/examples/typed-derivation.nix { inherit fx pkgs; }).api-server'
#   ./result/bin/api-server
#
# Try the insecure service (fails at eval, never built):
#   nix build --impure --expr '
#     let pkgs = import <nixpkgs> {};
#         fx = import ./nix-effects { inherit (pkgs) lib; };
#     in (import ./nix-effects/examples/typed-derivation.nix { inherit fx pkgs; }).insecure-public'
{ fx, pkgs, ... }:

let
  H = fx.types.hoas;
  v = fx.types.verified;
  elaborateValue = fx.types.elaborateValue;

  # ===== Service Configuration Type =====
  # Fields alphabetical — record elaborates to nested Sigma in this order.

  ServiceConfig = H.record [
    { name = "bind";     type = H.string; }
    { name = "logLevel"; type = H.string; }
    { name = "name";     type = H.string; }
    { name = "port";     type = H.string; }
    { name = "protocol"; type = H.string; }
  ];

  # ===== Policy Constants =====

  mkStrList = builtins.foldl' (acc: s: H.cons H.string (v.str s) acc) (H.nil H.string);
  allowedBinds     = mkStrList [ "127.0.0.1" "0.0.0.0" "::1" ];
  allowedProtocols = mkStrList [ "http" "https" ];
  allowedLogLevels = mkStrList [ "debug" "info" "warn" "error" ];
  allowedPorts     = mkStrList [ "80" "443" "3000" "5000" "8080" "8443" ];

  # ===== Tier 2: Verified Computation =====
  #
  # effectiveProtocol : ServiceConfig → String
  # The kernel computes the protocol the service will actually use.
  # Public bind (0.0.0.0) forces HTTPS — the kernel enforces this by
  # construction, not just validation. The extracted Nix function always
  # returns the right answer because the kernel proved it total and correct.

  effectiveProtocol = v.verify (H.forall "s" ServiceConfig (_: H.string))
    (v.fn "s" ServiceConfig (s:
      v.if_ H.string (v.strEq (v.field ServiceConfig "bind" s) (v.str "0.0.0.0")) {
        then_ = v.str "https";
        else_ = v.field ServiceConfig "protocol" s;
      }));

  # ===== Tier 3: Machine-Checked Proof =====
  #
  # The policy as an HOAS term — not extracted, used to build proof obligations.
  # Checks: bind ∈ allowed, protocol ∈ allowed, logLevel ∈ allowed, port ∈ allowed,
  # and the cross-field invariant: bind == 0.0.0.0 → protocol == https.

  policyBody = v.fn "s" ServiceConfig (s:
    v.if_ H.bool (v.strElem (v.field ServiceConfig "bind" s) allowedBinds) {
      then_ = v.if_ H.bool (v.strElem (v.field ServiceConfig "protocol" s) allowedProtocols) {
        then_ = v.if_ H.bool (v.strElem (v.field ServiceConfig "logLevel" s) allowedLogLevels) {
          then_ = v.if_ H.bool (v.strElem (v.field ServiceConfig "port" s) allowedPorts) {
            then_ = v.if_ H.bool (v.strEq (v.field ServiceConfig "bind" s) (v.str "0.0.0.0")) {
              then_ = v.strEq (v.field ServiceConfig "protocol" s) (v.str "https");
              else_ = v.true_;
            };
            else_ = v.false_;
          };
          else_ = v.false_;
        };
        else_ = v.false_;
      };
      else_ = v.false_;
    });
  policyAnn = H.ann policyBody (H.forall "s" ServiceConfig (_: H.bool));

  # ===== Proof-Gated Service Builder =====
  #
  # For a concrete config, the kernel:
  #   1. Encodes the Nix attrset as an HOAS record (nested Sigma pairs)
  #   2. Applies the policy function to it
  #   3. Normalizes the result via NbE
  #   4. Checks Refl : Eq(Bool, result, true)
  #
  # Valid config → result normalizes to true → Refl accepted → service built
  # Invalid config → result normalizes to false → Refl rejected → eval aborts

  mkVerifiedService = cfg:
    let
      cfgHoas  = elaborateValue ServiceConfig cfg;
      applied  = H.app policyAnn cfgHoas;
      proofTy  = H.eq H.bool applied H.true_;
      checked  = H.checkHoas proofTy H.refl;
      protocol = effectiveProtocol cfg;
    in if checked ? error
      then throw "Proof rejected: service '${cfg.name}' violates policy (bind ∈ allowed ∧ protocol ∈ allowed ∧ port ∈ allowed ∧ public → https)"
      else pkgs.writeShellScriptBin cfg.name ''
        echo "${cfg.name} listening on ${protocol}://${cfg.bind}:${cfg.port}"
        echo "log level: ${cfg.logLevel}"
        echo ""
        echo "# This service configuration was verified by an MLTT proof checker."
        echo "# The kernel proved: bind ∈ {127.0.0.1, 0.0.0.0, ::1}"
        echo "#                    protocol ∈ {http, https}"
        echo "#                    port ∈ {80, 443, 3000, 5000, 8080, 8443}"
        echo "#                    public bind (0.0.0.0) → protocol = https"
        exec ${pkgs.python3}/bin/python3 -c "
import http.server, sys
class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-Type', 'text/plain')
        self.end_headers()
        self.wfile.write(b'${cfg.name} ok\n')
    def log_message(self, fmt, *args):
        pass  # quiet
print('${cfg.name}: ${protocol}://${cfg.bind}:${cfg.port}', file=sys.stderr)
http.server.HTTPServer(('${cfg.bind}', ${cfg.port}), Handler).serve_forever()
"
      '';

in {
  # Builds — localhost HTTP on port 8080 satisfies all policy constraints.
  # Run: ./result/bin/api-server
  # Test: curl http://127.0.0.1:8080/
  api-server = mkVerifiedService {
    name = "api-server"; bind = "127.0.0.1";
    port = "8080"; protocol = "http"; logLevel = "info";
  };

  # Fails at eval — bind 0.0.0.0 with protocol http violates the
  # cross-field invariant (public bind requires HTTPS). The kernel
  # normalizes policy(cfg) to false and rejects the Refl proof.
  insecure-public = mkVerifiedService {
    name = "insecure-public"; bind = "0.0.0.0";
    port = "80"; protocol = "http"; logLevel = "debug";
  };
}
