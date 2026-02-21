# UID/GID Allocation: catching ID collisions at eval time
#
# NixOS assigns each system service a UID and GID. When two services
# get the same ID, the result is a silent privilege escalation — one
# service runs as the other's user after reboot. This has caused real
# production failures:
#
#   nixpkgs#112647 — Nextcloud assigned UID 1001, then human user bob
#   also got UID 1001. After reboot phpfpm-nextcloud ran as bob.
#
#   nixpkgs#3727  — ids.nix collisions since 2014: gitolite/firebird,
#   unifi/docker, tss/dhcpd sharing IDs.
#
# The NixOS community independently reinvented eval-time allocation:
#   alloc.nix  — discourse.nixos.org/t/alloc-nix-a-tool-to-help-you-
#                allocate-ranges-to-services/72603
#   port alloc — discourse.nixos.org/t/nixos-port-allocation/74953
#                "makes port collisions an evaluation error"
#
# This module provides `checkAllocations`: a function that takes a
# declarative user/group spec and validates UID/GID uniqueness using
# nix-effects linear resources. No monadic bind chains — you pass a
# plain attrset and get back a validated config or a throw.
#
#   checkAllocations {
#     users.nginx    = { uid = 400; description = "Nginx web server"; };
#     users.postgres = { uid = 401; description = "PostgreSQL database"; };
#     groups.nginx   = { gid = 400; members = [ "nginx" ]; };
#     groups.web     = { gid = 500; members = [ "nginx" "app" ]; };
#   }
#   # => { users = { nginx = { uid = 400; ... }; ... }; groups = { ... }; }
#   # or throws: "UID collision: 400 claimed by nginx and redis"
#
#   nix-instantiate --eval --strict -E \
#     'let pkgs = import <nixpkgs> {}; in import ./linear-resource.nix {
#        fx = import ../. { inherit (pkgs) lib; }; lib = pkgs.lib; }'
{ fx, lib ? builtins, pkgs ? null, ... }:

let
  inherit (fx) pure bind handle adaptHandlers;
  inherit (fx.effects) linear state typecheck;
  inherit (fx.types) mkType refined;

  # =========================================================================
  # TYPES
  # =========================================================================

  ServiceName = refined "ServiceName"
    (mkType { name = "String"; check = builtins.isString; })
    (s: builtins.stringLength s > 0 && builtins.match "[a-z][-a-z0-9]*" s != null);

  SystemId = refined "SystemID"
    (mkType { name = "Int"; check = builtins.isInt; })
    (n: n >= 1 && n <= 65534);

  # =========================================================================
  # INTERNAL: composed handler
  # =========================================================================

  linearLens    = { get = s: s.linear;     set = s: v: s // { linear = v; }; };
  typecheckLens = { get = s: s.typeErrors; set = s: v: s // { typeErrors = v; }; };
  configLens    = { get = s: s.config;     set = s: v: s // { config = v; }; };

  allHandlers =
    (adaptHandlers linearLens linear.handler)
    // (adaptHandlers typecheckLens typecheck.collecting)
    // (adaptHandlers configLens state.handler);

  mkInitialState = { users = {}; groups = {}; };

  composedReturn = value: st:
    let lr = linear.return value st.linear;
    in { value = lr.value; state = st // { linear = lr.state; }; };

  runComp = comp: handle {
    return = composedReturn;
    handlers = allHandlers;
    state = { linear = linear.initialState; typeErrors = []; config = mkInitialState; };
  } comp;

  # =========================================================================
  # INTERNAL: compile a declarative spec into a linear computation
  # =========================================================================
  #
  # The key idea: each unique UID value gets ONE linear token.
  # Every user that claims that UID consumes the token. If two users
  # claim the same UID, the second consume fails: exceeded-bound.
  # Same for GIDs.

  compileSpec = { users ? {}, groups ? {} }:
    let
      userNames  = builtins.attrNames users;
      groupNames = builtins.attrNames groups;

      # Collect all UID values. Duplicates are intentionally kept — the
      # linear handler will catch them when two users try to consume
      # the same token.
      allUids = lib.unique (map (n: users.${n}.uid) userNames);
      allGids = lib.unique (map (n: groups.${n}.gid) groupNames);

      # Phase 1: Allocate one linear token per unique UID value.
      allocUidTokens = builtins.foldl' (acc: uid:
        bind acc (pool:
        bind (SystemId.validate uid) (_:
        bind (linear.acquire { resource = uid; maxUses = 1; }) (token:
          pure (pool // { ${toString uid} = token; })))))
        (pure {})
        allUids;

      # Phase 2: Allocate one linear token per unique GID value.
      # Each GID must be assigned to exactly one group (maxUses = 1).
      # If two groups declare the same GID, the second consume fails.
      allocGidTokens = uidPool:
        builtins.foldl' (acc: gid:
          bind acc (pool:
          bind (SystemId.validate gid) (_:
          bind (linear.acquire { resource = gid; maxUses = 1; }) (token:
            pure (pool // { ${toString gid} = token; })))))
          (pure {})
          allGids;

      # Phase 3: Assign UIDs — each user consumes its UID's token.
      assignUsers = uidPool:
        builtins.foldl' (acc: name:
          let u = users.${name}; in
          bind acc (_:
          bind (ServiceName.validate name) (_:
          bind (linear.consume uidPool.${toString u.uid}) (uid:
          bind (state.modify (cfg: cfg // {
            users = cfg.users // {
              ${name} = {
                inherit uid;
                description = u.description or name;
                isSystemUser = u.isSystemUser or true;
                group = u.group or name;
              };
            };
          })) (_:
            pure uid)))))
          (pure null)
          userNames;

      # Phase 4: Assign GIDs — each group consumes its GID's token.
      assignGroups = gidPool:
        builtins.foldl' (acc: name:
          let g = groups.${name}; in
          bind acc (_:
          bind (linear.consume gidPool.${toString g.gid}) (gid:
          bind (state.modify (cfg: cfg // {
            groups = cfg.groups // {
              ${name} = {
                inherit gid;
                members = g.members or [ name ];
              };
            };
          })) (_:
            pure gid))))
          (pure null)
          groupNames;

    in
      bind allocUidTokens (uidPool:
      bind (allocGidTokens uidPool) (gidPool:
      bind (assignUsers uidPool) (_:
      bind (assignGroups gidPool) (_:
        pure "validated"))));

  # =========================================================================
  # PUBLIC API
  # =========================================================================

  # Format a LinearityError into a human-readable message identifying
  # which services collided.
  formatError = result: config:
    if result.error == "exceeded-bound" then
      let
        id = toString result.resource;
        claimants =
          if config ? users then
            builtins.filter (n: toString config.users.${n}.uid == id)
              (builtins.attrNames (config.users or {}))
            ++ builtins.filter (n: toString config.groups.${n}.gid == id)
              (builtins.attrNames (config.groups or {}))
          else [ "unknown" ];
      in "ID collision: ${id} claimed by ${builtins.concatStringsSep " and " (lib.unique claimants)}"
    else if result.error == "usage-mismatch" then
      "Unused ID allocations:\n"
      + builtins.concatStringsSep "\n" (map (d:
          "  - ${toString d.resource}: expected ${toString d.expected} uses, got ${toString d.actual}"
        ) result.details)
    else "Linear resource error: ${result.error}";

  # checkAllocations : { users, groups } -> { users, groups }
  #
  # Takes a declarative user/group specification. Returns the validated
  # config attrset (suitable for use in NixOS users.users / users.groups)
  # or throws with a descriptive error identifying the collision.
  #
  # Each UID and GID must be unique across all users/groups respectively.
  # Type validation runs in the same pass: invalid names, out-of-range
  # IDs, and missing fields are all caught.
  checkAllocations = spec:
    let
      result = runComp (compileSpec spec);
      hasTypeErrors = result.state.typeErrors != [];
      hasLinearError = result.value ? _tag
                       && result.value._tag == "LinearityError";
      # When an abort (exceeded-bound) happens mid-computation, the
      # return clause may also report unused tokens from phases that
      # never ran. The real error is in the `original` field.
      rootError =
        if hasLinearError
           && result.value.error == "usage-mismatch"
           && result.value ? original
           && builtins.isAttrs result.value.original
           && result.value.original ? _tag
           && result.value.original._tag == "LinearityError"
        then result.value.original
        else result.value;
    in
      if hasLinearError then
        throw (formatError rootError spec)
      else if hasTypeErrors then
        throw ("Invalid service config:\n"
          + builtins.concatStringsSep "\n"
              (map (e:
                if builtins.isString e then "  - ${e}"
                else if builtins.isAttrs e && e ? message then "  - ${e.message}"
                else "  - ${builtins.toJSON e}"
              ) result.state.typeErrors))
      else
        result.state.config;

  # =========================================================================
  # USAGE — separate modules merged at the top level
  # =========================================================================
  #
  # Each team writes its service config independently. The collision
  # only appears after NixOS merges the modules.

  webModule = {
    users.nginx = { uid = 400; description = "Nginx web server"; };
    groups.nginx = { gid = 400; members = [ "nginx" ]; };
    groups.web   = { gid = 500; members = [ "nginx" "app" ]; };
  };

  dbModule = {
    users.postgres = { uid = 401; description = "PostgreSQL database"; };
    groups.postgres = { gid = 401; members = [ "postgres" ]; };
  };

  cacheModule = {
    users.redis = { uid = 402; description = "Redis cache"; };
    groups.redis = { gid = 402; members = [ "redis" ]; };
  };

  # All UIDs unique → succeeds
  validServer = checkAllocations (
    builtins.foldl' lib.recursiveUpdate {} [ webModule dbModule cacheModule ]
  );

  # nixpkgs#112647: cloud team provisions Nextcloud, HR onboards bob.
  # Neither checks the other's UIDs — collision hidden in the merge.
  cloudModule = {
    users.nextcloud = { uid = 999; description = "Nextcloud"; };
    groups.nextcloud = { gid = 999; members = [ "nextcloud" ]; };
  };

  hrModule = {
    users.bob = { uid = 999; description = "Human user";
                  isSystemUser = false; };
  };

  buggySpec = builtins.foldl' lib.recursiveUpdate {} [ cloudModule hrModule ];

in {
  inherit checkAllocations;
  # Valid config round-trips; buggy config throws at eval time
  allPass = validServer.users.nginx.uid == 400
            && !(builtins.tryEval (checkAllocations buggySpec)).success;
} // (if pkgs == null then {} else {
  # nix build .#userConfig  — succeeds: all UIDs unique
  userConfig =
    let manifest = builtins.toJSON validServer;
    in pkgs.stdenv.mkDerivation {
      name = "nixos-user-config";
      dontUnpack = true;
      installPhase = ''
        mkdir -p $out
        echo '${manifest}' > $out/users.json
      '';
    };

  # nix build .#buggyConfig  — fails at eval time:
  #   "ID collision: 999 claimed by bob and nextcloud"
  #
  # The nixpkgs#112647 bug: two modules independently chose UID 999.
  # Currently NixOS only catches this at boot when systemd units
  # conflict. With linear tracking the collision fails at eval time.
  buggyConfig =
    let manifest = builtins.toJSON (checkAllocations buggySpec);
    in pkgs.stdenv.mkDerivation {
      name = "buggy-user-config";
      dontUnpack = true;
      installPhase = ''
        mkdir -p $out
        echo '${manifest}' > $out/users.json
      '';
    };
})
