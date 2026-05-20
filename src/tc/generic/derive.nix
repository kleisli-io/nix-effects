# Generic derived artifacts from normalized datatype metadata.
{ self, fx, api, ... }:

let
  inherit (api) mk;

  H  = fx.tc.hoas;
  HI = fx.tc.hoas._internal._indexed;

  typeOf = x:
    if builtins.isAttrs x && x ? T then x.T else x;

  peelSpine = node: args:
    if builtins.isAttrs node && (node._htag or null) == "app"
    then peelSpine node.fn ([ node.arg ] ++ args)
    else { head = node; inherit args; };

  takeLast = n: xs:
    let len = builtins.length xs;
    in builtins.genList (i: builtins.elemAt xs (len - n + i)) n;

  datatypeName = x:
    let r = builtins.tryEval (self.datatypeInfo x);
    in if r.success then r.value.name else null;

  typeDescriptor = ty:
    let
      t = typeOf ty;
      tag = if builtins.isAttrs t then t._htag or null else null;
      name = datatypeName t;
    in
      if !builtins.isAttrs t then { kind = "unknown"; }
      else if name == "Nat" then { kind = "nat"; }
      else if name == "Bool" then { kind = "bool"; }
      else if tag == "string" then { kind = "string"; }
      else if tag == "int" then { kind = "int"; }
      else if tag == "float" then { kind = "float"; }
      else if tag == "attrs" then { kind = "attrs"; }
      else if tag == "path" then { kind = "path"; }
      else if tag == "function" then { kind = "function"; }
      else if tag == "any" then { kind = "any"; }
      else if tag == "unit" then { kind = "unit"; }
      else if tag == "u" then { kind = "universe"; }
      else if tag == "list" then {
        kind = "list";
        elem = typeDescriptor t.elem;
      }
      else if tag == "sum" then {
        kind = "sum";
        left = typeDescriptor t.left;
        right = typeDescriptor t.right;
      }
      else if tag == "app" then
        let
          spine = peelSpine t [];
          headName = datatypeName spine.head;
          args = spine.args;
        in
          if headName == "List" && builtins.length args >= 1 then {
            kind = "list";
            elem = typeDescriptor (builtins.elemAt args 0);
          }
          else if headName == "Sum" && builtins.length args >= 2 then
            let payloadArgs = takeLast 2 args; in {
              kind = "sum";
              left = typeDescriptor (builtins.elemAt payloadArgs 0);
              right = typeDescriptor (builtins.elemAt payloadArgs 1);
            }
          else if headName != null then {
            kind = "datatype";
            name = headName;
            args = map typeDescriptor args;
          }
          else { kind = "hoas"; inherit tag; }
      else if name != null then { kind = "datatype"; inherit name; }
      else { kind = "hoas"; inherit tag; };

  fieldTypeDescriptor = f:
    if f.kind == "recAt" then { kind = "recursive"; }
    else if f.kind == "pi" || f.kind == "piD" || f.kind == "piAt" || f.kind == "piDAt" then { kind = "function"; }
    else if f ? type && f.type != null then typeDescriptor f.type
    else { kind = "dependent"; };

  fieldDescriptor = f: {
    inherit (f) name kind index;
    level = f.level or null;
    role = f.role or null;
    source = f.source or null;
    proof = f.proof or ((f.eq or null) != null);
    recursiveIndex = (f.idxFn or null) != null;
    branchIndex = (f.branchIdxFn or null) != null;
    dependentType =
      f.kind == "dataD" || f.kind == "piD" || f.kind == "piDAt";
    type = fieldTypeDescriptor f;
  };

  constructorDescriptor = c: {
    inherit (c) name index;
    targetIndex = (c.targetIdx or null) != null;
    fields = map fieldDescriptor (c.fields or []);
  };

  schemaForType = tyDesc:
    if tyDesc.kind == "nat" || tyDesc.kind == "int" then { type = "integer"; }
    else if tyDesc.kind == "bool" then { type = "boolean"; }
    else if tyDesc.kind == "string" || tyDesc.kind == "path" then { type = "string"; }
    else if tyDesc.kind == "float" then { type = "number"; }
    else if tyDesc.kind == "attrs" then { type = "object"; additionalProperties = true; }
    else if tyDesc.kind == "unit" then { type = "null"; }
    else if tyDesc.kind == "list" then {
      type = "array";
      items = schemaForType tyDesc.elem;
    }
    else if tyDesc.kind == "sum" then {
      oneOf = [ (schemaForType tyDesc.left) (schemaForType tyDesc.right) ];
    }
    else if tyDesc.kind == "recursive" then { "$ref" = "#"; }
    else if tyDesc.kind == "datatype" then { "$ref" = "#/definitions/${tyDesc.name}"; }
    else {};

  fieldSchema = f:
    if f.kind == "recAt" then { "$ref" = "#"; }
    else schemaForType (fieldTypeDescriptor f);

  constructorSchema = c:
    let
      fields = c.fields or [];
      fieldProps = builtins.listToAttrs (map (f: {
        name = f.name;
        value = fieldSchema f;
      }) fields);
    in {
      type = "object";
      additionalProperties = false;
      required = [ "_con" ] ++ map (f: f.name) fields;
      properties = {
        _con = { const = c.name; };
      } // fieldProps;
    };

  dependencyRoles = [
    "dependency"
    "depends-on"
    "dependency-ref"
    "dependency-reference"
  ];

  isDependencyRole = role:
    role != null && builtins.elem role dependencyRoles;

  isDataField = f:
    f.kind == "data" || f.kind == "dataD";

  childPath = path: name:
    if path == "$" then "$.${name}" else "${path}.${name}";

  sourceOf = x:
    x.source or null;

  fieldNode = info: path: f: {
    id = path;
    inherit path;
    kind = "field";
    con = null;
    constructor = null;
    datatype = info.name;
    indexed = info.indexed or false;
    field = f.name;
    fieldKind = f.kind;
    role = f.role or null;
    source = sourceOf f;
    proof = f.proof or false;
    recursiveIndex = (f.idxFn or null) != null;
    branchIndex = (f.branchIdxFn or null) != null;
    type = fieldTypeDescriptor f;
  };

  constructorNode = info: path: con: {
    id = path;
    inherit path;
    kind = "constructor";
    con = con.name;
    constructor = con.name;
    datatype = info.name;
    indexed = info.indexed or false;
    index = typeDescriptor info.indexTy;
    source = sourceOf con;
    targetIndex = (con.targetIdx or null) != null;
  };

  fieldEdge = path: f: kind: {
    from = path;
    to = childPath path f.name;
    field = f.name;
    role = f.role or null;
    inherit kind;
    source = sourceOf f;
    proof = f.proof or false;
    type = fieldTypeDescriptor f;
    recursiveIndex = (f.idxFn or null) != null;
    branchIndex = (f.branchIdxFn or null) != null;
  };

  dependencyFieldResult = info: path: f:
    let to = childPath path f.name; in {
      nodes = [ (fieldNode info to f) ];
      edges = [ (fieldEdge path f "data") ];
    };

  proofFieldResult = info: path: f:
    let to = childPath path f.name; in {
      nodes = [ (fieldNode info to f) ];
      edges = [ (fieldEdge path f "proof") ];
    };

  recursiveFieldResult = info: walk: path: record: f:
    let
      to = childPath path f.name;
      child = builtins.getAttr f.name record;
      edge = (fieldEdge path f "recursive") // {
        targetIndex = (f.idxFn or null) != null;
      };
    in
      if builtins.isAttrs child && child ? _con then
        let sub = walk to child; in {
          nodes = sub.nodes;
          edges = [ edge ] ++ sub.edges;
        }
      else {
        nodes = [ (fieldNode info to f) ];
        edges = [ edge ];
      };

  descriptorOf = spec:
    let info = self.datatypeInfo spec; in {
      inherit (info) name indexed;
      params = map (p: p.name or "_") (info.params or []);
      paramArgs = map typeDescriptor (info.paramArgs or []);
      index = typeDescriptor info.indexTy;
      shape = self.shape info.D;
      constructors = map constructorDescriptor info.constructors;
    };
in {
  scope = {
    typeDescriptor = typeDescriptor;

    deriveDescriptor = descriptorOf;

    deriveSchema = spec:
      let
        info = self.datatypeInfo spec;
        constructors = map constructorSchema info.constructors;
      in {
        title = info.name;
        oneOf = constructors;
      };

    deriveDocs = spec:
      let descriptor = descriptorOf spec; in {
        inherit (descriptor) name constructors;
        heading = descriptor.name;
      };

    deriveDeps = spec: value:
      let
        info = self.datatypeInfo spec;
        root = self.view (typeOf spec) value;
        walk = path: record:
          let
            con = self.constructorByName info record._con;
            fieldResults =
              builtins.concatMap (f:
                (if f.kind == "recAt" && builtins.hasAttr f.name record
                 then [ (recursiveFieldResult info walk path record f) ]
                 else [])
                ++ (if isDataField f && isDependencyRole (f.role or null) && builtins.hasAttr f.name record
                    then [ (dependencyFieldResult info path f) ]
                    else [])
                ++ (if (f.proof or false) && builtins.hasAttr f.name record
                    then [ (proofFieldResult info path f) ]
                    else []))
                (con.fields or []);
          in {
            nodes = [ (constructorNode info path con) ]
              ++ builtins.concatMap (r: r.nodes) fieldResults;
            edges = builtins.concatMap (r: r.edges) fieldResults;
          };
        graph = walk "$" root;
      in {
        datatype = info.name;
        root = root._con or null;
        rootPath = "$";
        indexed = info.indexed or false;
        index = typeDescriptor info.indexTy;
        inherit (graph) nodes edges;
      };

    deriveFold = spec:
      let descriptor = descriptorOf spec; in {
        datatype = descriptor.name;
        cases = map (c: {
          inherit (c) name;
          fields = map (f: {
            inherit (f) name kind type;
          }) c.fields;
        }) descriptor.constructors;
      };
  };

  tests = {
    "derive-descriptor-small-datatype" = {
      expr = let
        Box = H.datatype "Box" [
          (H.con "box" [ (H.field "value" H.nat) ])
        ];
      in self.deriveDescriptor Box;
      expected = {
        name = "Box";
        indexed = false;
        params = [];
        paramArgs = [];
        index = { kind = "unit"; };
        shape = {
          kind = "arg";
          body = { kind = "ret"; };
        };
        constructors = [
          {
            name = "box";
            index = 0;
            fields = [
              {
                name = "value";
                kind = "data";
                index = 0;
                level = 0;
                role = null;
                source = null;
                proof = false;
                recursiveIndex = false;
                branchIndex = false;
                dependentType = false;
                type = { kind = "nat"; };
              }
            ];
            targetIndex = true;
          }
        ];
      };
    };

    "derive-schema-small-datatype" = {
      expr = let
        Box = H.datatype "Box" [
          (H.con "box" [ (H.field "value" H.nat) ])
        ];
      in self.deriveSchema Box;
      expected = {
        title = "Box";
        oneOf = [
          {
            type = "object";
            additionalProperties = false;
            required = [ "_con" "value" ];
            properties = {
              _con = { const = "box"; };
              value = { type = "integer"; };
            };
          }
        ];
      };
    };

    "derive-descriptor-product-sugar" = {
      expr = let
        Box = H.product "Box" [ (H.field "value" H.nat) ];
        Explicit = H.datatype "Box" [ (H.con "Box" [ (H.field "value" H.nat) ]) ];
      in {
        sugar = self.deriveDescriptor Box;
        explicit = self.deriveDescriptor Explicit;
        equal = (self.deriveDescriptor Box) == (self.deriveDescriptor Explicit);
      };
      expected = {
        sugar = self.deriveDescriptor (H.datatype "Box" [ (H.con "Box" [ (H.field "value" H.nat) ]) ]);
        explicit = self.deriveDescriptor (H.datatype "Box" [ (H.con "Box" [ (H.field "value" H.nat) ]) ]);
        equal = true;
      };
    };

    "derive-schema-product-sugar" = {
      expr = let
        Pair = H.product "Pair" [
          (H.field "fst" H.nat)
          (H.field "snd" H.string)
        ];
      in self.deriveSchema Pair;
      expected = {
        title = "Pair";
        oneOf = [
          {
            type = "object";
            additionalProperties = false;
            required = [ "_con" "fst" "snd" ];
            properties = {
              _con = { const = "Pair"; };
              fst = { type = "integer"; };
              snd = { type = "string"; };
            };
          }
        ];
      };
    };

    "derive-descriptor-indexed-pi-field" = {
      expr = let
        IndexedPi = H.datatypeI "GenericIndexedPi" H.bool [
          (H.conI "mk"
            [ (HI.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) ]
            (_: H.true_))
        ];
      in (self.deriveDescriptor IndexedPi).constructors;
      expected = [
        {
          name = "mk";
          index = 0;
          fields = [
            {
              name = "next";
              kind = "piAt";
              index = 0;
              level = 0;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = false;
              branchIndex = true;
              dependentType = false;
              type = { kind = "function"; };
            }
          ];
          targetIndex = true;
        }
      ];
    };

    "derive-descriptor-poly-datatype" = {
      expr = let
        Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "leaf" [ (H.field "value" A) ])
            (H.con "node" [ (H.recField "left") (H.recField "right") ])
          ]);
      in (self.deriveDescriptor (H.app Tree.T H.nat)).constructors;
      expected = [
        {
          name = "leaf";
          index = 0;
          fields = [
            {
              name = "value";
              kind = "data";
              index = 0;
              level = 0;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = false;
              branchIndex = false;
              dependentType = false;
              type = { kind = "nat"; };
            }
          ];
          targetIndex = true;
        }
        {
          name = "node";
          index = 1;
          fields = [
            {
              name = "left";
              kind = "recAt";
              index = 0;
              level = null;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = true;
              branchIndex = false;
              dependentType = false;
              type = { kind = "recursive"; };
            }
            {
              name = "right";
              kind = "recAt";
              index = 1;
              level = null;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = true;
              branchIndex = false;
              dependentType = false;
              type = { kind = "recursive"; };
            }
          ];
          targetIndex = true;
        }
      ];
    };

    "derive-schema-poly-tree" = {
      expr = let
        Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "leaf" [ (H.field "value" A) ])
            (H.con "node" [ (H.recField "left") (H.recField "right") ])
          ]);
      in self.deriveSchema (H.app Tree.T H.nat);
      expected = {
        title = "Tree";
        oneOf = [
          {
            type = "object";
            additionalProperties = false;
            required = [ "_con" "value" ];
            properties = {
              _con = { const = "leaf"; };
              value = { type = "integer"; };
            };
          }
          {
            type = "object";
            additionalProperties = false;
            required = [ "_con" "left" "right" ];
            properties = {
              _con = { const = "node"; };
              left = { "$ref" = "#"; };
              right = { "$ref" = "#"; };
            };
          }
        ];
      };
    };

    "derive-descriptor-preserves-rich-field-metadata" = {
      expr = let
        Indexed = H.datatypeI "GenericIndexedMeta" H.bool [
          (H.conI "mk" [
            ((HI.fieldAt 0 "value" H.nat) // {
              role = "payload";
              source = { path = "constructors.mk.fields.value"; };
              proof = true;
            })
            ((H.recFieldAt "tail" (_: H.false_)) // {
              role = "dependency";
              source = { path = "constructors.mk.fields.tail"; };
            })
            ((HI.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) // {
              role = "branch";
              source = { path = "constructors.mk.fields.next"; };
            })
          ] (_: H.true_))
        ];
      in (builtins.head (self.deriveDescriptor Indexed).constructors).fields;
      expected = [
        {
          name = "value";
          kind = "data";
          index = 0;
          level = 0;
          role = "payload";
          source = { path = "constructors.mk.fields.value"; };
          proof = true;
          recursiveIndex = false;
          branchIndex = false;
          dependentType = false;
          type = { kind = "nat"; };
        }
        {
          name = "tail";
          kind = "recAt";
          index = 1;
          level = null;
          role = "dependency";
          source = { path = "constructors.mk.fields.tail"; };
          proof = false;
          recursiveIndex = true;
          branchIndex = false;
          dependentType = false;
          type = { kind = "recursive"; };
        }
        {
          name = "next";
          kind = "piAt";
          index = 2;
          level = 0;
          role = "branch";
          source = { path = "constructors.mk.fields.next"; };
          proof = false;
          recursiveIndex = false;
          branchIndex = true;
          dependentType = false;
          type = { kind = "function"; };
        }
      ];
    };

    "derive-descriptor-instantiated-poly-preserves-source-role" = {
      expr = let
        Tree = H.datatypeP "GenericPolyMeta" [{ name = "A"; kind = H.u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (H.con "leaf" [
              ((H.field "value" A) // {
                role = "payload";
                source = { path = "constructors.leaf.fields.value"; };
              })
            ])
          ]);
        field = builtins.head
          ((builtins.head (self.deriveDescriptor (H.app Tree.T H.nat)).constructors).fields);
      in {
        inherit (field) role source type;
      };
      expected = {
        role = "payload";
        source = { path = "constructors.leaf.fields.value"; };
        type = { kind = "nat"; };
      };
    };

    "derive-deps-recursive-tree" = {
      expr = let
        Tree = H.datatype "DepTree" [
          (H.con "leaf" [ (H.field "value" H.nat) ])
          (H.con "node" [
            ((H.recField "left") // { role = "dependency"; })
            ((H.recField "right") // { role = "dependency"; })
          ])
        ];
        graph = self.deriveDeps Tree {
          _con = "node";
          left = { _con = "leaf"; value = 0; };
          right = { _con = "leaf"; value = 1; };
        };
      in {
        inherit (graph) datatype root rootPath index;
        nodes = map (n: {
          inherit (n) id con;
          kind = n.kind or null;
          path = n.path or null;
          constructor = n.constructor or null;
        }) graph.nodes;
        edges = map (e: {
          inherit (e) from to field role kind;
          source = e.source or null;
          targetIndex = e.targetIndex or null;
          recursiveIndex = e.recursiveIndex or null;
        }) graph.edges;
      };
      expected = {
        datatype = "DepTree";
        root = "node";
        rootPath = "$";
        index = { kind = "unit"; };
        nodes = [
          {
            id = "$";
            path = "$";
            kind = "constructor";
            con = "node";
            constructor = "node";
          }
          {
            id = "$.left";
            path = "$.left";
            kind = "constructor";
            con = "leaf";
            constructor = "leaf";
          }
          {
            id = "$.right";
            path = "$.right";
            kind = "constructor";
            con = "leaf";
            constructor = "leaf";
          }
        ];
        edges = [
          {
            from = "$";
            to = "$.left";
            field = "left";
            role = "dependency";
            kind = "recursive";
            source = null;
            targetIndex = true;
            recursiveIndex = true;
          }
          {
            from = "$";
            to = "$.right";
            field = "right";
            role = "dependency";
            kind = "recursive";
            source = null;
            targetIndex = true;
            recursiveIndex = true;
          }
        ];
      };
    };

    "derive-deps-role-proof-source-fields" = {
      expr = let
        Builder = H.datatype "DepRoleProofBuilder" [
          (H.con "builder" [
            ((H.field "service" H.nat) // {
              role = "dependency";
              source = { path = "builder.service"; };
            })
            ((H.field "witness" H.bool) // {
              proof = true;
              source = { path = "builder.witness"; };
            })
          ])
        ];
        graph = self.deriveDeps Builder {
          _con = "builder";
          service = 7;
          witness = true;
        };
      in {
        nodes = map (n: {
          inherit (n) id kind;
          field = n.field or null;
          role = n.role or null;
          source = n.source or null;
          proof = n.proof or false;
          type = n.type or null;
        }) graph.nodes;
        edges = map (e: {
          inherit (e) from to field kind role;
          source = e.source or null;
          proof = e.proof or false;
          type = e.type or null;
        }) graph.edges;
      };
      expected = {
        nodes = [
          {
            id = "$";
            kind = "constructor";
            field = null;
            role = null;
            source = null;
            proof = false;
            type = null;
          }
          {
            id = "$.service";
            kind = "field";
            field = "service";
            role = "dependency";
            source = { path = "builder.service"; };
            proof = false;
            type = { kind = "nat"; };
          }
          {
            id = "$.witness";
            kind = "field";
            field = "witness";
            role = null;
            source = { path = "builder.witness"; };
            proof = true;
            type = { kind = "bool"; };
          }
        ];
        edges = [
          {
            from = "$";
            to = "$.service";
            field = "service";
            kind = "data";
            role = "dependency";
            source = { path = "builder.service"; };
            proof = false;
            type = { kind = "nat"; };
          }
          {
            from = "$";
            to = "$.witness";
            field = "witness";
            kind = "proof";
            role = null;
            source = { path = "builder.witness"; };
            proof = true;
            type = { kind = "bool"; };
          }
        ];
      };
    };

    "derive-deps-indexed-datatype-metadata" = {
      expr = let
        Indexed = H.datatypeI "DepIndexedBox" H.bool [
          (H.conI "mk" [
            ((H.field "dep" H.nat) // {
              role = "dependency";
              source = { path = "mk.dep"; };
            })
          ] (_: H.true_))
        ];
        graph = self.deriveDeps (H.app Indexed.T H.true_) {
          _con = "mk";
          dep = 1;
        };
      in {
        inherit (graph) datatype index;
        nodes = map (n: {
          inherit (n) id con;
          indexed = n.indexed or null;
        }) graph.nodes;
        edges = map (e: {
          inherit (e) from to field kind role;
          source = e.source or null;
        }) graph.edges;
      };
      expected = {
        datatype = "DepIndexedBox";
        index = { kind = "bool"; };
        nodes = [
          { id = "$"; con = "mk"; indexed = true; }
          { id = "$.dep"; con = null; indexed = true; }
        ];
        edges = [
          {
            from = "$";
            to = "$.dep";
            field = "dep";
            kind = "data";
            role = "dependency";
            source = { path = "mk.dep"; };
          }
        ];
      };
    };

    "derive-deps-ornamented-role-survives" = {
      expr = let
        CoreBuilder = H.datatype "DepCoreBuilder" [
          (H.con "builder" [
            ((H.field "name" H.nat) // {
              role = "dependency";
              source = { path = "core.name"; };
            })
            (H.field "actionCount" H.nat)
          ])
        ];
        CodeGenBuilder = H.ornament CoreBuilder {
          name = "DepCodeGenBuilder";
          constructors.builder.fields = [
            { insert = "language"; type = H.nat; }
            { keep = "name"; }
            { keep = "actionCount"; }
          ];
        };
        IdlBuilder = H.ornament CodeGenBuilder {
          name = "DepIdlBuilder";
          constructors.builder.fields = [
            { insert = "idlVersion"; type = H.nat; }
            { keep = "language"; }
            { keep = "name"; }
            { keep = "actionCount"; }
          ];
        };
        graph = self.deriveDeps IdlBuilder {
          _con = "builder";
          idlVersion = 1;
          language = 2;
          name = 3;
          actionCount = 5;
        };
      in builtins.elem {
        from = "$";
        to = "$.name";
        field = "name";
        kind = "data";
        role = "dependency";
        source = { path = "core.name"; };
        type = { kind = "nat"; };
      } (map (e: {
        inherit (e) from to field kind role;
        source = e.source or null;
        type = e.type or null;
      }) graph.edges);
      expected = true;
    };
  };

  __docs = {
    deriveDeps = {
      description = "deriveDeps: build a node-and-edge dependency graph from a value — walks each constructor record, emitting nodes for constructors and edges for `recAt` recursion sites, role-tagged dependency fields, and proof-bearing fields.";
      signature = "deriveDeps : DataSpec -> NixVal -> { datatype, root, rootPath, indexed, index, nodes, edges }";
      doc = ''
        Traversal seeds at path `\"$\"` and recurses into each `recAt`
        field, accumulating constructor nodes and per-field edges.
        Emitted edge kinds:

        - `recAt` field on a constructor: edge from parent to child
          constructor, carrying `field`, `role`, `source`, and the
          resolved child type.
        - Dependency-role field (matching the role-policy predicate):
          edge to a referenced datatype.
        - Proof-bearing field (`proof = true`): edge tagging the
          unresolved obligation.

        The returned `nodes` / `edges` shape is consumable by the
        generic graph renderer and by build-time dependency analysers.
      '';
    };
    deriveDescriptor = {
      description = "deriveDescriptor: produce a full structured descriptor of a datatype — name, constructors, fields with kinds/types/roles, and source provenance. The base artefact other `derive*` helpers consume.";
      signature = "deriveDescriptor : DataSpec -> { name : String; constructors : [ConstructorDescriptor]; ... }";
    };
    deriveDocs = {
      description = "deriveDocs: produce a documentation-friendly descriptor — same `name` and `constructors` as `deriveDescriptor` plus a `heading` field for use in Markdown/HTML rendering.";
      signature = "deriveDocs : DataSpec -> { heading : String; name : String; constructors : [...] }";
    };
    deriveFold = {
      description = "deriveFold: produce a fold-skeleton descriptor — `{ datatype; cases = [{ name; fields = [{ name; kind; type; }] }] }`; consumed by code generators emitting per-datatype fold scaffolds.";
      signature = "deriveFold : DataSpec -> { datatype : String; cases : [Object] }";
    };
    deriveSchema = {
      description = "deriveSchema: produce a JSON-Schema-flavoured `{ title, oneOf : [ConstructorSchema] }` from a datatype — each constructor schema records its name, field name+kind+type, and metadata flags (target index, proof, etc.).";
      signature = "deriveSchema : DataSpec -> { title : String; oneOf : [Object] }";
    };
    typeDescriptor = {
      description = "typeDescriptor: convert a kernel type (HOAS or `Val`) into a structured descriptor record — `{ kind; name?; constructors?; ... }` summarising the shape; used downstream by schema, docs, and dependency derivations.";
      signature = "typeDescriptor : Hoas | Val | null -> { kind : String; ... }";
    };
  };
}
