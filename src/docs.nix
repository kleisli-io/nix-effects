{ api, lib, ... }:

let
  metaKeys = [ "title" "doc" "description" "signature" "sections" "tests" "appendix" ];

  trimText = s:
    lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } s);

  yamlEscape = s: builtins.replaceStrings [ "\\" "\"" ] [ "\\\\" "\\\"" ] s;

  descriptionMinLength = 60;
  descriptionMaxLength = 160;

  shortenDescription = description:
    let
      trimmed = trimText description;
      maxStem = descriptionMaxLength - 3;
    in
    if builtins.stringLength trimmed <= descriptionMaxLength
    then trimmed
    else builtins.substring 0 maxStem trimmed + "...";

  frontMatterDescription = description:
    if description == null || description == "" then null
    else
      let shortened = shortenDescription description;
      in
      if builtins.stringLength shortened < descriptionMinLength
      then null
      else shortened;

  addFrontMatter = { title, body, mtime ? null, sha ? null, description ? null }:
    let
      lines = lib.splitString "\n" body;
      firstLine = if lines == [ ] then "" else builtins.head lines;
      hasH1 = lib.hasPrefix "# " firstLine;
      strippedBody =
        if hasH1
        then
          let
            rest = builtins.tail lines;
            trimmed =
              if rest != [ ] && builtins.head rest == ""
              then builtins.tail rest
              else rest;
          in
          lib.concatStringsSep "\n" trimmed
        else body;
      mtimeLine = if mtime != null then "mtime: ${toString mtime}\n" else "";
      shaLine = if sha != null && sha != "" then "sha: ${sha}\n" else "";
      pageDescription = frontMatterDescription description;
      descriptionLine =
        if pageDescription != null
        then "description: \"${yamlEscape pageDescription}\"\n"
        else "";
    in
    "---\ntitle: \"${title}\"\n${mtimeLine}${shaLine}${descriptionLine}---\n\n${strippedBody}";

  capitalise = s:
    let
      first = builtins.substring 0 1 s;
      rest = builtins.substring 1 (builtins.stringLength s) s;
    in
    lib.toUpper first + rest;

  fieldLine = field:
    "- `${field.name}`: `${field.type.kind or field.kind}`";

  renderDatatypeConstructor = con: ''
    ### ${con.name}

    ${lib.concatStringsSep "\n" (map fieldLine con.fields)}
  '';

  renderDatatype = title: descriptor: ''
    ## ${title}

    ${lib.concatStringsSep "\n\n" (map renderDatatypeConstructor descriptor.constructors)}
  '';

  childAttrs = node:
    lib.filterAttrs (k: v: !(builtins.elem k metaKeys) && builtins.isAttrs v) node;

  isLeafChild = node: childAttrs node == { };

  orderNames = preferred: names:
    let
      selected = lib.filter (n: builtins.elem n names) preferred;
      rest = lib.filter (n: !(builtins.elem n preferred)) names;
    in
    selected ++ lib.sort (a: b: a < b) rest;

  shortNameList = names:
    let
      sorted = lib.sort (a: b: a < b) names;
      shown = lib.take 4 sorted;
      extra = builtins.length sorted - builtins.length shown;
      rendered = lib.concatStringsSep ", " (map (n: "`${n}`") shown);
    in
    rendered + lib.optionalString (extra > 0) ", and ${toString extra} more";

  renderApiPage =
    { title
    , node
    , mtime ? null
    , sha ? null
    , description ? node.description or null
    , appendBody ? ""
    , sourceFilesSection ? ""
    , namespacePath ? null
    , subNamespaces ? [ ]
    , libraryName ? "this project"
    , linkify ? (x: x)
    }:
    let
      entries = lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;
      entryNames = lib.sort (a: b: a < b) (builtins.attrNames entries);

      fallbackIntro =
        let
          pathText =
            if namespacePath == null then "This namespace"
            else "The `${namespacePath}` namespace";
          surface =
            if entryNames != [ ] && subNamespaces != [ ] then "public values and child namespaces"
            else if entryNames != [ ] then "public values"
            else "child namespaces";
          entrySentence =
            lib.optionalString (entryNames != [ ])
              " Key exports include ${shortNameList entryNames}.";
          childSentence =
            lib.optionalString (subNamespaces != [ ])
              " Child namespaces cover ${shortNameList subNamespaces}.";
        in
        "${pathText} groups ${surface} for ${libraryName}.${entrySentence}${childSentence}";

      intro =
        if node ? doc && node.doc != "" then node.doc
        else if node ? description && node.description != "" then node.description
        else fallbackIntro;

      moduleDoc = lib.optionalString (intro != "")
        (linkify (trimText intro) + "\n\n");

      renderEntry = name: entry:
        let
          hasDesc = entry ? description && entry.description != "";
          hasDoc = entry ? doc && entry.doc != "";
          hasSig = entry ? signature && entry.signature != "";
          descBlock = lib.optionalString hasDesc "_${trimText entry.description}_\n\n";
          sigBlock = lib.optionalString hasSig "```\n${trimText entry.signature}\n```\n\n";
          docBlock = lib.optionalString hasDoc "${linkify (trimText entry.doc)}\n\n";
        in
        lib.optionalString (hasDesc || hasDoc || hasSig)
          "## `${name}`\n\n${descBlock}${sigBlock}${docBlock}";

      entriesBody = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);
    in
    addFrontMatter {
      inherit title mtime sha description;
      body = "${moduleDoc}${entriesBody}${appendBody}${sourceFilesSection}";
    };

  renderApiReferencePage = title: node:
    let
      moduleDocText =
        if node ? doc && node.doc != "" then node.doc
        else node.description or "";
      moduleDoc = lib.optionalString (moduleDocText != "")
        (trimText moduleDocText + "\n\n");

      entries = lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;

      renderEntry = name: entry:
        let
          hasDesc = entry ? description && entry.description != "";
          hasDoc = entry ? doc && entry.doc != "";
          hasSig = entry ? signature && entry.signature != "";
          descBlock = lib.optionalString hasDesc "_${trimText entry.description}_\n\n";
          sigBlock = lib.optionalString hasSig "```\n${trimText entry.signature}\n```\n\n";
          docBlock = lib.optionalString hasDoc "${trimText entry.doc}\n\n";
        in
        lib.optionalString (hasDesc || hasDoc || hasSig)
          "## `${name}`\n\n${descBlock}${sigBlock}${docBlock}";

      body = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);
    in
    "# ${title}\n\n${moduleDoc}${body}";

  isContainer = node:
    builtins.isAttrs node
    && !(node ? doc)
    && !(node ? description)
    && !(node ? signature);

  children = node: lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;

  genApiReferenceEntries = pkgs: prefix: docs:
    lib.foldlAttrs
      (acc: key: value:
        if isContainer value
        then acc ++ genApiReferenceEntries pkgs "${prefix}${key}/" value
        else acc ++ [{
          name = "${prefix}${key}.md";
          path = pkgs.writeText "${key}.md" (renderApiReferencePage key value);
        }]
      ) [ ]
      (children docs);

  mkApiDocsLinkFarm = { pkgs, docs, name ? "api-docs" }:
    pkgs.linkFarm name (genApiReferenceEntries pkgs "" docs);

  makeApiEntries =
    { pkgs
    , projectId
    , docs
    , apiSections ? [ ]
    , preferredDocOrder ? { }
    , coreUrl ? "core-api"
    , namespaceRoot ? projectId
    , libraryName ? projectId
    , sourceFilesSectionFor ? (_: "")
    , mtimeFor ? (_: null)
    , shaFor ? (_: null)
    , linkify ? (x: x)
    , nodeAppendix ? (_: "")
    }:
    let
      sectionKeys = map (s: s.key) apiSections;
      orderedDocNames = urlPath: attrs:
        orderNames
          (preferredDocOrder.${urlPath} or [ ])
          (builtins.attrNames attrs);

      hasOwnDoc = node:
        (node ? doc && node.doc != "")
        || (node ? description && node.description != "")
        || (node ? signature && node.signature != "");

      hasApiPageContent = node:
        let
          children = childAttrs node;
          leafChildren = lib.filterAttrs (_: isLeafChild) children;
          nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;
        in
        hasOwnDoc node || leafChildren != { } || nestedChildren != { };

      nestedApiPagePaths = urlPath: node:
        let
          children = childAttrs node;
          nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;
        in
        lib.concatLists (map
          (name:
            let
              child = nestedChildren.${name};
              childPath = "${urlPath}/${name}";
            in
            lib.optional (hasApiPageContent child) childPath
            ++ nestedApiPagePaths childPath child)
          (orderedDocNames urlPath nestedChildren));

      apiSectionPagePaths = sectionUrl: node:
        let
          children = childAttrs node;
        in
        lib.concatLists (map
          (name:
            let
              child = children.${name};
              childPath = "${sectionUrl}/${name}";
            in
            lib.optional (hasApiPageContent child) name
            ++ map
              (path: lib.strings.removePrefix "${sectionUrl}/" path)
              (nestedApiPagePaths childPath child))
          (orderedDocNames sectionUrl children));

      walkApi = { urlPrefix, srcPath, node, mtime ? null, sha ? null }:
        let
          children = childAttrs node;
          leafChildren = lib.filterAttrs (_: isLeafChild) children;
          nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;

          metaFields = lib.filterAttrs
            (k: _: builtins.elem k [ "doc" "description" "signature" ])
            node;
          pageNode = metaFields // leafChildren;

          subNamespaceSection =
            lib.optionalString (nestedChildren != { })
              ("## Sub-namespaces\n\n"
                + lib.concatStrings (map (n: "- [`${n}`](/${urlPrefix}/${n})\n")
                (orderedDocNames urlPrefix nestedChildren))
                + "\n");

          pageName = builtins.baseNameOf urlPrefix;
          selfPage = lib.optional (hasApiPageContent node) {
            name = "${urlPrefix}.md";
            path = pkgs.writeText "${pageName}.md" (renderApiPage {
              title = capitalise pageName;
              node = pageNode;
              inherit mtime sha libraryName linkify;
              namespacePath = "${namespaceRoot}.${builtins.replaceStrings [ "/" ] [ "." ] srcPath}";
              subNamespaces = orderedDocNames urlPrefix nestedChildren;
              sourceFilesSection = sourceFilesSectionFor srcPath;
              appendBody = (node.appendix or "") + nodeAppendix node + subNamespaceSection;
            });
          };

          nestedPages = lib.concatLists (map
            (name: walkApi {
              urlPrefix = "${urlPrefix}/${name}";
              srcPath = "${srcPath}/${name}";
              node = nestedChildren.${name};
              inherit mtime sha;
            })
            (orderedDocNames urlPrefix nestedChildren));
        in
        selfPage ++ nestedPages;

      coreModuleNames =
        let
          names = builtins.filter
            (name: !(builtins.elem name sectionKeys)
              && !(builtins.elem name metaKeys)
              && builtins.isAttrs docs.${name}
              && (docs.${name} ? doc || docs.${name} ? description))
            (builtins.attrNames docs);
        in
        orderNames (preferredDocOrder.${coreUrl} or [ ]) names;

      corePages = lib.concatLists (map
        (name:
          walkApi {
            urlPrefix = "${projectId}/${coreUrl}/${name}";
            srcPath = name;
            node = docs.${name};
            mtime = mtimeFor "_root";
            sha = shaFor "_root";
          })
        coreModuleNames);

      sectionedPages = lib.concatLists (map
        (sec:
          let
            sectionChildren = childAttrs (docs.${sec.key} or { });
          in
          lib.concatLists (map
            (childName: walkApi {
              urlPrefix = "${projectId}/${sec.url}/${childName}";
              srcPath = "${sec.key}/${childName}";
              node = sectionChildren.${childName};
              mtime = mtimeFor (sec.bucket or sec.key);
              sha = shaFor (sec.bucket or sec.key);
            })
            (orderedDocNames sec.url sectionChildren)))
        apiSections);
    in
    {
      entries = corePages ++ sectionedPages;
      inherit coreModuleNames apiSectionPagePaths;
    };

  mkProjectJson =
    { id
    , name ? id
    , description ? ""
    , sourceUrl ? null
    , sections
    , index ? "index.md"
    }:
    builtins.toJSON ({
      inherit id name description index sections;
    } // lib.optionalAttrs (sourceUrl != null) {
      source-url = sourceUrl;
    });

  mkSimpleApiDocsContent =
    { pkgs
    , docs
    , project
    , apiSections ? [ ]
    , preferredDocOrder ? { }
    , indexBody ? ""
    , requiredChecks ? [ ]
    }:
    let
      api = makeApiEntries {
        inherit pkgs docs apiSections preferredDocOrder;
        projectId = project.id;
        namespaceRoot = project.namespaceRoot or project.id;
        libraryName = project.name or project.id;
      };
      sectionChildren = [
        {
          slug = "core-api";
          title = "Core API";
          order = 1;
          pages = api.coreModuleNames;
          banner = "Auto-generated API reference.";
        }
      ] ++ lib.imap1
        (i: sec: {
          slug = sec.url;
          title = sec.title;
          order = i + 1;
          pages = api.apiSectionPagePaths sec.url (docs.${sec.key} or { });
          banner = sec.banner or "Auto-generated API reference.";
        })
        apiSections;
      projectEntry = {
        name = "${project.id}/project.json";
        path = pkgs.writeText "project.json" (mkProjectJson {
          inherit (project) id;
          name = project.name or project.id;
          description = project.description or "";
          sourceUrl = project.sourceUrl or null;
          sections = [{
            title = "API Reference";
            order = 1;
            reference = true;
            children = sectionChildren;
          }];
        });
      };
      indexEntry = {
        name = "${project.id}/index.md";
        path = pkgs.writeText "index.md" (addFrontMatter {
          title = project.name or project.id;
          body = indexBody;
          description = project.description or null;
        });
      };
      rawCorpus = pkgs.linkFarm "${project.id}-docs-raw"
        ([ projectEntry indexEntry ] ++ api.entries);
      checkDeps = lib.concatMapStringsSep "\n"
        (check: "test -e ${check}")
        requiredChecks;
    in
    pkgs.runCommand "${project.id}-docs" { } ''
      set -eu
      ${checkDeps}
      mkdir -p "$out"
      cp -a ${rawCorpus}/. "$out/"
    '';

in
api.mk {
  docHidden = true;
  description = "Documentation rendering helpers shared by Nix API-style modules.";
  doc = ''
    Reusable markdown and content-tree renderers for libraries that expose
    documentation through `api.extractDocs`.
  '';
  value = {
    inherit metaKeys trimText yamlEscape addFrontMatter capitalise renderDatatype
      renderApiPage renderApiReferencePage mkApiDocsLinkFarm makeApiEntries
      mkProjectJson mkSimpleApiDocsContent;
  };
  tests = {
    "front-matter-strips-h1" = {
      expr = lib.hasInfix "# Title" (addFrontMatter { title = "Title"; body = "# Title\n\nBody"; });
      expected = false;
    };
    "render-datatype-includes-constructor" = {
      expr = lib.hasInfix "### C" (renderDatatype "T" {
        constructors = [{
          name = "C";
          fields = [{ name = "x"; kind = "string"; }];
        }];
      });
      expected = true;
    };
  };
}
