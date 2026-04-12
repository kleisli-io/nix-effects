help:
  just -l

test suite="all" *args:
  nix-unit --expr 'let x = import ./tests.nix {}; in if "{{suite}}" == "all" then x else x.{{suite}}' {{args}}
