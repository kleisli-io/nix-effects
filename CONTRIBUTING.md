# Contributing to nix-effects

This repository is a read-only mirror of a monorepo, synced automatically via
[josh](https://josh-project.github.io/josh/). Pull requests cannot be merged
directly here.

## How to contribute

- **Issues** are welcome for bugs, feature requests, and discussion.
- **Pull requests** are welcome as a way to propose changes. Accepted changes
  are applied upstream and the next mirror sync pushes them to this repo.
- When a PR is applied upstream, it will be closed with a note.

## Running tests

```bash
# With just (requires nix-unit in PATH)
just test              # Run all tests
just test inline       # Run a specific suite

# With nix-unit directly
nix-unit ./tests.nix

# With flake
nix flake check
```
