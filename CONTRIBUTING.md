# Contributing to nix-effects

This repository is a read-only mirror of a monorepo, synced automatically via
[josh](https://josh-project.github.io/josh/). Pull requests cannot be merged
directly here.

## How to contribute

- **Issues** are welcome for bugs, feature requests, and discussion.
- **Pull requests** are welcome as a way to propose changes. Accepted changes
  are applied upstream and the next mirror sync pushes them to this repo.
- When a PR is applied upstream, it will be closed with a note.

## CI requirements

Upstream applies two automated checks to every contribution before the
mirror sync pushes the change here. Both must pass.

### Tests

`nix flake check` runs the nix-unit suite: the inline tests discovered
via `api.mk` wrappers and the integration tests under `tests/`. Every
leaf assertion must pass.

### Performance gate

`nix-effects-bench-gate` compares a contribution's bench run against
the committed reference at `bench/history/baseline.{json,md}`. Two
axes are potentially gated:

- **Allocation counters** (`envs`, `thunks`, `sets`, `lookups`, …
  reported by `NIX_SHOW_STATS`) are deterministic for a fixed Nix
  evaluator. A regression means the contribution caused the code to
  allocate more. Gated at `allocTolerancePermille` (5‰ = 0.5% in the
  committed `bench/budgets.toml`).
- **CPU percentiles** (`cpu.p50`, `cpu.p95`) are hardware- and
  scheduler-dependent. A regression means slower execution on *the
  machine that measured it*. Gated per-workload via `[cpu]` in
  `bench/budgets.toml`, with a `current.cpu.p95 > baseline.cpu.p95`
  non-overlap guard to reject noisy false positives.

The **allocation** axis is a structural property of the code; the
**cpu** axis is an environmental property. CI and local developers
use the axes differently:

**Upstream CI** runs `bench-gate --alloc-only`. Shared runners have
variable hardware tiers and noisy neighbours; the recorded baseline
was captured on a developer workstation, so percentage deltas against
CI-runner cpu timings don't mean anything. Only the allocation axis
is gated. `allocTolerancePermille` and per-workload `noiseLimited`
declarations remain in force.

**Local development** runs the full dual-metric gate. Cpu feedback is
useful on the same hardware that captured the baseline, *at sufficient
sample count*: `--runs 5` (the CI default) leaves the cpu p50 / p95
estimates noise-dominated, so spurious cpu warnings are common and a
single unlucky sample can produce a 40%+ apparent regression on an
identical-code run. Use `--runs 20` or higher for meaningful cpu
diagnostics; reserve `--runs 5` for quick alloc-only checks. Workloads
in the `noiseLimited` array of `bench/budgets.toml` retain alloc
gating but are exempt from cpu gating even locally (they are
structurally noisy on small inputs or specific DAG shapes).

If a contribution knowingly regresses a workload on either axis,
acknowledge it with a commit trailer:

```
Perf-regression: <workload>, <reason at least 20 characters>
```

The gate demotes the matching workload's hard-fail into an "overridden"
status and the commit ships. `bench-open-regressions` classifies each
acknowledged regression against current baseline metrics; a regression
clears the audit the moment its workload passes the gate again.

#### Nix version constraint

Allocation counters are deterministic *for a fixed Nix evaluator*.
Different Nix versions can ship different thunk / env / lookup
strategies and produce different counts for identical code. The gate
refuses to compare a baseline captured on one Nix version against a
current run on another, and will fail with a clear message. Both the
shell driver and the pure finalize layer enforce this.

`baseline.json` records the Nix version it was captured with. CI pins
the evaluator to match. To change Nix versions, update both together:
see **Baseline refresh** below.

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

## Running the bench harness

```bash
# Capture a local run:
nix build .#bench-run
result/bin/nix-effects-bench-run --name myrun --runs 5 --tier quick

# Preview the CI gate against the committed baseline:
nix build .#bench-gate
result/bin/nix-effects-bench-gate \
  --baseline bench/history/baseline.json \
  --current  bench/history/myrun.json \
  --budgets  bench/budgets.toml
```

See `bench/workloads/` for the workload tree, `bench/lib/` for the
measurement and gate libraries, and `bench/runner/` for the CLI
drivers. Each file carries inline documentation describing its role
in the harness.

## Baseline refresh

`bench/history/baseline.{json,md}` is a committed artifact — it is the
reference the alloc gate compares against. Regenerate it in exactly
these cases:

1. **Intentional allocation improvement.** A contribution reduces
   allocation counts on one or more workloads and the improvement
   should become the new floor. Without a refresh, future regressions
   would be measured against an obsolete high-water mark.
2. **Nix evaluator upgrade.** The flake's pinned nixpkgs moves to a
   new Nix version. Allocation counters can shift for reasons
   unrelated to the nix-effects code. Refresh the baseline in the same
   commit that bumps the flake input.
3. **New workload added.** A workload present in the current run but
   missing from the baseline is reported as "new" (informational, not
   gated). Adding it to the baseline makes it gateable.

Do **not** refresh the baseline to paper over an unintentional
regression. That defeats the purpose of the gate.

### Procedure

```bash
# 1. Confirm your Nix version matches (or intentionally update both
#    together).
nix --version

# 2. Capture a fresh run. --runs 5 --tier quick matches the CI
#    configuration; use higher runs for a reduced-noise capture if
#    cpu budgets will also be recalibrated.
nix build .#bench-run
result/bin/nix-effects-bench-run --name baseline --runs 5 --tier quick

# 3. Verify the capture against the previous baseline locally (full
#    dual-metric gate, no --alloc-only). If workloads fail, confirm
#    the regressions are intentional before proceeding.
nix build .#bench-gate
result/bin/nix-effects-bench-gate \
  --baseline bench/history/baseline.json \
  --current  bench/history/baseline.json \
  --budgets  bench/budgets.toml

# 4. Commit bench/history/baseline.{json,md} together. The working
#    copy has already overwritten them in step 2.
git add bench/history/baseline.json bench/history/baseline.md
git commit -m "bench: refresh baseline (<reason>)"
```

Step 3 above runs `bench-gate` with `current == baseline` — the gate
should pass trivially. If the commit message references a specific
workload whose alloc count changed, include the before/after figures
in the commit body.

### When cpu budgets also need updating

`bench/budgets.toml` is calibrated against a specific hardware
profile. When hardware changes (or the baseline-capture machine
changes), cpu budgets can drift out of the noise band. Recalibrate:

```bash
nix build .#bench-calibrate
result/bin/nix-effects-bench-calibrate --runs 50 --tier quick \
  --existing-budgets bench/budgets.toml \
  --output bench/budgets.toml
```

`--existing-budgets` preserves the `noiseLimited` array across
recalibration; otherwise it would be regenerated as just `[cpu]`
entries and workloads deliberately excluded from cpu gating would
quietly return. Recalibration is a workstation-local activity; CI
does not recalibrate.
