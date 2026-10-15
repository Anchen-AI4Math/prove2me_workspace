# Big O Speedrun verifier

This repository runs public Lean proof checks on a fresh GitHub-hosted VM.
A maintainer starts **Verify a Lean proof** from the Actions tab. The workflow
uploads full logs and a JSON receipt, including failed and incomplete checks.
No leaderboard file is changed by a run.

## Start a run

The workflow has five inputs:

| Input | Meaning |
|---|---|
| `repo_url` | Public `https://github.com/OWNER/REPO` submission URL |
| `commit` | Complete 40-digit commit SHA; branch names are rejected |
| `challenge_file` | Registered statement file in **this verifier repository** |
| `theorem_names` | Comma-separated names allowed by that statement's profile |
| `lean_toolchain` | Toolchain pinned by the reviewed profile |

The first profile is `challenges/dft/UniformFourier233.lean`, Lean 4.34.1.
It checks `OAI.PowerSaving.transform_mainY` and
`OAI.PowerSaving.convolution_mainY` at saving `7547360/10^10`.
The dispatch defaults pin Chafik Boukhalfa's (`chafreaky`) [PR #2](https://github.com/jacobalansussman/wht-power-saving-lean/pull/2)
head `837dc3130adc79f7b7ab4ddd56c15576bbd766b0`, observed 2026-10-10.
A new challenge or toolchain requires a reviewed repository change.

## What the workflow checks

1. Fetch the pinned submission without running its scripts or Lake file.
2. Build pinned Comparator, exporter, nanoda, and landrun tools. Fetch the
   pinned Mathlib cache in a separate trusted setup step.
3. Copy regular Lean source files into a fresh project with our Lake config.
   Comparator first builds and exports our trusted challenge. Its solution
   build then compiles dependency chains from source, one new module at a time.
4. Compare the solution statement and its dependencies with our challenge,
   check permitted axioms, and replay the proof in Lean's kernel.
5. Run `#print axioms` for each target. Run Comparator again with nanoda enabled;
   that pass also repeats Lean's kernel check.
6. Upload `receipt.json`, source/tool hashes, per-stage logs, times, and
   sampled cgroup memory peaks as `verifier-receipt-and-logs-…`.

The receipt reports each theorem and kernel separately. The theorems in one
request share a proof closure, so their time and memory measurements are shared.
A complete pass requires both kernels and the axiom audit. A failed workflow
can still contain a completed Lean-kernel pass; read the per-kernel receipt.
A timeout or resource limit gives no mathematical verdict.

The trusted DFT statement is based on our saved OpenAI challenge, not the
submission's challenge. It covers every positive length and every complex
input in the same exact scalar/index RAM, including root-order selection,
supplied canonical root, preparation cost, and polynomial integer/work bounds.
It is an operation-count theorem, not a bit-complexity claim.

## Isolation and resource limits

- `permissions: contents: read`; checkout does not retain credentials. The
  workflow uses no repository secrets and no Actions cache upload/save action.
- A new VM runs each job. Network access is used only for public source fetches
  and trusted tool/dependency setup. No submission code runs during setup.
  Setup loads Ubuntu's packaged `bwrap-userns-restrict` AppArmor profile so
  bubblewrap can create its namespaces; global userns restrictions stay enabled.
- Submission compilation, export, kernel checks, and audit run in a bwrap
  namespace with no network, a private process namespace, and an empty
  environment except for explicit tool paths. Comparator also retains landrun
  and its AF_UNIX restriction. Missing isolation causes a failure.
- Only public system executables/libraries, the toolchain/tools, the fixed
  dependency cache, staged sources, and trusted control files are readable.
  Only the run's build directory and temporary directory are writable.
  The workflow checkout, credentials, host process tree, receipts, and cache
  are outside the submission's writable namespace.
- Submission Lake files, hooks, generators, submodules and compiled objects are
  not used. The trusted challenge imports only fixed Mathlib. Its compiled
  outputs are removed inside the sandbox before each Comparator call so an
  earlier submission build cannot replace the statement used for comparison.
- One workflow runs at a time. New modules compile in dependency order using
  four Lean threads, nice 10, a 4-CPU quota and a 14 GiB RAM cgroup maximum. Builds and the first Lean
  check have no swap. The nanoda phase gets 16 GiB of swap on the disposable VM
  because Comparator retains its parsed proof while the external kernel runs.
  The swap file is outside the submission mounts; receipts record sampled swap
  use separately. This uses the standard free public runner.
  There is no soft memory limit that would force prolonged reclaim.
- The job timeout is **350 minutes**. Verification stops at a 320-minute total
  deadline, leaving time to save artifacts. Tool setup has a 45-minute limit.
  The controller also stops a check if free disk falls below 1 GiB.
- Setup removes only known preinstalled SDK folders on the disposable runner
  to make room for Lean and Mathlib. It does not reuse proof objects or publish
  cache entries from an untrusted build.

GitHub's [runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
lists public `ubuntu-latest` as **4 vCPU, 16 GB RAM and 14 GB SSD**, checked
2026-10-10. These are the documented standard-runner specifications; receipts
record the run's measured usage. A proof can exceed those resources.

## Trust and credit

OpenAI wrote the exact RAM formalization and all-length DFT reduction at
`openai/math` commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Our challenge changes seven names with suffix `Y` and changes the decimal
saving. All machine definitions and quantifiers remain unchanged. See `NOTICE`.

The submitted proof builds on Jacob Sussman's checker and framework and the
community circuit credited in PR #2. Authorship of that proof stays with its
authors. Comparator, Lean, nanoda, landrun, bwrap, the OS, and the pinned
Mathlib cache are part of the checking environment. Tool and source hashes
are included for audit. This runner does not perform line-by-line human review.

Logs can contain untrusted submission output. The controller does not stream
that output as Actions workflow commands. The authoritative gate is the exit
status of the pinned Comparator plus its completed acceptance output.

Local controller tests require only Python:

```sh
python3 -m unittest discover -s tests -v
```

Lean compilation runs in GitHub Actions, not on the office host.
