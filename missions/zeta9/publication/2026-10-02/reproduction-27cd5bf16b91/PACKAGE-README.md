# Zeta(9) research source package — 2026-10-02

Public mission: [weighted lattice route](https://prove2.me/missions/Irrationality_of_%CE%B6(9)%3A_weighted_lattice_route).

ζ(9) irrationality is **not proved**. This package preserves our dated written
research, exact finite certificates and selected earlier Lean source modules.
The 2026-10-01/02 research is not newly formalized in Lean. Packaging and Python
reruns do not certify a Lean build. See `missions/zeta9/PUBLIC_OVERVIEW.md` and
`missions/zeta9/status.md` for proved results, finite evidence and open exits.

## Contents and provenance

The archive retains the original `missions/zeta9/` paths and exactly selected
`Theorems/`, `Definitions/`, `Solutions/` imports if needed. Original source and
certificate bytes are unchanged; `source-manifest.json` records their SHA-256,
size and selection reasons. The generated `lakefile.lean` includes only the
selected theorem roots and the original pinned Mathlib commit. It does not
copy the workspace's unrelated task targets. Third-party papers, downloaded
source repositories, credentials, API/platform snapshots, compiled artifacts,
caches and external Python package binaries are excluded. Older paper-audit
scripts may require excluded third-party material obtained separately from
their documented sources; they are not part of the five-group rerun claim.

## Reproduce the five latest groups from an independent extraction

Use Python 3.12 in a virtual environment. From the extracted archive root:

```text
python -m venv .venv
# Activate .venv for your operating system.
python -m pip install -r requirements.txt
python missions/zeta9/scripts/verify_direction_arithmetic_next.py
python missions/zeta9/scripts/verify_growing_rank_one_route.py
python missions/zeta9/scripts/verify_dispersed_pole_frontier.py
python missions/zeta9/scripts/verify_new_linear_form_route.py
python missions/zeta9/scripts/verify_new_linear_form_repair.py
```

Or run `python rerun_latest.py`, which starts the same five scripts in separate
processes, compares generated JSON bytes with the preserved original records,
and writes `rerun-report.json`. Scripts rewrite only the extracted verification
copies. Keep the original zip and manifest for immutable provenance. The old
`tmp/zeta7/exact_packages` search path may be absent: normal installed
`python-flint` satisfies the imports. No files from that old path are packaged.

All five original certificates record finite checks and bounded sample counts.
Their successful rerun is not a proof of the all-parameter mathematical claims
or of irrationality. Those claims and their open conditions are in the written
research and independent reviews. No all-task Lean build is required or run.

## Offline package verification

The packaging recipe is
`missions/zeta9/scripts/package_public_research_2026_10_02.py`.
Its `--verify` option extracts the final zip into a fresh local directory and
runs the five groups with separately installed external Python dependencies.
The sidecar `reproduction-report.json` identifies the exact tested zip hash,
runtime versions, source hashes and byte comparisons. It performs no network
calls, credentials access or Lean compilation.
