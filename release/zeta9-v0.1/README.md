# Research Notes on ζ(9): Constructions, Computations, and Open Problems — v0.1 release package

**This release does not claim a proof of the irrationality of ζ(9).** It publishes concrete
constructions, local arguments, archived computations, and open problems from a research effort
of 24–25 September 2026.

## Contents of this directory (release staging area)

| file | audience | purpose |
|---|---|---|
| `zeta9-research-note-v0.1.pdf` | public | the research note (print of `note/zeta9-research-note-v0.1.html`) |
| `zeta9-source-v0.1.zip` | public | source archive: note source + research notes + scripts + small verification artifacts (whitelist-packed) |
| `note/zeta9-research-note-v0.1.html` | public | note source (self-contained HTML + MathJax; also inside the ZIP) |
| `README.md` | public | this file |
| `CHANGELOG.md` | public | version log, including the three pre-release corrections C-I/C-II/C-III |
| `zenodo-metadata.md` | public | draft Zenodo record metadata (license/affiliation/ORCID pending author confirmation) |
| `AUTHOR_REVIEW.md` | **private — not in the ZIP, not for upload** | author confirmation checklist before publishing |
| `staging/` | private | packing workspace used to build the ZIP (sanitized copies) |

## Reproducing the computations

The archived scripts under `missions/zeta9/scripts/` (round 1) and `missions/zeta9/round*/scripts/`
(rounds 2–9) were run with Python 3.13 plus `mpmath`, `python-flint` (Arb) and exact `Fraction`
arithmetic, from the workspace root. `missions/zeta9/verification/artifact-manifest.json` records
SHA-256 hashes of scripts, notes and evidence. Displayed decimals anywhere in the notes are
presentational; the certified objects are the archived rationals and Arb intervals.

The audit's independent re-checks live in `missions/zeta9/verification/audit-2026-09-25/`
(scripts + transcripts). The three small verification checks run for this release
(kernel identities in both forms, Eulerian coefficient sum, the `f_* < −τ` margin) are in
`release-checks/` inside the ZIP.

## Licensing

The research note, its text content, and accompanying research documentation are licensed under
**CC BY 4.0** (see `LICENSES/CC-BY-4.0.txt`), except where otherwise indicated.

Original software files (Python scripts and similar) are licensed under the **MIT License**
(see `LICENSES/MIT.txt`), except where otherwise indicated.

Third-party materials retain their original licenses and notices; inclusion in this archive does
not relicense them.

## How to cite

Yuxuan Xu, *Research Notes on ζ(9): Constructions, Computations, and Open Problems*, v0.1,
Zenodo, 2026. DOI: **[to be filled with the version DOI minted at publication]**.

If you use this note or the archived scripts in your research, please cite the record above.

## Boundaries (short form)

- No irrationality statement is made; the canonical open-problem list is §12 of the note.
- Interval-certified objects are the archived Arb balls and exact rationals; ordinary floats are not certified.
- Finite computations cover only the tested parameters; no infinite-sequence conclusion is drawn from them.
- Eight platform theorems exist with abstract statements; no concrete ζ(9) object has a Lean definition.
- The internal proof-state audit is included as provenance; its three factual misstatements are
  corrected in §8 of the note and logged in `CHANGELOG.md`.
