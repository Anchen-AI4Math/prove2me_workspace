# Zenodo record metadata (draft, v0.1) — for author review before upload

> Identity and license fields below reflect the author's decisions of 2026-09-25
> (see AUTHOR_REVIEW.md). Final publication is still the author's action.

- **Title:** Research Notes on ζ(9): Constructions, Computations, and Open Problems
- **Version:** v0.1
- **Upload type:** Publication → Working paper / Research note
- **Creators:** Yuxuan Xu
  - Family name: **Xu**; Given names: **Yuxuan** (do not swap the Zenodo fields)
  - Affiliation: School of Computer Science, Wuhan University, Wuhan, China
    (in the Zenodo affiliation field prefer the ROR-matched entry "Wuhan University")
  - ORCID: **0009-0001-8760-5277** (format and check digit verified against the ORCID
    algorithm; account ownership not independently verified online)
- **Publication date:** set at publish time. NOTE: Zenodo's default is the draft-creation
  date — verify at publish that the stamped date equals the actual first-public date;
  do not backdate. Research dates (24–25 September 2026) are stated inside the note.
- **License (mixed record, both declared):**
  - **CC-BY-4.0** — the research note (PDF/HTML), its text content, and accompanying
    research documentation;
  - **MIT** — original software files (Python scripts etc.) written by the author.
  - Third-party materials retain their original licenses/notices. See `LICENSES/` in the
    source ZIP and the Licensing section of README.md.
- **Keywords:** zeta values; irrationality; linear forms; Gram determinants; p-adic valuations;
  contour methods; formal verification; Lean 4; open problems
- **Related identifiers:** none in v0.1 (no DOI imports; the internal workspace is private).

## Description (paste into Zenodo)

Research notes recording a two-day effort (24–25 September 2026) on the irrationality of ζ(9):
nine research rounds, a 40-node roadmap dependency graph, and a partial formalization layer.

**This note does not claim a proof of the irrationality of ζ(9).** Version 0.1 publishes the
concrete constructions, the local arguments that are proved in writing (with stated caveats), the
computations that were actually run and archived, and the open problems that remain.

Contents: (i) a rational-function construction giving linear forms A·ζ(9)+B with exact partial
fractions, an elementary integrality result and a proposed sharper multiplier (headline
multiplier d_n^9/G) supported by a written proof sketch and finite checks, exact p-adic valuation
formulas, and a certified analytic upper bound limsup (1/n) log|L| ≤ sup H_α with six
interval-certified constants; (ii) a positive-weight Gram route with positivity and exact-degree
statements at finite K; (iii) finite certified computations (21 linear-form and 21 Gram samples,
direct-sum certificates) with scripts and Arb/exact-rational artifacts; (iv) the later rounds
(higher-order poles, rational shifts, an all-n leading-coefficient nonvanishing theorem, a
rational connection with exact determinant, and four scoped negative results); (v) the current
roadmap: 13 open nodes, 27 note-proved nodes, eight abstract formal theorems, and a canonical
closure list C1–C10 (mathematical obligations plus separate formalization tasks — the items are
not asserted to be jointly necessary for an irrationality proof).

Every statement carries an explicit status tag (proved-in-writing / conditional / modulo another
claim / finite numerical / heuristic / open). Finite computations are reported as finite; no
infinite-sequence conclusion is drawn from them. AI assistance is disclosed in §14 of the note.
Three factual misstatements in the internal audit were corrected before release (coefficient sum
720, phase scale n·Re Φ, and the direction f_* < −τ); see CHANGELOG.md.

Files: zeta9-research-note-v0.1.pdf (note), zeta9-source-v0.1.zip (note source, research notes,
scripts, verification artifacts, license texts), README.md, CHANGELOG.md.

Licensing: the note and research documentation are CC-BY-4.0; original software is MIT;
third-party materials retain their original licenses. See the bundled README.md.
