# CHANGELOG — Research Notes on ζ(9)

## v0.1 (first public release candidate, prepared 2026-09-25)

Initial public release. Content: nine research rounds (2026-09-24), the roadmap dependency graph
and platform layer (2026-09-24/25), distilled from the internal proof-state audit of 2026-09-25.

### Corrections applied against the internal audit (verified before release)

- **C-I — R19 coefficient sum (360 → 720).** The audit text says the Eulerian numerator of
  `∑ ℓ^6 q^ℓ` "sums to 360". The coefficients `1, 57, 302, 302, 57, 1` sum to **720 = 6!**, the
  value required for the principal part `(z−k)^{-7}`; the displayed kernel formula with prefactor
  `(2π)^7/720` was and is correct. The separate trigonometric form
  `π^7[302 cos πz + 57 cos 3πz + cos 5πz] / (360 sin^7 πz)` has numerator coefficients summing to
  360 against denominator 360 and is self-consistent; the only script using these identities uses
  the trigonometric form and is unaffected. Both forms were re-verified numerically against a
  direct truncated sum (agreement ~1e-18 at 50-digit precision). **Impact: audit prose only; no
  formula, script, or archived constant changes.** The note uses 720.
- **C-II — R20 phase-exponent scale (1/n → n).** The audit's R20 wrote
  `log|R| = (1/n) Re Φ_α(w) + O_α(1)`, inconsistent with its own R21 and with the source note
  (`research/analytic.md` §3). Correct scale: `log|R_{n,m}(nw)| = n Re Φ_α(w) + O_α(log n)`,
  equivalently `(1/n) log|R| = Re Φ_α(w) + o(1)`; the exact `n log n` cancellation
  (3−14α vs 14α−3) is consistent only with the `n·Re Φ` scale. **Impact: none downstream** — the
  uniform estimate (R21) and the limsup bound (R22) already used the correct scale.
- **C-III — f_* vs τ inequality direction.** The certified statement is `−10.564155 < f_* < −10.564`,
  i.e. **f_* < −τ** with τ = 2641/250 = 10.564 (equivalently −f_* > τ); the proved decay exceeds
  the threshold by ≈ 1.54×10⁻⁴ per unit n. The audit's roadmap paragraph ("with −f_* < τ proved")
  and gap item G8.7 ("the proved statement is −f_* < −τ") both state the wrong direction; the
  source roadmap (`roadmap/DAG.md`) states `f_* < −τ` correctly and the audit's numerical margin is
  correct. Re-verified numerically (margin 0.0001538376402…). The note uses the correct direction.

### Classification downgrades / clarifications (no new results claimed)

- Round-4 all-n nonvanishing is stated as conditional on the cited external theorem
  (Borcea–Brändén, Thm. 2), matching the source note.
- The roadmap's 27 "note-proved" nodes are reported as note-proved (prose proofs, not Lean-checked,
  not platform theorems); the audit is not presented as a substitute for independent verification.
- The eight platform theorems are reported as **abstract**; they are never cited as verification of
  the concrete ζ(9) constructions.
- The five-point cubature (FQ) weight positivity is reported as a finite scan (not positive at
  n = 1000, 2000; positive at n = 6000, 20000); the positivity threshold is reported as located
  only within (2000, 6000], not as a determined constant.
- The imported potential constant M = −1329/200 (Gram branch) is reported as imported and not
  independently certified; its literature source was not re-verified for this release.
- No claim was promoted from "finite numerical" to "proved" for this release; no open node was
  closed; no new large-scale experiment was run.

### Known issues carried (not resolved in v0.1)

- R8 (improved integerization): written proof is a sketch; conclusion re-verified on five
  parameters only.
- R21: uniformity argument written with untracked constants.
- R35: rank-bound index shift is an unverified adaptation of the s = 7 pattern (differs by one
  unit; no conclusion depends on it).
- R31/R32 (Gram functional and positivity): inherited from earlier local notes, not re-derived.
- The internal audit file included in the source ZIP retains its original text (with the three
  misstatements above) as provenance; the corrections are documented here and in §8 of the note.
- Platform identifiers (private mission UUIDs, item and comment IDs) are redacted from the public
  copies of internal documents; the platform receipts themselves are not included in the ZIP.

### Revisions from the pre-release author review (2026-09-25, second pass)

Wording-only revisions; no new results, no new computations, no status promotions.

- **R-V — §5 upper-bound wording.** Replaced "It cannot imply nonvanishing, decay, or an
  asymptotic equality; no chain of upper bounds can." (too strong: a chain of upper bounds *can*
  establish decay, e.g. |L_n| ≤ e^(−cn)) with: the bound is on the exponential rate of |L|; the
  certified bounds on the tested parameter grid are positive and do not establish decay; upper
  bounds alone do not establish nonvanishing or a matching asymptotic formula.
- **R-VI — §10 sampling scale (0.19 → 0.055).** The displayed constant
  a = 330.65816828687 gives 1/√a = 0.05499337…, so √（n/a) ≈ 0.055√n, not 0.19√n. Arithmetic
  re-checked against the displayed decimal only; the interval certification of a itself was not
  re-derived. "First fully valid at n = 2000" is now explicitly scoped to the listed discrete
  test values; no minimality over all n is claimed.
- **R-VII — §10 positivity threshold.** Removed "the positivity threshold lies in (2000, 6000]";
  the finite observations (not all positive at n = 1000, 2000; all positive at n = 6000, 20000)
  do not locate a threshold for positivity at all sufficiently large n. Noted that the archived
  computations were not re-run for this release. (This CHANGELOG's classification entry was
  reworded identically.)
- **R-VIII — §11 no strict-strengthening claim.** The two accepted root decompositions are no
  longer described as "strictly stronger than the root": pinning a fixed exponential rate is not
  by itself sufficient to prove strict strengthening, and the precise coefficient/construction/
  indexing constraints of the formal statements were not checked for this release.
- **R-IX — §12 split into obligations vs formalization tasks.** Added a preamble: the C-items
  mix mathematical obligations of several alternative routes with formalization engineering; they
  are not asserted to be jointly necessary, and a complete rigorous written proof does not
  require prior formalization. C6, C10, and the formalization half of C7 moved to a separate
  "Formalization tasks" list (labels unchanged).
- **R-X — §13 scope of the "opposite direction" remark.** Added: the described mismatch is the
  present state of these particular routes, not a claim that any route of this type must first
  obtain an exact asymptotic for the true multiplier or a quantitative lower bound for |L|.
- **R-XI — metadata R8 qualifier.** The Zenodo Description now says "an elementary integrality
  result and a proposed sharper multiplier supported by a written proof sketch and finite
  checks" instead of the unqualified "two integerization theorems".

### Author decisions recorded (2026-09-25)

- Author display name **Yuxuan Xu** (Zenodo fields: family Xu / given Yuxuan); affiliation
  School of Computer Science, Wuhan University; ORCID 0009-0001-8760-5277 (format and check
  digit verified; account ownership not independently verified online).
- Licenses: note and research documentation **CC-BY-4.0**; original software **MIT**;
  third-party materials retain their original licenses. License texts added under `LICENSES/`
  and the ZIP repacked (entries 284 → 287).
