# Harmonic denominator asymptotic transfer — 2026-10-02

The actual Lean 4.33.1 compilation is recorded in `lean-check.log`.
`formalization/HarmonicAsymptotic.lean` contains no `sorry`, custom axiom,
or assumed harmonic denominator baseline. All seven printed axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

From the workspace root, first compile the exact finite-prime dependency:

```powershell
lake env lean -o missions/zeta9/formalization/HarmonicPrimeValuation.olean missions/zeta9/formalization/HarmonicPrimeValuation.lean
$env:LEAN_PATH = (Get-Location).Path
lake env lean missions/zeta9/formalization/HarmonicAsymptotic.lean
```

The main theorem `harmonic_log_den_rate_of_pnt` proves, for every positive
natural order `s`, the full-sequence limit

`logDen (harmonicPower s N) / N → s`.

Its only external number-theoretic hypotheses are:

1. `ThetaPNT`: the actual Mathlib `Chebyshev.theta x / x → 1` as real `x → ∞`.
2. `LcmPNT`: `log (Nat.lcmUpto N) / N → 1` as natural `N → ∞`.

These are theorem arguments, not declared axioms. The fixed Mathlib source
search is recorded separately in `mathlib-pnt-audit.json`; the checked
revision contains elementary Chebyshev bounds and theta/psi comparisons,
but the required PNT convergence theorem was not found. Consequently this
file does **not** establish unconditional Theorem 1 of the research note.
The PNT input itself remains an outstanding formalization dependency.

The transfer proof supplies the actual arithmetic missing from an assumed
baseline: for each fixed `K`, it filters `Nat.primesLE N` by the literal
condition `N/(K+1) < p`, proves the logarithmic prime sum equals
`theta N - theta (N/(K+1))`, and excludes actual prefix numerator exceptions
using the explicit fixed threshold

`(K+1) * (max K (harmonicExceptionalProduct s K) + 1)`.

Every admitted prime then contributes exactly `s` to the valuation of the
actual reduced harmonic denominator. The fixed-`K` PNT lower limit is
`s * (1 - 1/(K+1))`; only after taking that limit does the proof send `K`
to infinity. The upper bound comes from the actual LCM divisibility.

The perturbation corollary now derives the harmonic baseline from these
PNT inputs and requires only the perturbation's own sublinear logarithmic
denominator condition. Positive integer reindexing is also proved; in
particular the actual `s=9, N=2M` denominator has normalized rate `18`,
under exactly the same PNT inputs.

No zeta irrationality goal, previous mission state, platform theorem status,
or frozen research release was changed by this subtask.
