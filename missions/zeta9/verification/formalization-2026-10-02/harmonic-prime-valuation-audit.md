# Harmonic large-prime valuation: verified arithmetic core

Date: 2026-10-02.

Source: `../../formalization/HarmonicPrimeValuation.lean`.

Actual command from the workspace root:

```
lake env lean missions/zeta9/formalization/HarmonicPrimeValuation.lean
```

Lean 4.33.1, Windows GNU release, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Final compilation exit code: **0**, with no warnings or errors.
The actual compiler output is `harmonic-prime-valuation-lean.log`.
Source SHA-256:
`bb7df45433a3441520c343356548ac2cd279e05a4b10ff59b8dd3a13d13a99fb`.

The source imports the shared `Definitions.Def_ZetaNine_HarmonicStability`
and uses its actual rational finite sum `harmonicPower` throughout. It
does not redefine the target harmonic numbers. No `sorry`, `axiom`, or
unproved `constant` declaration occurs in the source. All ten printed
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The all-parameter arithmetic proved here is:

1. For every `s,N` and `p>0`, split the actual finite sum into its terms
   divisible by `p` and its exact nonmultiple remainder. The result is both
   `H_N = p^(-s) H_(N/p) + U` and `p^s H_N = H_(N/p) + p^s U`.
2. For every prime `p` and arbitrary endpoint, `den(U)` is coprime to `p`.
3. If `N<p^2`, the actual prefix denominator `den(H_(N/p))` is coprime
   to `p`.
4. If additionally `s>0`, `p≤N`, and `p` does not divide the reduced
   numerator of the actual prefix, prove `padicValRat p H_N = -s` and
   `padicValNat p den(H_N) = s`.
5. For every first block `p≤N<2p`, the prefix is `H_1=1`, and the exact
   denominator valuation is `s` without an exceptional-prime assumption.
6. For arbitrary fixed `s,K`, define the explicit positive product
   `E_(s,K)=∏_(1≤k≤K) |num(H_k)|`. Every prefix numerator divides this
   product. If `N/p≤K`, `K<p`, `E_(s,K)<p`, and `p≤N`, derive the exact
   denominator valuation; the unit condition and `N<p^2` are proved,
   rather than supplied as assumptions.
7. For any finite set of primes satisfying these fixed-block bounds,
   prove `∏ p^s ∣ den(H_N)` and
   `s ∑ log p ≤ log den(H_N)` for the fully reduced positive denominator.

This closes the finite-prime-block arithmetic and explicit finite-exception
isolation in sections 1--2 of the original written research note. It does
not assert that every large prime is a unit without the proved threshold.

The PNT-dependent full-sequence limit `log den(H_N)/N → s` is still not
proved here. No PNT axiom, assumed denominator limit, prime-distribution
assumption, or irrationality conclusion is introduced by this file.

Integration note: `primeRemainder` and `harmonicExceptionalProduct` are
the two new actual definitions, currently in this standalone proof file.
The root integrator can place them in the corresponding shared Definitions
module while preserving their names and expressions. Shared modules,
scope, task status, and platform state were not edited by this subtask.
