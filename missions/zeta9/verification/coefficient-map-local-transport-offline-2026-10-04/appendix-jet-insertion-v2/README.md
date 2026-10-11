# Uncompiled insertion proof scripts

`JetInsertionCandidate.lean` contains twelve complete written proof candidates,
with no admission or new axiom. **No Lean invocation has been made for this file.**
It is an appended design artifact, not a verified theorem module.

The shorter route uses the existing `clearedPolePolynomial_comp_shift` plus one
new direct factor lemma from `Finset.mul_prod_erase`:

```
polePolynomial m = (X + C j) * clearedPolePolynomial m j
(polePolynomial m).comp (shiftedVariable j) = X * shiftedClearedDenominator m j
```

For upper insertion, shift the full successor pole-product identity and cancel
the common polynomial X. For lower insertion, shift the already proved
`polePolynomial_successor_shift`, compose `(X+1)` with the guarded shifted
variable, use the old pole-product factor identity, then cancel X. This avoids
reindexing an erased finite set and isolates Nat subtraction under `1 <= j`.

The two actual cleared-series identities then follow from
`numeratorClearedSeries_unique` and its denominator identity. At the inserted
endpoints, `X^9` divides the actual shifted numerator, so all coefficients of
degree <9 vanish by `PowerSeries.X_pow_dvd_iff`. Applying coefficient `9-s`
proves upper, lower and double insertion for every actual numerator A, m=0
included, without strict properness. The statements retain `j <= m+1` and
`1 <= s <= 9`, matching the existing finite exact checks and counterexamples.

All twelve scripts are uncompiled. Remaining risks are ordinary Lean expression
rewrites/coercions, product lemma orientation, function-composition rewriting and
nat/rational cast normalization. The mathematical reductions use only actual
pole factors and actual series uniqueness, with no PF existence or abstract
coefficient assumptions. The earlier frozen nineteen-file design package and
all native author sources/independent preparation files remain unchanged.
