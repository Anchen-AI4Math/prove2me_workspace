# Actual Franel gamma identity: differential certificate

Date: 2026-10-02.

Source: `../../formalization/FranelGammaCertificate.lean`.
SHA-256: `31a57451b2f65766c63f5c37af223299771da3634e0938fff4878bde9c67e73a`.

Actual command from the workspace root:

```
lake env lean missions/zeta9/formalization/FranelGammaCertificate.lean
```

The final compilation returned exit code **0**, with no warnings or errors.
Its actual six-line compiler output is saved in `franel-gamma-lean.log`.
All six printed theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The source contains no `sorry`, `axiom`, `constant`, or
assumed gamma expansion.

The actual all-parameter identity is

\[
\sum_{j=0}^{n}\binom{n}{j}^{3}X^{j}
=\sum_{k=0}^{\lfloor n/2\rfloor}
  \binom n{2k}\binom{2k}k\binom{n+k}k
  X^k(1+X)^{n-2k}
\]

for every natural `n`, as an equality in `ℚ[X]`. The two sides are explicit
finite polynomials, not abstract sequences substituted for the original
binomial coefficients.

The proof uses the actual Euler operator `θp = Xp'` and

\[
L_n=(1+X)\theta^3-3nX\theta^2+3n^2X\theta-n^3X.
\]

1. Its coefficient at `j+1` is
   `(j+1)^3 p_(j+1) - (n-j)^3 p_j`. Binomial coefficient recursion proves
   `L_n F_n=0` for the actual left-hand polynomial.
2. Since `(j+1)^3 ≠ 0` in `ℚ`, two polynomial elements of the kernel with
   the same constant coefficient are equal. This is proved by induction
   on every coefficient, with no degree assumption.
3. For `γ_(k,t)=X^k(1+X)^t`, the exact polynomial identity is
   `L_(2k+t) γ_(k,t) = (1-X)(k^3γ_(k,t) -
   (3k+t+1)t(t-1)γ_(k+1,t-2))`. The natural truncations in `t-1,t-2`
   are verified in the separate boundary cases `t=0,1,2`.
4. For the actual natural coefficient
   `a_(n,k)=choose(n,2k)choose(2k,k)choose(n+k,k)`, factorial identities
   prove `(k+1)^3a_(n,k+1) =
   (n+k+1)(n-2k)(n-2k-1)a_(n,k)` for every `n,k`. Outside the support,
   the proof handles the zero binomial coefficients explicitly.
5. Thus the operator applied to each admitted gamma term is
   `(1-X)(B_k-B_(k+1))`, where
   `B_k=k^3a_(n,k)γ_(k,n-2k)`. The finite sum telescopes exactly.
   Both endpoint terms vanish: `B_0=0`, while
   `choose(n,2(floor(n/2)+1))=0` at the other endpoint.
6. The gamma polynomial has constant coefficient one, as does `F_n`.
   Kernel uniqueness gives the complete displayed identity.

This closes the Franel expansion input used by the coefficient cone route.
The separate coefficient agent integrates it with the actual weighted
polynomial and the all-parameter paired-operator bounds before claiming
the original coefficient theorem. This file alone makes no irrationality
or denominator-growth assertion. No shared module, scope, existing frozen
platform payload, or platform state was changed by this subtask.
