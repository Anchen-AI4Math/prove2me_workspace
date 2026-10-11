# Pure author mathematical review — 2026-10-07

This is a SOURCE review of the 17 uncompiled endpoints. It is not a Lean
compilation, kernel check or independent proof review. No Lean or API call
was made for this preparation. The Outputs dependency is the frozen native
AUTHOR export `8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6`;
Root has separately rehashed its complete author report and 636 stable files.
The new SOURCE is `bf21501e51b31a9e9e754f8c7f22dcd734aa1435d5770838d2118bb40b662446`.

## Direction and coordinate conventions

`actualFMatrix n r i = aggregate n (X^r.val) i`. Rows index monomials;
columns index the actual outputs B, rho3, rho5, rho7, rho9. Hence a quartic
with coefficient row c has output c vecMul F(n). Gamma(n) has row r equal
to the polynomial coefficients of the actual chosen connectionP(n,r).
The verified finite transport is F(n+2) = Gamma(n) * F(n).

The definition transferMultiplier(n,W) uses the row
`polynomialCoordinates W vecMul connectionGamma n`. Its output at n is
(c Gamma(n)) F(n) = c (Gamma(n) F(n)) = c F(n+2). No transpose or right
multiplication of F by Gamma is used. The actual Mathlib SOURCE declaration
`Mathlib/Data/Matrix/Mul.lean:873` was read: vecMul_vecMul takes v, M, N
and proves exactly this associativity direction.

## Quartic domain and genuine choices

The transfer definition always has degree at most 4, because it is built by
coordinatePolynomial. The output equality additionally needs
W.natDegree <= 4: the final step uses polynomial_restore W hW. Without
this hypothesis, polynomialCoordinates records only the first five
coefficients; no claim for arbitrary higher-degree W is made.

For X^r.val with r:Fin5, natDegree_X_pow and r.isLt give degree <= 4.
For connectionP, the bound is proved by connectionPair_spec for n >= 1.
For inverseMultiplier and selectedIntegerMultiplier, their existing actual
degree bounds supply the same hypothesis. No degree identity of a product
or nonzero polynomial is assumed. The connection choice is the actual
unique Connection pair; the preparation copies genuine SOURCE bytes and
does not replace this choice with a new abstract matrix.

## Exact real values and infinite sums

exactL n W is definitionally prescribedL(aggregate n W), using the five
actual finite rational outputs. Thus equality of aggregate gives equality
of these real expressions for all n >= 1 and quartic W. This formal value
equality does not by itself assert HasSum when n is odd.

For HasSum endpoints, even n >= 2 is explicit. even_add_two derives Even
(n+2). The actual StrongProperMultiplier condition is
2*n + 2*W.natDegree <= 9*(n+1)-2; the existing
quartic_is_strong_proper theorem proves it from n >= 1 and degree <= 4.
The existing actualSeries_hasSum_exactL and actualSeries_norm_summable
provide the two genuine infinite series and absolute convergence. Only
their limits are rewritten by the newly proved finite output identity.
The tsum equality then follows from both HasSum.tsum_eq conclusions.
There is no assertion that the two sequences agree term by term.

## Inverses and selected integer output targets

The inverse endpoint transfers the genuine inverse multiplier at n+2 to
the actual output b at n, then applies the existing quartic uniqueness
theorem at even n >= 2. Consequently its coefficient row satisfies
c(n+2,b) Gamma(n) = c(n,b). Matrix invertibility and uniqueness are existing
proved results, not added hypotheses of the candidate.

The selected endpoints specialize b to the same
selectedIntegerOutput(b,a):Fin5->Q at both parameters. That row is
(b,0,0,0,a), with b at B and a at rho9. The common real target is
b + a*zetaReal(9). The multiplier remains a rational-coefficient quartic;
an integer output target does not prove an integer-coefficient multiplier.
Integrality, denominator/height/content estimates, the J condition and
irrationality of zeta(9) remain outside these endpoints.

## Evidence and execution boundary

The pure preparation contains 22 native SOURCE modules, 5 SOURCE controls,
17 complete expected theorem headers, one complete expected definition,
and 9 closed boundary SOURCE cases. These are planned checks, not reached
kernel results. No package junction, build directory or proof object exists
in the new private project .rt/ost1. The planned serial run has 29 calls
and 27 own-object resolutions. Its longest own object path plus 64 is 217.

The expected scripts deliberately call the actual source theorems with
their complete original quantified headers. This is an AUTHOR statement
binding check; it is not a second independent proof. An independent lane
must later rebuild and audit the candidate from SOURCE under its own
runtime. Any compiler failure must retain source/log/exit/object evidence,
and corrections must use a new version without editing frozen preparations.
