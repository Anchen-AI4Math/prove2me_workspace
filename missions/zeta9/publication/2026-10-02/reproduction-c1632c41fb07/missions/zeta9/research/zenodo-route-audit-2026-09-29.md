# Zenodo routes: a concrete ζ(7) countercheck and a ζ(9) positive-moment option

Started 2026-09-29; completed 2026-09-30. This is a bounded public-source audit,
not a claim that the literature has been exhaustively searched. No status,
scope, existing certificate, or Lean file was changed.

## 1. Located manuscripts and status boundaries

* [Aabir Fauzan, ζ(5) is irrational](https://zenodo.org/records/22826419),
  September 17, 2026, v1. The original 32-page PDF was downloaded and its
  SHA-256 is `a42c05ccc46b9a7c36428913453c4617202c59109713ba20f464ab9ec640d0da`.
  It proposes growing-degree integral polynomials built from positive Hankel
  determinants. This audit reads the construction and positivity argument;
  it does **not** independently verify all of its arithmetic estimates or
  certify the complete irrationality theorem. The separate team review of
  the Dan Romik repository should determine the status of that formalization.
* [Prince Anand, Zeta 7 is Irrational](https://zenodo.org/records/22920911),
  September 23, 2026, v1. This is **not** a Fauzan ζ(7) paper. The 42-page PDF
  has SHA-256 `18b44b7ee0783ad43557d240b9c28f3167eef0350df163b3dc1c12e70f88e753`.
  Its page acknowledges a mismatch between two decay constants. Sections 2–3
  below exhibit a separate exact contradiction in the arithmetic integral
  supporting decay. Thus this version does not establish its claimed theorem.
* Searches for Zenodo ζ(9) irrationality, including a native Zenodo API query,
  did not locate a relevant standalone real ζ(9) proof to audit. This is a
  search outcome, not evidence of nonexistence. A returned title concerning
  **2-adic** ζ₂(7) is not the real ζ(7) problem and was not audited.
* [Shekhar Suman, arXiv:2609.22316](https://arxiv.org/abs/2609.22316),
  September 15, 2026, claims at least one of ζ(5), ζ(7), ζ(9) is irrational.
  Only its primary abstract was read here. It is neither a separately
  certified result of this audit nor a claim about ζ(9) alone.

Zenodo hosting, a DOI, a repository, and formalization progress are distinct
from an independently checked complete proof. Social discussions were used
only to locate original documents; none is an input to the countercheck.

## 2. An exact contradiction in Anand Table 5

The manuscript uses α=3/40, λ=37/40, y=p/K. Equation (71) defines

    R₀(y) = lim (−γ_out/K).

Section 5.1 sets γ_out=0 for p>K, so R₀(y)=0 for y>1. Its (72) is

    d(y) = (1+6α−3y−(1+2α−3y)₊)₊ + 1_(1/3,1/2)(y).

The (73) integrand is

    T(y)=R₀(y)−d(y)−2λ floor(1/y)+Σ_(j=1)^7(2λ−jy)₊.

At the interior point y=3/2, every term except j=1 vanishes. Thus, directly
from the printed definitions,

    T(3/2)=37/20−3/2=7/20.

But Table 5 (printed p.39), on the entire interval [1,37/20], gives

    T(y)=−239/20−2y,
    T(3/2)=−299/20.

The values differ by 153/10. This contradiction uses only rational arithmetic;
it does not involve difficult asymptotics, prime distribution, a numerical
quadrature, an endpoint convention, or a choice of cutoff M. The corresponding
PDF pages were rendered and inspected to rule out extraction of a mistaken
sign or indicator. On the whole open interval (1,37/20), the definitions in
fact give T(y)=37/20−y>0, whereas that table row is negative.

## 3. Exact reconstruction of the outer normalization cost

The reproducible script is
[`verify_zenodo_route_audit.py`](../scripts/verify_zenodo_route_audit.py).
It uses only Python's `Fraction` and a piecewise affine algebra supporting
exact addition, minimum, maximum, splicing, and integration. It independently
reconstructs the outer prime-sum cost from (54), (58), (59), and (62), and also
computes the literal (71)–(73) expression. This distinction matters: (71)
already includes the rank correction, whereas the sentence after (73)
subtracts it again.

Put r(y)=min(λ,(1+6α−3y)₊). The limit R=−γ_out/K coming from (59) is:

* For 1/3<y<1/2, put u=(1+α−3y)₊ and t=min(α,1−2y)+u. Then
  R=9(1−y)−16α−7t+min(r,y+u).
* For 1/2<y<1, put u=(1+α−2y)₊ and t=min(α,1−y)+u. Then
  R=9(1−y)−8t+min(r,y−α+u).
* For 1<y<37/20, R=0.

Legendre's formula in (62) gives the remaining cost

    −2λ floor(1/y)+Σ_(j=1)^7(2λ−jy)₊.

Indeed −v_p(S_K)/K has this limit; N<p throughout this range and the
factorial sum contributes the displayed positive parts. The j=6,7 terms
are identically zero here. Endpoint values have no effect on the integral.

The exact outputs are:

| Quantity | Exact integral | Approximation |
|---|---:|---:|
| Actual normalization formula (59),(62) | 453803/288000 | 1.5757048611 |
| Literal formula (71)–(73), with its extra subtraction | 397163/288000 | 1.3790381944 |
| Printed Table 5, also equal to the claimed (122) | −11002997/720000 | −15.2819402778 |

The script reproduces the printed table's negative integral exactly: the issue
is its disagreement with the defining formulas, not simply a summation typo.
Even granting the manuscript's other quoted integral contributions and its
real upper bound U=44/25, replacing only this outer contribution changes the
limiting upper-bound coefficient from a negative number to

    262829554253438845006139 / 54488694580149392640000
    = 4.823561222719941... > 0.

The finite-cutoff correction tends to zero as M increases. Therefore that
chain of bounds no longer implies the required negative quadratic decay.
**A positive upper bound does not prove that the determinants actually grow.**
This audit invalidates the stated proof route in v1; it does not rule out a
different estimate, different parameters, or a repaired construction.

The analytic comparison constants C*=3.64933512875... and I(ρ)=−3.14332508938...
were separately recomputed at high precision and matched the text; a few
point checks of its potential inequality also agreed. Those checks do not
constitute a complete independent proof of that analytic lemma. They help
localize the exact failure without blaming all sections of the manuscript.

## 4. What does transfer: a fully nonzero ζ(9) moment family

Fauzan's Proposition 2.2 uses a positive measure to make the **whole** Hankel
determinant nonzero, before a rational normalization is chosen. This structural
idea can be independently extended to ζ(9), without accepting either paper's
arithmetic estimates. Here is the resulting elementary construction.

Let

    w₉(y) = 2(2π)^8 y^9 / 8! · Σ_(ℓ≥1) ℓ^8 exp(−2πℓy),   y>0.

It is positive, bounded at zero, and exponentially decreasing at infinity.
Define the rational functional on polynomials and simple poles at negative
integer squares by

    μ_X(t^e) = (−1)^e B_(2e+2) · Π_(j=3)^9(2e+j) / 8!,
    μ_X(1/(t+j²)) = j^8(X−H_j^(9)) + 1/(2j) − 1/8.

For every rational function R in this domain,

    μ_(ζ(9))(R)=∫₀^∞ R(y²)w₉(y)dy.                         (A)

For polynomial monomials, termwise integration yields

    2(2e+9)! ζ(2e+2)/(8!(2π)^(2e+2)),

which is the stated Bernoulli expression by Euler's even-zeta formula.
For a pole use f(y)=1/(exp(2πy)−1), so w₉=2y^9 f^(8)/8!. Polynomial division
followed by eight derivatives gives

    (d/dy)^8 [y^9/(y²+a²)] = 8! a^8 Im(a−iy)^−9.

Eight integrations by parts have zero boundary terms: at zero each boundary
product is O(y), and at infinity the f-derivatives decay exponentially.
[Hermite's formula, DLMF 25.11.29](https://dlmf.nist.gov/25.11.E29) then gives

    ∫₀^∞ w₉(y)/(y²+a²)dy = a^8 ζ(9,a) −1/(2a)−1/8.

For a=j∈Z_>0 this equals the pole formula above; partial fractions prove (A).

For arbitrary integers 0≤N<K, put h=K−N, D_m(t)=Π_(j=1)^m(t+j²), and

    G_K(X)_(i,j)=μ_X(D_N(t)^10 t^(i+j)/D_K(t)),  0≤i,j<h.

For every nonzero real polynomial q of degree<h, its Gram quadratic form is

    ∫₀^∞ D_N(y²)^10 q(y²)^2/D_K(y²) · w₉(y)dy > 0.

Consequently det G_K(ζ(9))>0 for **every** such N,K. Its degree in X is exactly
h: after cancelling D_N, the coefficient matrix is V diag(c_j)Vᵀ, where
V_(i,j)=(−j²)^i for N<j≤K and

    c_j=j^8 D_N(−j²)^9 / (D_K/D_N)'(−j²) ≠ 0.

The Vandermonde matrix V is square and invertible. Clearing the finitely many
rational coefficients gives a nonzero integer polynomial taking a positive
value at ζ(9). **No useful decay after clearing denominators has been proved.**
This is the new route's precise remaining quantitative obligation.

## 5. Relation to our fixed-direction gap

Our current rank-two linear-form family already has small volume, but a short
output could be a fixed rational zero direction. A positive moment determinant
avoids that particular nonvanishing problem by constructing a different,
growing-degree polynomial family whose value is strictly positive. It does
not prove that our old shortest output is nonzero, nor transfer our existing
linear-lattice denominator estimates to these Hankel determinants.

The appropriate test for this alternate route is to find integer polynomials
P_K of degree O(K) with 0<P_K(ζ(9))≤exp(−cK²) for some c>0. Under ζ(9)=a/b,
b^deg(P_K)P_K(a/b) would then be a positive integer tending to zero. The new
work must control the complete Q[X] functional, including the polynomial
quotient in partial-fraction division; estimates only at X=ζ(9) or only for
the pole terms cannot certify coefficient integrality.

Anand's failed outer integral is a direct warning against changing the weight
power and copying a previously successful arithmetic table. For ζ(9), any
trial parameters need a newly derived prime-class valuation profile, exact
piecewise integration, and a real-energy certificate in the same normalization.
The positive Gram mechanism is valid; the desired decay and irrationality
remain unproved.

## 6. Reproduction and retained evidence

Run from the mission directory:

    python scripts/verify_zenodo_route_audit.py

The output `verification/zenodo-route-audit-2026-09-29/certificate.json` stores
exact fractions, the piecewise affine normalization cost, the audited PDF
hash, and explicit limitations. That directory also contains the two original
PDFs, extracted text, and rendered source pages 21, 23, 24, 39. These copies
serve local checking and are not a republication or an external submission.

The countercheck does not depend on downloading a changing document at runtime.
Its rational counterexample is a proof of the stated internal inconsistency;
the auxiliary potential evaluations are only finite diagnostics.

Independent cross-review: the independent-audit agent inspected the rendered
original pp.21,23,39, reran the exact script successfully, and checked the ζ(9)
moment proof in §4. It confirmed both the counterexample and the distinction
between a positive upper bound and actual determinant growth.

## 7. Review of the root agent's single-pole experiment

The implementation `scripts/probe_single_pole_pade.py` uses the positive measure
above (with general odd s≥3), a fixed positive integer a, and moments
μ_X(t^k/(t+a²)). Polynomial division gives exactly the quotient and residual
term in the script. For dimension h≥1 put v_i=(−a²)^i. Its variable coefficient
matrix is B=a^(s−1)vvᵀ. At ξ=ζ(s), G=G(ξ) is positive definite, hence

    det(G+(X−ξ)B)
      = det G · (1+(X−ξ)a^(s−1)vᵀG^−1v).

Both det G and vᵀG^−1v are strictly positive. Therefore the determinant is
affine with a strictly positive slope for all a≥1 and h≥1; this is a uniform
proof, not a consequence of the three interpolation checks in the script.
The real constant ξ in this identity is merely a way to prove the slope's
sign; the original determinant belongs to Q[X].

The implementation multiplies its two rational coefficients by the positive
least common denominator and then divides by their positive gcd. Thus its
primitive integer form retains positive slope and positive value at ξ, with
no sign convention hidden in the normalization.

The independent rerun `scripts/review_single_pole_pade.py` checked the source
hashes, recomputed every coefficient and primitive multiplier, and recomputed
rigorous Arb values for all 60 recorded cases. For s=9 all 30 values exceed 1;
for s=3, 14 values lie below 1 and 16 exceed 1. All are positive. This agrees
with the source record and is retained in
`verification/zenodo-route-audit-2026-09-29/single-pole-review.json`.

These finite observations give neither an asymptotic obstruction for s=9 nor
an irrationality proof for any s. They also do not transfer the fixed-rank
rank-one slope identity to the earlier full-square-pole family, whose degree
is h rather than one.

## 8. Cross-review of the alternative-route note

Sections 2–5 of `research/alternative-route-2026-09-29.md` received a complete
independent mathematical read here. No correction was required. Its script
was inspected, but its 22-pattern computation was not independently rerun in
this review; that distinction is separate from the 60 single-pole reruns above.

For the Mellin family, row/column subtraction gives the stated positive
Schur complement, and the affine slope is det C>0. The primitive form is
exactly P X−Q when q=Q/P is reduced with P>0. The constraint p(1)=1 is exactly
the affine hyperplane used in the variational formula, even for arbitrary
sparse exponent sets. The inequality

    (−log x)^8/[8!(1−x)] ≥ (1−x)^7/8!

and the endpoint Jacobi norms give the claimed bound

    P ζ(9)−Q ≥ P/(8! K_D),
    K_D=(D+8)^2 binom(D+7,7)^2/8.

The closed form follows directly from successive differences: after using
binom(D+6,7)=D binom(D+7,7)/(D+7), the difference is
(2D+8)binom(D+7,7)^2. Thus the constant and degree-16 denominator threshold
are correct. This gives a necessary condition P<8!K_D for a value below 1;
it does not assert that every exponent set violates that condition.

For the completely monotone family, the partial fractions and ΣB_j=0 cancel
the even ζ(8) term with the displayed factor 1/8. The standard denominator
8d_(M+n)^9 is valid. In the analytic lower bound, the two repeated reciprocals
1/T alone contribute eight monomials of degree seven to h_7, so h_7≥8/T^7;
this explains why the bound is R_n(T)/T^7 with no missing factor of eight.
The upper bound h_7≤(Σreciprocals)^7 and the displayed integral comparison
give only polynomial losses. Stirling therefore yields the stated rate for
every fixed ρ≥0, including ρ=0 by R_n(1)=(n+1)^−2.

Finally F'(ρ)=9+2log(ρ/(ρ+1)) has one zero, with F''(ρ)>0. Substitution gives
min F=9+2log(1−exp(−9/2))>8.97. This disproves decay for that **standard
clearing factor and linear cutoff regime**. It does not rule out substantially
better primitive normalization, different pole patterns, or the full class
of positive constructions. The reviewed note preserves that boundary.
