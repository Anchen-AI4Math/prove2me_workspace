# Eightfold endpoint zeros: an exact repair candidate, with new gaps

This supplement keeps the main boundary-leakage theorem in
`new-linear-form-route-2026-10-02.md` intact. It examines the root agent's
explicit repair candidate rather than claiming that every derivative-based
construction has the same obstruction. No irrationality claim is made.

For n>=1 define

    R*_n(t) = (4n)!^2/(n!)^8
                * [(t-1)...(t-n)]^8 / [t(t+1)...(t+4n)]^2,
    L*_n = -1/8! sum_{k=1}^infinity (R*_n)^(7)(k).

Its degree difference is still -2. It has an eighth-order zero at every
integer k=1,...,n, so the seventh derivatives at all these integers vanish
exactly. In particular the polynomial endpoint leakage proved in the main
note does not apply to this new rational function.

Writing R*_n=sum_{j=0}^{4n}[A*_j/(t+j)^2+B*_j/(t+j)] gives

    A*_j = binom(4n,j)^2 binom(n+j,n)^8 in Z_(>0),
    B*_j = A*_j [10H_j-8H_(n+j)-2H_(4n-j)],
    sum_j B*_j = 0.

Taking the value and logarithmic derivative of (t+j)^2 R*_n at -j proves
these formulas; degree -2 proves the residue sum. Thus the identity is
strictly isolated, again without any assumption on relations among zeta
values:

    L*_n = A*_n zeta(9)-b*_n,
    A*_n = sum_j A*_j,
    b*_n = sum_j [A*_j H_j^(9)+B*_j H_j^(8)/8].           (1)

The sum converges absolutely, since (R*_n)^(7)(k)=O_n(k^-9).

One safe clearer remains

    d_(4n) B*_j in Z,     8d_(4n)^9 b*_n in Z.           (2)

Indeed all harmonic denominators are <=4n, except possibly H_(n+j)
with n+j<=5n. If a prime power p^e is larger than 4n and at most n+j,
then n,j<p^e<=n+j, so binom(n+j,n) has a Legendre carry. Its eighth power
provides valuation at least eight, clearing the one possible extra level
above floor(log_p(4n)). The other prime powers are already cleared by
d_(4n). This proves (2) for all primes. In particular the safe clearer has
logarithmic rate 36 per n by PNT, but this is not the full primitive cost.

The full primitive scale is exactly

    c*_n=den(b*_n)/gcd(A*_n,num(b*_n)),
    primitive value = c*_n L*_n.                         (3)

The scalar prefactor has rate

    log[(4n)!^2/(n!)^8]/n -> 8log4.

These facts do not decide the behavior of (3). Eliminating the first n
summands removes the specific leakage mechanism; it does not by itself
prove positivity or nonvanishing of the remaining seventh-derivative
sum. Its summands need not have one sign. A valid further route needs an
all-parameter nonvanishing argument, an actual analytic rate for L*_n,
and the full-content estimate (3). This supplement supplies none of those
three missing asymptotic conclusions by promoting finite observations.

The dedicated checker verifies the complete polynomial partial-fraction
identity, all eighth-order endpoint cancellations, (1)--(3), and rigorous
nonzero Arb enclosures for n=1,...,6. It reports the observed signs and
primitive magnitudes without imposing an unproved common sign.
The certified signs are negative for n=1,2,3 and positive for n=4,5,6;
all six primitive absolute values exceed one. In particular this variant
does not give a positive form for every parameter. These counterexamples
to uniform positivity do not decide eventual nonvanishing or decay.

An independent written review by the shifted-arithmetic agent also passed
the root's distinct growing-rank-one Gram draft
`growing-rank-one-route-2026-10-02.md`: its density upper bound, scaled
Riemann estimate, monic Legendre lower bound, exponent quantifiers, and
generic large-prime Jacobi reduction were all checked. This supplements
the bounded scripts; it is not a Lean verification.
