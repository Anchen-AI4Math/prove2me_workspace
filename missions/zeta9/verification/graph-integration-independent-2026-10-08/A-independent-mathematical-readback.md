# Independent mathematical readback of the A platform targets

This text reads the exact candidate statements and their shared function bodies.
It does not itself certify compilation; the actual independent compiler receipts
and frozen final audit are separate evidence.

The common rational function is the original factorial-product coefficient-map
`actualR`, and `weightedR(n,W,t) = actualR(n,t) * W(t(t+n))`. The infinite real
sequence is obtained by evaluating at every positive integer t=m+1 and casting the
rational product to the reals. This is the complete infinite sum, including the
initial zero terms; it is not a finite numerical truncation or an assumed sum.

For every n >= 1 and integer r in [0,4], the first target bounds the true infinite
r-th moment by

`C (n+1)^10 exp(-(2641/250)n) n^(2r)`,

where `C = 5184 exp(18) + (729/224) exp(7)`. The definition of the moment multiplies
the real actual kernel by `[t(t+n)]^r` at each positive integer t.

For any family W_n of rational polynomials, each of degree at most four, the second
target bounds, for every n >= 1, the absolute value of the actual infinite weighted
sum by the same prefactor times

`H_n(W_n) = sum_{r=0}^4 |coeff_r(W_n)| n^(2r)`.

The polynomials may change arbitrarily with n, have arbitrary coefficient signs,
and have no assumed coefficient-growth restriction. The finite five-coefficient
weighted l1 height is the actual polynomial height appearing in this theorem.
It is not a separately postulated Euclidean lattice norm.

The final target asserts that a single real error sequence epsilon_n tends to zero
and, simultaneously for every n >= 1 and every rational quartic W, the absolute
value of the complete infinite sum is at most

`exp((-2641/250 + epsilon_n)n) H_n(W)`.

The existential error sequence is outside the polynomial quantifier: its decay
is coefficient independent. The whole function body of `uniformError` is

`[log(C) + 10 log(n+1)] / n`.

The theorem takes no assumed Summable, HasSum, moment estimate, parity, or
coefficient-growth hypothesis. Its complete 122-proof closure proves the analytic
facts needed for the sum and the upper bound. The independent raw contracts expand
the actual kernel/polynomial product, the norm summability, all five moment bounds,
and the explicit epsilon-limit expression without relying on names alone.

These targets do not construct short integer outputs in the selected two-dimensional
inverse-image lattice. They do not assert nonvanishing, any bound on that lattice's
first or second minimum, J, an exact saddle exponent limit, or irrationality of
zeta(9). A graph reduction must supply those genuinely missing construction-level
conditions rather than importing A and announcing the root proved.

The three Solution files each contain all 122 original proof bodies because the
platform proof submission is self-contained. Their repeated canonical names must
be compiled and audited in isolated contexts; importing all three together is not
a valid way to compare them. There are 29 distinct whole functions in the closure,
with the 13 new analytic functions included in that total.
