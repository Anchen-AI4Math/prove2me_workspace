# Unshifted Mellin frontier: rectangular minors control denominator cancellation

2026-10-01. This continues the Mellin construction in
[alternative-route-2026-09-29.md](alternative-route-2026-09-29.md),
the [sharp-error theorem](mellin-sharp-error-2026-09-30.md), and
the [earlier local-prime audit](mellin-prime-audit-2026-09-30.md).
The large-shift obstruction is proved separately in
[mellin-shift-arithmetic-2026-10-01.md](mellin-shift-arithmetic-2026-10-01.md).

The present result is a new all-parameter reduction of **large-prime
denominator cancellation** to the maximal-minor ideal of a rectangular
powered Hilbert matrix. It also gives strict consecutive monotonicity and
the raw Hankel determinant's exact quadratic rate. It does **not** prove
that P_D>=D^16 eventually or that P_D grows faster than every polynomial.
Those remain arithmetic questions; D<=24 computations are only finite
checks. No Lean run or external submission is involved.

## 1. Difference basis and the positive moment pair

Set N=2M, a_j=(N+j)^(-9), and let indices i,j below run from 0 to D-1.
The determinant-one basis change
x^M(x^(i+1)-1) -> x^M(x-1)x^i turns the Schur data into

\[
 C_D=(a_{i+j+1}-a_{i+j+2}),\qquad b_D=(-a_{i+1}),
 \qquad q_{M,D}=H_N+b_D^tC_D^{-1}b_D.            \tag{1}
\]

Define the positive densities

\[
 \tau_N(x)=x^N\frac{(-\log x)^8}{8!},\qquad
 \nu_N(x)=(1-x)\tau_N(x),\quad 0<x<1.
\]

Then a_(k+1)=integral x^k tau_N, and C_D is the monomial Gram matrix
for nu_N. In particular all C_D are positive definite. This exhibits
the difference matrix as a genuine Hankel moment matrix, rather than
merely a positive matrix with harmonic entries.

## 2. Every added consecutive exponent changes the approximation strictly

For n=D-1 let p_n be the monic degree-n orthogonal polynomial for nu_N,
and write

\[
 h_n=\int p_n^2\nu_N>0,\qquad
 \xi_n=\int p_n\tau_N.
\]

Gram-Schmidt and the Schur complement of the last row give the exact
increment identity

\[
 q_{M,D}-q_{M,D-1}=\frac{\xi_n^2}{h_n}.          \tag{2}
\]

There is no vanishing increment. Indeed
(p_n(1)-p_n(x))/(1-x) is a polynomial of degree at most n-1, so
orthogonality gives

\[
 p_n(1)\xi_n=\int_0^1p_n(x)^2\tau_N(x)dx>0.     \tag{3}
\]

All integrals are finite, including N=0. Thus p_n(1) and xi_n are
nonzero, and (2) is strictly positive for every D>=1 and M>=0.
This strengthens the earlier weak monotonicity statement; it does
not supply a denominator growth rate.

For an entirely rational determinantal version put d_D=det C_D,
d_0=1, and let m_D be the determinant of the D by D matrix whose first
D-1 rows are the first D-1 rows of C_D and whose last row is
(a_1,...,a_D). The block determinant formula gives m_D=d_(D-1) xi_(D-1),
and hence

\[
 q_{M,D}-q_{M,D-1}=\frac{m_D^2}{d_Dd_{D-1}}>0.   \tag{4}
\]

The numerator is an exact square of a mixed moment minor, not a
numerical sign observation.

## 3. The rectangular matrix and its maximal-minor ideal

Define the (D+1) by D rational matrix

\[
 K_{N,D}=((N+i+j+1)^{-9})_{0\le i\le D,\ 0\le j<D}.          \tag{5}
\]

Stacking b_D^t above C_D gives rows
-K_0, K_0-K_1, ..., K_(D-1)-K_D. The row transformation is an
integer triangular (D+1) by (D+1) matrix with determinant plus or
minus 1. Therefore the maximal-minor ideals of K_(N,D) and [b^t;C]
are equal over every Z_p for which their entries are integral.

Let p>N+2D be a prime. Every entry is p-integral. Put

\[
 d=v_p(\det C_D)\ge0,\qquad
 \delta=\min_I v_p(\det(K_{N,D})_I),            \tag{6}
\]

where I ranges over the D-row subsets. These minors are not all zero:
the first D rows of K are a positive definite Gram matrix for tau_N.
If y=adj(C_D)b_D, the maximal minors of [b^t;C] are det C_D and
the coordinates of y, up to signs. Thus

\[
 \delta=\min\{d,\min_j v_p(y_j)\}.              \tag{7}
\]

## 4. A square bound on all possible cancellation

**Theorem.** For every M>=0,D>=1 and every prime p>2M+2D,
with P_(M,D)=den(q_(M,D)),

\[
 \boxed{v_p(P_{M,D})\ge\max(0,d-2\delta).}      \tag{8}
\]

Moreover if delta=0, then v_p(P_(M,D))=d exactly.

Proof. Let z=b^t adj(C)b. The correction r=z/det C is rational and
strictly positive. The p-integral harmonic term H_N cannot change a
negative valuation, so
v_p(P)=max(0,d-v_p(z)). Consider the bordered matrix

\[
 B=\begin{pmatrix}0&b^t\\b&C\end{pmatrix},\qquad\det B=-z.
\]

Jacobi's adjugate identity, or the block inverse followed by polynomial
continuation, gives

\[
 yy^t-z\operatorname{adj}(C)
   =(\det C)\,[\operatorname{adj}(B)]_{\rm bottom}.             \tag{9}
\]

The matrix on the right is p-integral. If d<=2delta, (8) is trivial.
If d>2delta, (7) implies delta=min_j v_p(y_j)<d; choose a coordinate
y_j attaining that minimum. If v_p(z)>2delta, the jth diagonal of
the left side in (9) has valuation exactly 2delta: y_j^2 has that
valuation while z adj(C)_jj has strictly larger valuation, since
adj(C)_jj is p-integral. The right side has valuation at least d,
a contradiction. Hence v_p(z)<=2delta, proving (8). If delta=0 and
d>0, this argument gives v_p(z)=0, and if d=0 the denominator
valuation is automatically zero. This proves the exact final claim.

This argument does not require a simple determinant root, a Smith
rank-one defect assumption, positivity over F_p, or a hypothesis
v_p(det C)<9. Positivity over the reals is used to ensure the rational
Schur objects and maximal-minor ideal are nonzero.

There is an equivalent global integer statement. For any integer n>0
let n^(>T) denote its part supported on primes greater than T. Let

\[
 F_{N,D}=(\operatorname{num}(\det C_D))^{(>N+2D)},\qquad
 J_{N,D}=\left(\gcd_I|\operatorname{num}(\det(K_{N,D})_I)|
        \right)^{(>N+2D)}.
\]

The rational numerators are taken after reduction; all their
denominators have prime support at most N+2D. Equations (6)--(8) imply

\[
 \boxed{F_{N,D}\mid P_{M,D}^{(>N+2D)}J_{N,D}^2,
 \qquad P_{M,D}\ge F_{N,D}/J_{N,D}^2.}          \tag{10}
\]

Also P_(M,D)^(>N+2D) divides F_(N,D). If J_(N,D)=1, these two
integers are exactly equal. Consequently every newly created large
determinant prime survives in the primitive denominator unless the
**entire rectangular moment matrix** loses column rank modulo that
prime. Singular C alone does not suffice for cancellation.

## 5. Small forced exceptions explain the finite unshifted data

For p>max(9,N+2D), all arguments of the matrix are nonzero modulo p.
Fermat gives x^(-9)=x^(p-10) in F_p. Therefore

\[
 \operatorname{rank}_{\mathbb F_p}K_{N,D}\le p-9.               \tag{11}
\]

Indeed each column is the evaluation on D+1 points of a polynomial
of degree at most p-10. Thus if D>p-9, every maximal minor vanishes,
and its valuation is at least D-(p-9): an integral square matrix of
rank r modulo p has determinant valuation at least D-r, as follows
by integral row and column reduction.

For N=0 the simultaneous conditions p>2D, p>9 and D>p-9 permit
only p=11 at D=3,4,5 and p=13 at D=5,6. They force exactly the
following lower factors in J_(0,D):

| D | forced factor |
|---:|---:|
| 3 | 11 |
| 4 | 11^2 |
| 5 | 11^3 * 13 |
| 6 | 13^2 |

The exact D<=24 verification finds equality with this table and
J_(0,D)=1 for D=1,2 and D=7,...,24. Hence in those tested cases
with J=1 the large-prime part of P_D equals F_(0,D) exactly.
For example, at D=24 the whole denominator has 2,664 digits and
its large-prime part has 2,588 digits.

The polynomial rank upper bound (11) only explains **forced** rank
defects. It gives no converse asserting full column rank when
p-9>=D. Thus the observed absence of extra factors after D=6 is
not a theorem for all larger D or all larger primes.

There is a concrete counterexample to such a converse when fixed or
linear shifts are allowed: M=D=3, N=6 and p=19>N+2D. Here

\[
 \operatorname{rank}(K_{6,3}\bmod19)=1,\quad
 \delta=2,\quad v_{19}(\det C_3)=2,\quad v_{19}(P_{3,3})=0.
\]

The determinant's entire factor 19^2 cancels. This rank defect is not
forced by (11), since p-9=10>D. It has a direct explanation: modulo
19, x^(-9)=x^9 is the quadratic character, and at the six consecutive
arguments 7,...,12 its values alternate 1,-1,1,-1,1,-1. Thus the
rectangular moment matrix has rank one. This exact countercheck
rules out the naive full-column-rank assertion; it does not assert
infinitely many extra defects or disprove an eventual unshifted bound.

## 6. The raw real determinant has a precise main rate

For t=-log x, e^t>=1+t gives
t/(1-e^(-t))<=1+t. The maximum of (1+t)^8 exp(-t/2) for t>=0
occurs at t=15 and is less than 16^8. Together with -log x>=1-x,
this proves the global pointwise comparison

\[
 \frac{x^N(1-x)^9}{8!}\le\nu_N(x)
 \le\frac{16^8x^{N-1/2}(1-x)^9}{8!}.           \tag{12}
\]

Both comparison weights are integrable even at N=0. Denote by
G_D(b) the monomial Gram matrix for x^b(1-x)^9, b>-1. Positive
matrix comparison gives

\[
 (8!)^{-D}\det G_D(N)\le\det C_D
 \le(16^8/8!)^D\det G_D(N-1/2).                \tag{13}
\]

Every comparison matrix entry in (13) is rational, including
b=N-1/2: Beta(b+i+j+1,10)=9!/prod_(l=0)^9(b+i+j+1+l).
Its determinant is the product of monic Jacobi norms

\[
 h_k(b)=\frac{k!\,(k+9)!\,\Gamma(k+b+1)\Gamma(k+b+10)}
 {(2k+b+10)\Gamma(2k+b+10)^2},\qquad
 \det G_D(b)=\prod_{k=0}^{D-1}h_k(b).           \tag{14}
\]

For fixed b, Stirling's formula gives
log h_k(b)=-k log 16+O(log(k+2)). Applying (13) at N=0 gives

\[
 \boxed{\log\det C_D=-(\log4)D^2+O(D\log D).}  \tag{15}
\]

More generally, if N/D->t with 0<=t<infinity, the same products
and Stirling's formula give

\[
 \frac{\log\det C_D}{D^2}\longrightarrow
 \Phi(t):=(t+1)^2\log(t+1)
  -\frac{t^2}2\log t-\frac{(t+2)^2}2\log(t+2),                \tag{16}
\]

with 0 log 0=0. This includes all fixed and linear right shifts;
it asserts no uniformity when N/D is unbounded. To see the limit,
the leading summand at k=xD is
2x log x+2(x+t)log(x+t)-2(2x+t)log(2x+t).
The log D and linear Stirling terms cancel. Its integral from 0
to 1 is Phi(t). The fixed shifts by 9,10,-1/2 cost O(D log(D+N+2));
the first O(1) small-k terms and the integrable u log u endpoint
cause no D^2 error, including t=0. Thus lower and upper products
in (13) have the same limit. In particular Phi(0)=-log4.

These are rates of the **rational real determinant**, not its reduced
numerator or primitive normalization. A rational determinant may be
small through its denominator alone. The real rate cannot be converted
to a lower bound on F_(N,D) without additional arithmetic.

## 7. The remaining bottleneck is now explicit

For N=0 the primitive positive form has error comparable to D^(-16).
Equation (10) would prove eventual failure of small primitive forms
if, for example, one established

\[
 F_{0,D}/J_{0,D}^2\ge8!K_D
\]

eventually, where K_D=8 binom(D+8,8)^2. A stronger sufficient
condition is log(F_(0,D)/J_(0,D)^2)/log D ->infinity. Neither is
proved here. Two distinct arithmetic steps remain:

1. A growth lower bound for the prime-above-2D part of the reduced
   determinant numerator F_(0,D).
2. A sufficiently small maximal-minor gcd J_(0,D), or a direct
   bound on the determinant cancellation controlled by its square.

Even proving J_(0,D)=1 for all D>=7 would settle only the second
step. The finite computations establish both large F and small J
for the stated bounded range, but they establish no eventual claim.
For M=O(D), the same two tasks apply with cutoff 2M+2D; the harmonic
anchor does not supply a surviving block of primes above that cutoff.

## 8. Exact verification

[verify_mellin_unshifted_frontier.py](../scripts/verify_mellin_unshifted_frontier.py)
uses the existing exact FLINT runtime, found through the same local
path as verify_local_connection.py; it installs nothing. The range
is fixed in the script. It checks the Hankel basis, mixed-square
increment identity, nonvanishing identity (3), rectangular maximal
minors, the adjugate identity (9), exact divisibility (10), the forced
F_p rank exceptions, rational beta products and positive comparison.
The run passed all 24 unshifted degrees D=1,...,24 and 23 additional
cases D=1,...,12 with M=1 or M=D, including the M=D=3,p=19
countercheck. Each maximal-minor gcd is computed exactly, so its
prime-above-cutoff conclusions cover every such prime for each
fixed tested parameter, rather than only a selected prime list.
The output is
[certificate.json](../verification/mellin-unshifted-frontier-2026-10-01/certificate.json).
These finite checks supplement the all-parameter written proofs;
they do not prove asymptotic denominator growth, Lean correctness,
or irrationality of zeta(9).
