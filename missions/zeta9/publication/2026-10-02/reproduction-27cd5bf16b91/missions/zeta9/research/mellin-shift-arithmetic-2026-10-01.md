# Mellin right shifts: an all-parameter arithmetic obstruction

2026-10-01. This note concerns the positive Mellin construction in
[the alternative route, Sections 2--3](alternative-route-2026-09-29.md),
with the error estimates of
[the sharp-error note](mellin-sharp-error-2026-09-30.md).
All proofs below are written proofs. No Lean result or irrationality of
zeta(9) is claimed.

The main conclusion is that a sufficiently large right shift cannot repair
the primitive denominator: if

\[
 M\longrightarrow\infty,\qquad
 D^2\log(2+M/D)=o(M),\quad D\ge1,
\]

then both the denominator and the positive primitive form have exact
exponential rate 18 per unit M. This includes every fixed D. The remaining
regimes, including bounded or linear shifts as D grows, are not excluded
by this theorem.

## 1. Exact arithmetic reduction

Put N=2M and E={M,M+1,...,M+D}, with M>=0 and D>=1 integers.
Write H_n=sum_(j=1)^n j^(-9), h=H_N, and q=q_(M,D)=h+r. From the
Schur reduction, with indices 1<=i,j<=D,

\[
 b_i=H_N-H_{N+i},\qquad
 C_{ij}=H_{N+i}+H_{N+j}-H_{N+i+j}-H_N,
 \qquad r=b^tC^{-1}b>0.                         \tag{1}
\]

C is positive definite: it is the Gram matrix of x^M(x^i-1) for the
strictly positive Mellin weight. Define

\[
 \ell=\operatorname{lcm}(N+1,\ldots,N+2D),\quad
 L=\ell^9,\quad A=LC,\quad v=Lb.
\]

All entries of A,v are integers, A is positive definite, and det A is
a positive integer. Therefore

\[
 r=\frac{v^t\operatorname{adj}(A)v}{L\det A},
 \qquad R:=\operatorname{den}(r)\mid L\det A.
                                                               \tag{2}
\]

Here den is the positive reduced denominator, including den(0)=1.
The numerator in (2) is integral; no upper bound on that numerator is
needed. Let T=den(H_N) and P=den(q). The elementary denominator
stability lemma gives

\[
 T/R\le P\le TR,\qquad
 |\log P-\log T|\le\log R.                    \tag{3}
\]

Indeed den(x+y) divides den(x)den(y), and den(x) divides
den(x+y)den(y), by applying the same fact to x=(x+y)-y. Both statements
hold without any numerator-height restriction.

## 2. A short-interval lcm lemma

For every integer N>=0 and t>=1, with d_t=lcm(1,...,t),

\[
 \boxed{\operatorname{lcm}(N+1,\ldots,N+t)
       \mid\binom{N+t}{t}d_t.}                 \tag{4}
\]

Proof. Fix a prime p. Let k be the largest exponent for which some
integer in the interval is divisible by p^k, and put a_0=floor(log_p t).
If k<=a_0, d_t already supplies the required p-power. Otherwise, for
every a_0<a<=k the interval contains a multiple of p^a, while p^a>t,
so the interval contains exactly one such multiple. The corresponding
term in Legendre's formula for the binomial valuation is

\[
 \left\lfloor\frac{N+t}{p^a}\right\rfloor
 -\left\lfloor\frac{N}{p^a}\right\rfloor
 -\left\lfloor\frac{t}{p^a}\right\rfloor=1.
\]

The terms at other a are nonnegative. Thus the binomial supplies at
least k-a_0 further powers, proving (4) prime by prime.

In particular, with psi(t)=log d_t and the usual binomial estimate,

\[
 \log\ell\le \log\binom{N+2D}{2D}+\psi(2D)
 \le 2D\log\bigl(e(1+M/D)\bigr)+\psi(2D).       \tag{5}
\]

The estimate binom(n,t)<= (en/t)^t follows from t!>=(t/e)^t;
it is only an upper bound, whereas (4) is an integer divisibility.

## 3. Three explicit determinant bounds

The entries in (1) can also be written

\[
 C_{ij}=\sum_{k=1}^{\min(i,j)}
  \left[(N+k)^{-9}-(N+\max(i,j)+k)^{-9}\right].
                                                               \tag{6}
\]

Consequently C_ii<=i/(N+1)^9. The integral identity
t^(-9)-(t+i)^(-9)=9 integral_t^(t+i) u^(-10)du also gives
C_ii<=9i^2/(N+1)^10. Hadamard's inequality for positive Gram matrices
now gives the exact all-parameter bound

\[
 \det C\le B_{N,D}^{(0)}:=
 \min\left\{\frac{D!}{(N+1)^{9D}},
       \frac{9^D(D!)^2}{(N+1)^{10D}}\right\}.    \tag{7}
\]

If N>=4 (M>=2), a stronger optional bound uses the weight inequality
w(x)<=x^(-4)(1-x)^7/8!. Make the determinant-one integer basis change
x^M(x^i-1) -> x^M(x-1)x^(i-1), i=1,...,D. In the new basis the
actual Gram matrix is at most 1/8! times the positive beta Gram matrix

\[
 G_{kl}=\int_0^1x^{N-4+k+l}(1-x)^9dx
       =\operatorname{Beta}(N-3+k+l,10),\quad 0\le k,l<D.
\]

For positive definite matrices B<=G/8!, conjugating by G^(-1/2)
shows every eigenvalue is at most 1/8!, hence det B<=det G/(8!)^D.
The monic Jacobi squared norms, or their Rodrigues derivation, yield

\[
 B_{N,D}^{(1)}=\frac1{(8!)^D}
 \prod_{k=0}^{D-1}
 \frac{k!(k+9)!(k+N-4)!(k+N+5)!}
 {(2k+N+5)!(2k+N+6)!},\qquad
 \det C\le B_{N,D}^{(1)}.                       \tag{8}
\]

For clarity, for weight x^b(1-x)^9 the Rodrigues polynomial has
leading coefficient binom(2k+b+9,k) and squared norm
(k+9)!(k+b)!/[(2k+b+10)k!(k+b+9)!]. Dividing by the square of
its leading coefficient gives the kth factor in (8), with b=N-4.
Orthogonality makes the monomial Gram determinant the product of these
monic norms. This proves the formula at all degrees, separately from
its finite computational checks.

A simpler consequence of (8), useful for seeing the scale, is

\[
 B_{N,D}^{(1)}\le
 \frac{\prod_{k=0}^{D-1}k!(k+9)!}
 {(8!)^D(N-3)^{D^2+9D}}.                       \tag{9}
\]

In each kth factorial ratio, the two denominator strings together
have 2k+10 factors, all at least N-3; summing gives D^2+9D.

Define B_(N,D) to be (7) for N<4 and the minimum of (7),(8) for N>=4.
Combining (2) with det A=L^D det C proves the finite, fully explicit
bound

\[
 \boxed{R\le U_{M,D}:=\ell^{9(D+1)}B_{N,D}.}    \tag{10}
\]

Every quantity on the right is rational and can be checked exactly.
It is necessarily at least 1, since it bounds the positive integer R.
Substituting binom(N+2D,2D)d_(2D) for ell gives a possibly larger,
likewise explicit bound.

For M>=1 every prime M<p<=2M occurs just once as a p-multiple in H_N,
and p^2>N. Multiplying H_N by p^9 leaves a p-adic unit. Thus

\[
 B_M:=\prod_{M<p\le2M}p^9\mid T,
 \qquad P\ge\frac{T}{U_{M,D}}\ge\frac{B_M}{U_{M,D}}.             \tag{11}
\]

The lower bounds in (11) need not be integral. They are valid inequalities
for every parameter, with no asymptotic or finite-prime exception.

## 4. The large-shift theorem

The only prime-distribution input is the prime number theorem in the form
psi(n)=n+o(n). It implies psi(2D)=O(D), uniformly for integer D>=1.
Equations (5),(7),(10), with the negative determinant terms discarded,
give

\[
 \log R=O\left(D^2\log(2+M/D)\right).           \tag{12}
\]

For a simple uniform way to discard the determinant term, each
C_ii<sum_(j=1)^infty j^(-9)<2, so det C<2^D and discarding its
logarithm costs at most D log 2. More sharply (7) may be retained.
Either gives (12), including small M. When M>=D,
log(2+M/D)=O(log(1+M/D)), which gives the requested
O(D^2 log((M+D)/D)) right-shift cost.

The generic harmonic-denominator theorem proved in
[harmonic denominator stability](harmonic-denominator-stability-2026-10-01.md)
says log den(H_N^(s))/N -> s for each fixed positive integer s. Its
lower-bound proof retains primes epsilon N<p<=N outside the finite
numerator-prime set of H_j^(s), j<=1/epsilon; its upper bound is
den(H_N^(s))|d_N^s. Thus it uses the same PNT input and no assumption
about zeta(9).

Assume now M->infinity and D>=1 varies with M so that

\[
 D^2\log(2+M/D)=o(M).                           \tag{13}
\]

Then (12) and (3), with s=9 and N=2M, give

\[
 \boxed{\frac{\log P_{M,D}}{M}\longrightarrow18.}               \tag{14}
\]

This is a two-sided limit, not merely an exponential lower bound from
the primes in (M,2M]. The condition (13) implies D=o(M), since
log(2+M/D)>=log 2 and D^2=o(M).

Let epsilon=zeta(9)-q>0 and Lambda=P epsilon, the primitive positive
integer form. The previously proved variational lower bound and trial
p=x^M give, for M>=1,

\[
 \frac{5040}{\prod_{j=1}^{8}(D+j)\prod_{j=1}^{8}(D+N+j)}
 \le\epsilon\le\zeta(9)-H_N\le\frac1{8N^8}.                   \tag{15}
\]

Since D=o(M), both logarithms in (15) are O(log M), so
log epsilon=o(M). Therefore

\[
 \boxed{\frac{\log(P_{M,D}\zeta(9)-Q_{M,D})}{M}
        \longrightarrow18.}                                \tag{16}
\]

These primitive values tend to infinity exponentially. Hence this
parameter regime cannot satisfy the small-nonzero-integer-form
criterion. Every fixed D>=1 is included, as are moving examples
D=floor(M^alpha) for every fixed 0<alpha<1/2. For D=0 the Schur
correction vanishes; the harmonic theorem and the tail bound give
the same rates directly.

Before taking any limit, (11) and (15) already give the exact
all-parameter inequality, for M>=1 and D>=1,

\[
 P\zeta(9)-Q\ge
 \frac{5040B_M}
 {U_{M,D}\prod_{j=1}^{8}(D+j)\prod_{j=1}^{8}(D+2M+j)}.         \tag{16a}
\]

## 5. A boundary-scale extension

The beta determinant improves the range of the obstruction beyond (13).
Suppose D->infinity and

\[
 \frac{M}{D^2\log D}\longrightarrow c,
 \qquad 17/18<c<\infty.                        \tag{17}
\]

Then the finite bounds (5),(9),(10) give

\[
 \log R\le (17+o(1))D^2\log D.                 \tag{18}
\]

Here are explicit uniform estimates to justify moving D. From (17),

\[
 \log(1+M/D)=\log D+\log\log D+O(1),\qquad
 \log(N-3)=2\log D+\log\log D+O(1).
\]

Also psi(2D)=O(D), and without any fixed-D asymptotic,

\[
 \log\prod_{k=0}^{D-1}k!(k+9)!
 \le (D^2+8D)\log(D+8)
 =D^2\log D+O(D\log D).
\]

Substituting these all-parameter inequalities in (9),(10) gives

\[
 \log R\le
 17D^2\log D+17D^2\log\log D+O(D^2+D\log D).
\]

Both displayed remainders are o(D^2 log D); no asymptotic valid only
for fixed D has been used. The harmonic theorem gives
log T=(18c+o(1))D^2 log D. Consequently (3),(15) imply

\[
 \liminf\frac{\log P}{M}\ge18-17/c>0,\qquad
 \liminf\frac{\log(P\zeta(9)-Q)}{M}\ge18-17/c>0.               \tag{19}
\]

Thus these boundary-scale primitive values also grow exponentially.
This is a lower-rate result, not the exact rate 18 from (14),(16).
For instance M=floor(D^2 log D) gives a lower rate of 1 in (19).
If the ratio in (17) instead tends to infinity, then (13) holds and
the exact rate 18 applies: writing M=c_D D^2 log D with c_D->infinity,
the ratio in (13) is bounded by a constant times
1/c_D+(log c_D)/(c_D log D), which tends to zero.

## 6. Sparse sets: dimension and width enter separately

Let E={M,M+a_1,...,M+a_d}, where 1<=a_1<...<a_d=W and d>=1.
Set ell=lcm(N+1,...,N+2W), L=ell^9, and use (1) with i,j replaced
by a_i,a_j. The same proofs give

\[
 \operatorname{den}(q_E-H_N)
 \le\ell^{9(d+1)}
 \min\left\{\frac{\prod_i a_i}{(N+1)^{9d}},
            \frac{9^d\prod_i a_i^2}{(N+1)^{10d}}\right\},       \tag{20}
\]

and consequently

\[
 \log\operatorname{den}(q_E-H_N)
 =O\left((d+1)W\log(2+M/W)\right).             \tag{21}
\]

To justify (21) for all parameter sizes one can use each C_ii<2 and
(4) with t=2W. Retaining (20) sharpens the finite bound. If M->infinity
and

\[
 (d+1)W\log(2+M/W)=o(M),                       \tag{22}
\]

then W=o(M); harmonic-denominator stability yields log den(q_E)/M->18.
The lower bound in (15) remains valid with D=W, because the sparse
space is contained in x^M R[x]_(<=W). The trial x^M gives the same
upper bound. Hence the primitive positive form also has rate 18.
For M>=W one may replace log(2+M/W) by log(1+M/W).

This is a wider obstruction than the consecutive theorem: a sparse
window pays its dimension d separately from its width W. It does not
assert an obstruction when (22) fails.

## 7. Exact verification and boundaries

Run the standalone standard-library verifier:

    python scripts/verify_mellin_shift_arithmetic.py

It checks short-interval lcm divisibilities and their prime-valuation
proof terms, exact Schur reductions, denominator divisibility (2),
denominator stability (3), both diagonal bounds (7), the beta determinant
formula and positive matrix comparison in (8), finite prime bounds (11),
and sparse analogues (20). The certificate is
[verification/mellin-shift-arithmetic-2026-10-01/certificate.json](../verification/mellin-shift-arithmetic-2026-10-01/certificate.json).
The limit theorems are consequences of the written all-parameter
arguments and PNT, not of those finite checks. No Lean build, external
submission, or general zeta(9) irrationality conclusion is part of this note.
