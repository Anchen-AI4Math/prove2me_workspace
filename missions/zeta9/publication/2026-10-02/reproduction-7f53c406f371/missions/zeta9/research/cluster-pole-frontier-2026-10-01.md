# Fixed-complexity narrow square-pole clusters have exact primitive growth

2026-10-01. This extends the positive square-pole construction of
[modified-poles-2026-09-30.md](modified-poles-2026-09-30.md).
It is separate from the unshifted Mellin arithmetic frontier.
The proofs are written arguments, not Lean-checked results.

## 1. The theorem and its scope

Fix positive integers h,m and a nonnegative integer u. Let
A={a_1<...<a_m=b} be positive integer poles with b->infinity, and let
S be a nonzero integer polynomial of degree at most u, nonnegative
on [0,infinity). Both A and S may vary. Write

\[
 W=b-a_1,\qquad H=\max_e|[t^e]S|\ge1,
 \qquad W=o(b),\quad\log H=o(b).                \tag{1}
\]

The original proposed condition W log b=o(b) is sufficient but is
stronger than necessary. The short-interval lcm lemma permits (1).
No fixed offsets, consecutive poles, monicity, or prescribed rank
pattern are required. Factors of S that cancel poles may be retained
or removed; the actual determinant degree below is what matters.

Let D_A(t)=prod_(a in A)(t+a^2), and define

\[
 G_A(X)_{ij}=\mu_{9,X}\!\left(\frac{S(t)t^{i+j}}{D_A(t)}\right),
 \quad0\le i,j<h,\qquad\Delta_A(X)=\det G_A(X).
\]

The moment functional, including its polynomial quotient terms, is
the one defined in the cited square-pole notes. At X=zeta(9), G_A is
the positive Gram matrix for S(y^2)w_9(y)/D_A(y^2). Thus Delta_A is
nonzero and its value there is strictly positive. Let d_A=deg Delta_A,
0<=d_A<=h, and let

\[
 \mathcal P_A(X)=c_A\Delta_A(X)\in\mathbb Z[X],\qquad c_A>0,
\]

be its primitive integer polynomial. Then, uniformly along every
sequence satisfying (1),

\[
 \boxed{\frac{\log\mathcal P_A(\zeta(9))}{b}-9d_A\longrightarrow0.}
                                                               \tag{2}
\]

In particular, on every fixed-degree subsequence d_A=d>=1 the exact
growth rate is 9d. Any sequence of nonconstant determinants has
liminf log mathcal P_A(zeta(9))/b>=9, so it cannot yield small
primitive forms. If d_A=0, the primitive polynomial is exactly 1.
This excludes the fixed-complexity, subexponential-numerator-height,
asymptotically narrow-cluster regime. It does not exclude growing
h,m,u, exponential numerator height, or clusters with W comparable
to b.

## 2. Centering at one harmonic number

Put a=a_1 and H_a^(9)=sum_(v=1)^a v^(-9). Polynomial division gives

\[
 G_A(X)=R_A+(X-H_a^{(9)})B_A.                   \tag{3}
\]

If k=i+j and Q_k is the complete polynomial quotient of S(t)t^k by
D_A(t), its constant part at this center is

\[
 (R_A)_{ij}=\mu_9(Q_k)+
 \sum_{c\in A}\frac{S(-c^2)(-c^2)^k}{D_A'(-c^2)}
 \left[-c^8(H_c^{(9)}-H_a^{(9)})-\frac18+\frac1{2c}\right].    \tag{4}
\]

The X coefficient is

\[
 (B_A)_{ij}=\sum_{c\in A}\frac{S(-c^2)(-c^2)^{k+4}}{D_A'(-c^2)}.
\]

It is an integer: this sum is the t^(m-1) coefficient of the remainder
of S(t)t^(k+4) modulo the monic integer polynomial D_A(t), by Lagrange
interpolation. This remains true when the numerator degree exceeds m;
one must take the full remainder.

## 3. An explicit common clearer and coefficient-height bound

Let k_0=u+2h-2, let K be the lcm of the reduced denominators of the
fixed rational moments mu_9(t^e), 0<=e<=k_0, and put

\[
 V_A=\prod_{i<j}(a_j^2-a_i^2),\qquad
 \ell=\operatorname{lcm}(a+1,\ldots,b),\qquad
 L=8K V_A\left(\prod_i a_i\right)\ell^9.        \tag{5}
\]

For W=0 define ell=1. Since abs D_A'(-a_i^2) divides V_A, the
harmonic tails have denominator dividing ell^9, and every quotient
coefficient is integral, L R_A and L B_A are integer matrices.
The factors 8 prod a_i clear both -1/8 and 1/(2a_i).

The [short-interval lcm lemma](mellin-shift-arithmetic-2026-10-01.md#2-a-short-interval-lcm-lemma)
gives ell|binom(b,W)d_W for W>=1, where d_W=lcm(1,...,W). Hence

\[
 \log L\le 9\log\binom bW+9\psi(W)+m^2\log b+O_{h,u}(1)
 \le9W\log(eb/W)+9\psi(W)+m^2\log b+O_{h,u}(1).               \tag{6}
\]

Here psi(W)=log d_W=O(W) by PNT; W=0 contributes zero. Because
x log(1/x)->0 at x=0, (1) implies log L=o(b).

For completeness the entry-height bound is also quantitative. Let
M_0=max(1,abs mu_9(t^e):0<=e<=k_0) and set

\[
 C_0=(u+1)\left[(k_0+1)\binom{m+k_0}{k_0}M_0+2m+1\right],
 \qquad E=2k_0+9=2u+4h+5.
\]

For b>=1,

\[
 \max_{i,j}(|(R_A)_{ij}|,|(B_A)_{ij}|)\le C_0 H b^E.         \tag{7}
\]

Indeed division of t^n by D_A has quotient coefficients bounded by
binom(m+k_0,k_0)b^(2k_0): they are signed complete homogeneous
polynomials in a_i^2. At most u+1 such divisions combine for S t^k.
For each residue abs D_A'(-c^2)>=1, so its numerator is bounded by
(u+1)H b^(2k_0). The bracket in (4) is bounded by 2b^9, using
H_c-H_a<=W<=b. These bounds prove (7), including every Bernoulli
quotient term.

Write the centered determinant as

\[
 F_A(Y)=\det(R_A+YB_A)=L^{-h}\sum_{j=0}^{d_A}A_jY^j,
 \qquad A_j\in\mathbb Z,\quad A_{d_A}\ne0.
\]

Expanding its h! permutation terms and the choices of j factors
from B gives the finite bound

\[
 |A_j|\le h!\binom hj(C_0 L H b^E)^h.           \tag{8}
\]

Consequently log abs A_(d_A)=o(b), uniformly even if the degree varies.
No explicit formula or full-rank assertion for B is needed.

## 4. A translation-normalization lemma

Put T=den(H_a^(9)) and let T_small be its part supported on primes
p<=sqrt a. Since T divides d_a^9,

\[
 \log T_{\rm small}\le9\pi(\sqrt a)\log a
 \le9\sqrt a\log a=o(b).                       \tag{9}
\]

High powers of small primes are included in (9); replacing this bound
by 9 psi(sqrt a) would be unjustified. Suppose d=d_A>=1, write
Z=L abs A_d, and call a prime good if p>sqrt a, p|T, p does not
divide Z. Its denominator valuation e=v_p(T) is positive and at most
9. Every coefficient of F is p-integral and its leading coefficient
is a p-unit. Thus in

\[
 \Delta_A(0)=F_A(-H_a^{(9)}),
\]

the top term has valuation -de and every other term has strictly
larger valuation. More generally the X^i coefficient of
F_A(X-H_a^(9)) has valuation at least -(d-i)e. Its constant coefficient
therefore has the unique least valuation, so primitive integerization
forces

\[
 v_p(c_A)=de\quad\hbox{at every good prime}.     \tag{10}
\]

The part of T supported on bad primes greater than sqrt a divides
Z^9. Also den(c_A) divides abs A_d, since c_A A_d/L^h is integral
and c_A is reduced. We obtain the entirely finite inequalities

\[
 \frac{T^d}{|A_d|\,T_{\rm small}^d Z^{9d}}
 \le c_A\le L^hT^d.                            \tag{11}
\]

For the upper bound L^h T^d Delta_A has integer coefficients, so its
ratio to the primitive scalar c_A is a positive integer. Equations
(6),(8),(9),(11) now imply

\[
 \log c_A=d_A\log T+o(b).                      \tag{12}
\]

The same conclusion holds at d=0 directly: c_A=L^h/abs A_0, and
its logarithm has size o(b). All errors are uniform for 0<=d_A<=h.
The [harmonic-denominator theorem](harmonic-denominator-stability-2026-10-01.md)
gives log T/a->9. Since a=b-W~b, (12) yields

\[
 \frac{\log c_A}{b}-9d_A\longrightarrow0.       \tag{13}
\]

The PNT enters through that harmonic theorem and the short-lcm estimate;
no irrationality assumption or numerator-height bound on H_a is used.

## 5. The real Gram value contributes only o(b)

Normalize S by H. The coefficient vectors of degree-at-most-u
polynomials nonnegative on [0,infinity), with maximum coefficient
absolute value 1, form a compact set that excludes the zero polynomial.
For each such polynomial and each unit coefficient vector p of degree
at most h-1,

\[
 \int_1^2p(y^2)^2(S/H)(y^2)w_9(y)dy>0.
\]

Continuity and compactness give a uniform positive minimum gamma.
On this interval D_A(y^2)<=(b^2+4)^m. This gives a uniform Gram
lower bound. For the upper bound use D_A(y^2)>=a^(2m),
abs S(y^2)<=H sum_(e=0)^u y^(2e), and the fixed finite moments of
w_9. Thus constants C_-,C_+>0 depending only on h,m,u satisfy

\[
 C_-H^h(b^2+4)^{-mh}\le\Delta_A(\zeta(9))
 \le C_+H^ha^{-2mh}.                           \tag{14}
\]

Since a~b and log H=o(b), log Delta_A(zeta(9))=o(b). Combining
this with (13) proves (2). At d=0 the positive rational constant
has primitive integer polynomial 1, as stated.

## 6. Verification boundary

The small exact checker
[verify_cluster_pole_frontier.py](../scripts/verify_cluster_pole_frontier.py)
constructs complete quotient and residue moments for predefined
nonconsecutive clusters, several nonnegative integer numerators,
full-rank, low-rank and degree-zero cases. It verifies the entry
clearer, coefficient-height bounds, primitive scalar, both bounds in
(11), good-prime valuations and positive Arb evaluations. The certificate
is [certificate.json](../verification/cluster-pole-frontier-2026-10-01/certificate.json).
The theorem's quantified conclusion comes from the written arguments,
PNT and compact positivity, not from the bounded checker.
No Lean build, external submission, or zeta(9) irrationality claim is made.
