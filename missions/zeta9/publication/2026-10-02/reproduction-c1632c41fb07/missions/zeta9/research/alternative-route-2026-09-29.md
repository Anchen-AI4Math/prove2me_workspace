# Alternative routes: positive single-zeta forms and an arithmetic obstruction

Started 2026-09-29; completed 2026-09-30. This is a separate route from the
five-column lattice and its unresolved shortest-direction condition. No
irrationality claim is made. The positive-form constructions below remove
nonvanishing as an assumption, but the tested arithmetic is insufficient.

## 1. Primary-source triage

* Fischler, [Linear independence of odd zeta values using Siegel's lemma](https://www.imo.universite-paris-saclay.fr/~stephane.fischler/siegel.pdf),
  published in JLMS 113.4 (2026), e70535; the [preprint began in 2021](https://arxiv.org/abs/2109.10136).
  The large-s lower bound is 0.21 sqrt(s/log s). Its useful methodological
  distinction is to construct several forms by Siegel's lemma, then establish
  enough rank via a multiplicity estimate, rather than estimate a chosen
  form from below. This does not establish a finite-s rank-two criterion
  restricted to 1 and zeta(9). Such a restricted family still has to be built.
  The 2026 publication date should not be described as a wholly new 2026 theorem.

* Brown, [Irrationality proofs for zeta values, moduli spaces and dinner parties](https://www.ihes.fr/~brown/IrratModuliMotivesv8.pdf),
  supplies structured cellular integrals; a generic moduli-space period has
  unwanted multiple zeta values. Positivity alone does not eliminate them.
  Brown--Zudilin's [cellular approximations to zeta(5)](https://arxiv.org/abs/2210.03391)
  illustrate this issue with simultaneous zeta(3), zeta(5) periods and effective
  zeta(5) approximations of exponent 0.86, which is below the irrationality
  threshold. These historical statements do not assess newer zeta(5) claims.

* Brown, [Mellin transforms, transfinite diameter and rational approximations of integrals](https://arxiv.org/html/2604.20741v1)
  (22 April 2026), is the most directly relevant change of mechanism.
  Positive Gram matrices give a nonzero determinant, and two-sided arithmetic
  normalization must be combined with its size. The paper's worked example
  is zeta(2), not zeta(9). Its Criterion 1.3 and Lemma 3.2 motivate the
  explicit specialization in Sections 2--4 below. The specialization and
  its obstruction are derived here; no priority claim is intended.

* Fischler--Sprang--Zudilin, [Many odd zeta values are irrational](https://www.imo.universite-paris-saclay.fr/~stephane.fischler/zeta.pdf)
  (Compositio 155 (2019)), uses rational shifts and divisor profiles d^s.
  Their standard family requires s>3D. At s=9 this permits only D=1,2,
  with at most two divisor profiles, insufficient to eliminate three
  independently present coefficients of zeta(3), zeta(5), zeta(7).
  Section 6 makes this obstruction exact. It excludes that direct transplant,
  not all rational-shift constructions.

## 2. An arbitrary sparse-exponent positive matrix containing only zeta(9)

Set H_k=sum_{j=1}^k j^(-9), H_0=0, and

    w(x)=(-log x)^8 / [8! (1-x)],        0<x<1.

Termwise integration of the nonnegative geometric series gives

    integral_0^1 x^k w(x) dx = zeta(9)-H_k.                 (1)

For any distinct nonnegative integers E={e_0,...,e_(m-1)}, define

    G_E(X)_(i,j)=X-H_(e_i+e_j).

At X=zeta(9), this is the Gram matrix of the independent monomials x^e_i
for a strictly positive weight. Thus it is positive definite. Its X
coefficient is the rank-one matrix of all ones. Consequently det G_E(X)
has degree at most one. The following calculation proves its degree is
exactly one and its leading coefficient is positive, for every E.

Subtract the first row from all other rows, and then the first column from
all other columns. With h=H_(2e_0), the resulting matrix is

    [ X-h    b^T ] ,    b_i=h-H_(e_0+e_i),
    [  b      C  ]

    C_ij=-H_(e_i+e_j)+H_(e_i+e_0)+H_(e_j+e_0)-h.

C is the Gram matrix of x^e_i-x^e_0, i>0, hence is positive definite.
The Schur formula yields

    det G_E(X)=det(C) (X-q_E),
    q_E=h+b^T C^(-1)b in Q,         det(C)>0.              (2)

For m=1 use det C=1 and q_E=H_(2e_0). Write q_E=Q/P in lowest terms,
P>0. Dividing the integer polynomial obtained from (2) by its full
content gives precisely

    P X-Q,                  P zeta(9)-Q>0.                (3)

This establishes nonvanishing for arbitrary moving exponent sets as well
as fixed ones. No conjecture about zeta(9), no old direction condition,
and no numerical sign check are used. The unnormalized determinant can
be far smaller than the primitive integer value in (3).

There is also an exact variational identity. In the space spanned by
the monomials x^e, write p=x^e_0+sum c_i(x^e_i-x^e_0). These are precisely
the polynomials in that space satisfying p(1)=1. Completing the square gives

    zeta(9)-q_E = min_{p in span(E), p(1)=1} integral p(x)^2 w(x) dx. (4)

For nested consecutive exponent sets, (4) proves q_E increases strictly
or weakly and stays below zeta(9). Taking the trial p=x^D proves convergence
to zeta(9), since its integral is zeta(9)-H_(2D), which tends to zero.
Only weak monotonicity is needed or asserted here.

## 3. A universal height obstruction, including every sparse pattern

Let D=max E. Since -log x >= 1-x,

    w(x) >= (1-x)^7/8!.

The exact endpoint Christoffel constant for degree at most D is

    K_D=sum_{k=0}^D (2k+8) binom(k+7,7)^2
       =(D+8)^2 binom(D+7,7)^2 / 8.                       (5)

For completeness, no special-function theorem is needed. Rodrigues'
polynomials

    J_k(x)=(-1)^k/(k!(1-x)^7) d^k/dx^k [x^k(1-x)^(k+7)]

are polynomials of degree k. Integration by parts k times proves
orthogonality to smaller degrees for the weight (1-x)^7; boundary terms
vanish. Their leading coefficients are binom(2k+7,k), their values at 1
are binom(k+7,7), and the beta integral gives squared norm 1/(2k+8).
Expanding p in this orthogonal basis and applying Cauchy--Schwarz to p(1)
therefore proves

    integral_0^1 p(x)^2(1-x)^7 dx >= 1/K_D,   if p(1)=1.

Equality occurs at the normalized reproducing kernel. The closed form
in (5) follows by taking successive differences and checking D=0.
Combining this with (4) proves the all-parameter bound

    P zeta(9)-Q >= P/(8! K_D).                            (6)

In particular, a member of this family can have primitive integer value
less than 1 only if

    P < 8! K_D = O(D^16).                                 (7)

This is a useful obstruction and a concrete future target: denominators
growing exponentially in D cannot produce small primitive forms through
this particular monomial Gram construction. It is not a theorem that all
possible E have such denominator growth. Arithmetic modifications that
preserve positivity, or a different period weight, are still possible.

## 4. Exact finite experiment: the denominator is decisive

The companion script computes q_E over Q by the Schur formula, reduces
it to coprime P,Q, independently expands three small symbolic determinants,
and checks (5) and seven Rodrigues norms. It covers exactly 22 exponent
sets: ten consecutive sets of sizes 1--10, plus twelve listed sparse or
translated sets. It does not search until a favorable example appears.

For numerical display only, it encloses zeta(9) using a rational
Euler--Maclaurin sum with M=120 and K=80, bounding the periodic-Bernoulli
remainder by the absolute value of the last retained correction. All
displayed primitive-value intervals have rational endpoints.

| E | digits of P | primitive integer value P zeta(9)-Q |
|---|---:|---:|
| {0,1} | 3 | 0.02628873412801156752... |
| {0,1,2} | 13 | 734854.6039358875... |
| {0,1,2,3} | 34 | 6.0970551124978 * 10^25 |
| {0,...,9} | 359 | 2.2739342933690 * 10^345 |

The first line is exactly 511 zeta(9)-512. Every tested set with at least
three elements satisfies the exact integer comparison P>=8!K_D, so (6)
alone proves its primitive value is at least 1. This failure conclusion
does not depend on numerical evaluation of zeta(9).

The singleton E={0} gives zeta(9)>1. Thus only one of the 22 test cases
has primitive value below 1; one isolated small value proves no
irrationality statement. Rapid decay of raw Gram determinants would not
change this conclusion.

## 5. Completely monotone derivative family: positivity and a full baseline obstruction

Here is a second direct construction, useful for separating the analytic
and arithmetic issues. For distinct nonnegative integer poles a_j put

    R(t)=product_j (t+a_j)^(-2),
    L=-1/8! sum_{t=1}^infty R^(7)(t).

Each factor is strictly completely monotone and Leibniz' rule shows
(-1)^7 R^(7)(t)>0. Thus L>0. Write its partial fractions as

    R(t)=sum_j [A_j/(t+a_j)^2+B_j/(t+a_j)],
    A_j=product_{k!=j}(a_k-a_j)^(-2)>0,
    B_j=-2 A_j sum_{k!=j}(a_k-a_j)^(-1).

The coefficient of t^(-1) at infinity vanishes, so sum B_j=0.
Differentiating seven times and summing yields exactly

    L=(sum A_j) zeta(9)
      -sum_j [A_j H_(a_j)^(9)+(B_j/8) H_(a_j)^(8)] >0.    (8)

No zeta(8) remains. A tail beginning at t=M+1 merely replaces each
harmonic index a_j by M+a_j. The script checks four different pole patterns
by exact partial-fraction identities. This is an elementary specialization,
not a claim to have invented derivative-based zeta approximations.

For the consecutive family normalize

    R_n(t)=(n!)^2/product_{j=0}^n(t+j)^2,
    L_(n,M)=-1/8! sum_{t=M+1}^infty R_n^(7)(t).

Then A_j=binom(n,j)^2, while
B_j=2 A_j(H_j^(1)-H_(n-j)^(1)). Hence the standard multiplier

    8 d_(M+n)^9 L_(n,M) in Z+Z zeta(9),                  (9)

where d_k=lcm(1,...,k), is valid. It need not be primitive.
For M=floor(rho n), any fixed rho>=0, the exact exponential rate is

    lim log L_(n,M)/n
       =2[rho log rho-(rho+1)log(rho+1)],                 (10)

with 0 log 0=0. Here is a direct justification, including rho=0.
Write T=M+1. If h_7 is the complete homogeneous polynomial of the 2n+2
reciprocals 1/(t+j), each repeated twice, then

    -R_n^(7)(t)/8! = R_n(t) h_7/8.

At t=T it is at least R_n(T)/T^7. For all t>=T it is at most
R_n(t)[2(n+1)/T]^7/8. Also

    sum_{t=T}^infty R_n(t)
      <=R_n(T)[1+(T+n)/(2n+1)],

because R_n(t)/R_n(T)<=((T+n)/(t+n))^(2n+2), followed by
the integral test. Both bounds differ from R_n(T) by at most polynomial
factors. Stirling's formula for R_n(T) gives (10); for rho=0,
R_n(1)=1/(n+1)^2 gives the same conclusion without Stirling at zero.

The prime number theorem applied to (9) now gives the rate

    F(rho)=9(rho+1)+2rho log rho-2(rho+1)log(rho+1).

Its unique minimum is attained at rho=1/(exp(9/2)-1), and equals

    min F=9+2 log(1-exp(-9/2)) >8.97.                    (11)

Thus this standard clearing scheme grows exponentially for **every**
linear tail cut, despite automatic nonvanishing. Equation (11) does not
exclude a substantially better primitive denominator or other pole
patterns; it rules out the stated normalization, uniformly in rho.

## 6. Exact divisor-elimination obstruction at weight nine

In the FSZ standard construction, shift aggregation at d|D produces
coefficient profile d^s for zeta(s). For up to three distinct positive
nodes d, the rows d^3,d^5,d^7 have full column rank: divide each column
by d^3 and use Vandermonde nodes d^2. Hence a nonzero combination
annihilating all three profiles requires at least four divisor nodes.
The smallest D with four divisors is 6.

For illustration, nodes (1,2,3,6) have the primitive kernel vector

    (-7776,1701,-224,1).

Its profiles at s=3,5,7 are exactly zero, while at s=1 and s=9 they
are -5040 and 6531840, respectively. Therefore the linear algebra is
perfectly suitable for preserving zeta(9) and a nonzero asymptotic profile.

The obstruction lies before asymptotics: FSZ's numerator has degree
3Dn+1, denominator degree (s+1)(n+1). At D=6, s=9, their difference
is 8n-9, so the defining series fails to converge for every n>=1
(degree -1 already diverges at n=1). Cancelling common factors does
not change this degree difference. Their stated s>3D condition already
excludes D=6. A successful rational-shift route to individual zeta(9)
therefore needs a different root/pole design or additional intrinsic
vanishing; importing the standard family cannot suffice.

## 7. Outcome and verification boundary

The substantive new work in this note is the exact sparse-monomial
specialization, its universally positive primitive linear form, and
the height obstruction (6). It supplies a genuinely different, explicit
nonzero mechanism rather than another estimate for the old lattice.
The finite experiment fails for an identified arithmetic reason. The
completely monotone family and the divisor-profile argument give two
additional all-parameter diagnostics.

Reproduce with the already installed Python 3.12 plus SymPy (PowerShell):

    & 'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe' scripts/verify_alternative_route.py

The default `python` here resolves to Python 3.14 without SymPy; no package
installation was performed.

Outputs: `verification/alternative-route-2026-09-29/certificate.json`.
All current exact checks pass. The theorem proofs are written arguments;
the finite Rodrigues checks do not substitute for their all-degree proof.
Independent mathematical review by `local_plane` passed Sections 2--5,
including the primitive normalization, the all-degree Christoffel bound,
the completely monotone estimates, and the Euler--Maclaurin remainder
interface; see [the review, Section 8](zenodo-route-audit-2026-09-29.md#8-cross-review-of-the-alternative-route-note).
That reviewer did not independently rerun the 22 cases. Separately, the
root agent reran the complete script with the stated Python 3.12 interpreter
and obtained PASS. No Lean or external publication was performed. This
agent did not edit status or scope; the root agent subsequently registered
the new sources and certificate path.
