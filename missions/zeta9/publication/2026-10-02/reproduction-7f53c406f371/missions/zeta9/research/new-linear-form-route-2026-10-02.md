# An isolated zeta(9) rational sum and its boundary leakage

This note studies a different, growing-complexity construction. It does
not reuse the fixed-complexity square-pole cluster obstruction. The result
is an exact rational linear form in only 1 and zeta(9), an unconditional
eventual nonzero asymptotic, and a local theorem for its full primitive
normalization. It does not prove that the primitive forms decay, or that
zeta(9) is irrational. All proofs below are written mathematical proofs;
the attached bounded exact certificate is not a Lean verification.

The starting rational function is the double-pole function appearing in
the Gutnik--Nesterenko form of the Apéry construction; see the series (8)
in [Zudilin, *Well-poised hypergeometric service for diophantine problems
of zeta values*, JTNB 15 (2003), pp. 593--626](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.415.pdf).
The seventh derivative, its endpoint asymptotic, and the local arithmetic
statement are derived explicitly here, without importing an irrationality
claim from that source.

## 1. Exact isolation

For n>=1 put

    R_n(t) = [(t-1)...(t-n) / (t(t+1)...(t+n))]^2,
    L_n = -1/8! * sum_{k=1}^infinity R_n^(7)(k).

The derivatives are O(k^-9), so this sum converges absolutely. Its partial
fraction decomposition is

    R_n(t) = sum_{j=0}^n [A_(n,j)/(t+j)^2 + B_(n,j)/(t+j)],
    A_(n,j) = binom(n,j)^2 binom(n+j,j)^2,
    B_(n,j) = 2 A_(n,j) [2 H_j - H_(n+j) - H_(n-j)].       (1)

Here H_0=0. The first identity follows by taking the value and first
derivative of (t+j)^2 R_n(t) at t=-j. Also sum_j B_(n,j)=0: the coefficient
of t^-1 vanishes because R_n(t)=O(t^-2). Seven differentiations give

    -R_n^(7)(t)/8! = sum_j [A_(n,j)/(t+j)^9
                                    + B_(n,j)/(8(t+j)^8)].

Consequently the exact identity is

    L_n = A_n zeta(9) - b_n,
    A_n = sum_j A_(n,j) in Z_(>0),
    b_n = sum_j [A_(n,j) H_j^(9) + B_(n,j) H_j^(8)/8].    (2)

The possible zeta(8) coefficient is sum_j B_(n,j)/8=0. No other zeta
value occurs. In particular no zeta(3), zeta(5), or zeta(7) contamination
has been suppressed by an unproved linear relation.

For example L_1=5 zeta(9)-9/2. The primitive form at n=1 is
10 zeta(9)-9; one finite example supplies no decay assertion.

## 2. Unconditional boundary theorem

The all-parameter asymptotic is

    L_n = (16/15) n^-4 (log n)^5 [1+O(1/log n)].          (3)

Thus L_n is strictly positive and nonzero for every sufficiently large n.
The seventh-derivative transplant has polynomial raw decay.

To prove (3), first write near t=1, with delta=t-1,

    R_n(1+delta) = delta^2 c_(n,1) exp(g_(n,1)(delta)),
    c_(n,1) = 1/[n^2(n+1)^2],  g_(n,1)(0)=0.

Taking analytic logarithms of the factors after removing delta^2 gives

    g'_(n,1)(0) = -2 H_(n-1)-2 H_(n+1) = -4 log n+O(1).

All Taylor coefficients of g of orders 2 through 5 are uniformly bounded:
each is a fixed reciprocal-power sum with power at least two. Therefore

    [delta^5] exp(g_(n,1)(delta))
        = g'_(n,1)(0)^5/5! + O((log n)^4),
    R_n^(7)(1) = 42 c_(n,1) (-4 log n)^5
                                + O(c_(n,1)(log n)^4).

Since 42*4^5/8!=16/15, this is the asserted positive contribution to L_n.
It remains to prove that every other summand is smaller.

For any 1<=k<=n the corresponding second-order zero coefficient is

    c_(n,k) = [(k-1)!^2 (n-k)! / (n+k)!]^2.              (4)

On a complex circle |t-k|=rho, rho=1/4, write
R_n(k+delta)=delta^2 c_(n,k) exp(g_(n,k)(delta)). Its logarithmic first
derivative is exactly

    g'_(n,k)(0)=4H_(k-1)-2H_(n-k)-2H_(n+k).

Uniformly in k, its absolute value is at most 4 log n+O(1). The remaining
Taylor terms are uniformly O(1) on this fixed circle, by summing the
reciprocal powers at distances at least one from their zeros and poles.
Hence, with absolute constants,

    sup_{|t-k|=rho}|R_n(t)| <= C n^(4rho) c_(n,k).

This uses the exact first-derivative cancellation; an absolute sum of its
separate numerator and denominator terms would give a weaker bound.
Moreover

    sqrt(c_(n,k+1)/c_(n,k))=k^2/[(n-k)(n+k+1)]

is increasing in k, so the maximum over 2<=k<=n is at an endpoint. Here
c_(n,2)=1/[(n-1)n(n+1)(n+2)]^2=O(n^-8), while
c_(n,n)=1/[n^4 binom(2n,n)^2]=O(n^-8); the latter follows, for example,
from binom(2n,n)>=4^n/(2n+1). Cauchy's derivative estimate now gives

    sum_{k=2}^n |R_n^(7)(k)| = O(n^-6).                  (5)

For k>=n+1 take instead |t-k|=k/4. Then Re(t)>=3k/4,
|t|<=5k/4, and j<=n<k. For each factor

    |(t-j)/(t+j)|^2
       =1-4j Re(t)/|t+j|^2 <= exp(-16j/(27k)).

It follows that sup |R_n(t)|<=C k^-2 exp(-8n(n+1)/(27k)). A second
Cauchy estimate yields

    |R_n^(7)(k)| <= C k^-9 exp(-8n(n+1)/(27k)),
    sum_{k=n+1}^infinity |R_n^(7)(k)| = O(n^-16).         (6)

For the last step, bound the sum by the integral and twice the maximum
of the nonnegative unimodal function x^-9 exp(-c n^2/x), x>0. Its integral
is C n^-16 and maximum O(n^-18). Equations (5)--(6) prove (3).

The double zeros make R_n'(k)=0 at 1<=k<=n in the zeta(3) version. They
do not make R_n^(7)(k)=0. Formula (3) identifies precisely the leakage
that a contour argument ignoring those finite summands would miss.

## 3. Safe integerization and the true primitive cost

Let d_n=lcm(1,...,n). The explicit coefficients satisfy

    d_n B_(n,j) in Z,      8 d_n^9 b_n in Z.              (7)

For completeness, fix p and e=floor(log_p(n+j)), m=floor(log_p n).
If e<=m, multiplication by d_n clears the three harmonics in (1).
Otherwise e=m+1, since n+j<=2n. The prime power q=p^e satisfies
n,j<q<=n+j, so its Legendre term in binom(n+j,j) is one. Every Legendre
term is nonnegative, whence v_p A_(n,j)>=2. The harmonic bracket has
valuation at least -e, and m+2-e>=1. This proves the first assertion for
every p, including small primes; the second follows because
den(H_j^(s)) divides d_n^s.

Set M_n=8d_n^9, G_n=gcd(M_n A_n,M_n b_n). The full primitive integer
form with positive zeta coefficient is

    P_n zeta(9)-Q_n = c_n L_n,
    c_n=M_n/G_n,
    P_n=M_n A_n/G_n,       Q_n=M_n b_n/G_n.               (8)

If b_n=u_n/v_n is reduced, the same normalization is

    c_n=v_n/gcd(A_n,u_n).                                (9)

In particular c_n can be a noninteger rational number. Replacing it by
the denominator v_n, or by the safe clearer M_n, would not analyze the
full primitive form. The exact decay criterion from (3) is

    c_n L_n -> 0  iff  c_n=o(n^4/(log n)^5).              (10)

On the other hand PNT and (3) imply

    log(M_n L_n)/n -> 9.

This only excludes the displayed safe integerization. It is not an
unconditional obstruction for (8), because G_n is not yet controlled.

## 4. A full-primitive large-prime theorem

For every prime p>=11 with n/2<p<=n, put r=n-p. Then 0<=r<p and

    A_n == 5 A_r (mod p),
    p^9 b_n is p-integral and
    p^9 b_n == (9/2) A_r (mod p).                        (11)

Here A_0=1. If p does not divide A_r, (11) gives the exact statements

    v_p(b_n)=-9,       v_p(A_n)=0,       v_p(c_n)=9.       (12)

These concern the full normalization (8), after all common content is
removed, not merely its original coefficients.

To prove (11), write j below or above p. Lucas's binomial congruence
gives A_(n,j)==A_(r,j) for 0<=j<=r, zero for r<j<p,
and A_(n,p+l)==4A_(r,l) for 0<=l<=r. These formulas remain true when
r+j>=p: the binomial binom(r+j,j) is then divisible by p. Summing proves
the first congruence. Because p>=11 and n<2p, all harmonics in (1) have
p-valuation at least -1. For j<p, its contribution to p^9 b_n vanishes
mod p. For j=p+l with A_(r,l) nonzero mod p one has r+l<p and

    p H_j ==1,       p H_(n+j)==3/2,       p H_(n-j)==0.

Thus p B_(n,j)==A_(n,j). Also p^9 H_j^(9)==1 and
p^8 H_j^(8)==1. Its contribution is 9A_(n,j)/8. Terms with
A_(r,l)==0 still contribute zero, since A_(n,j) has valuation at least
two while the harmonic bracket has valuation at least -1. Summation
gives (9/8)*4A_r=(9/2)A_r. Finally (9) proves (12).

Let E_n be the weighted exceptional-prime mass

    E_n = sum_{n/2<p<=n, p>=11, p | A_(n-p)} log p.

The negative part of c_n has denominator dividing A_n by (9), so (12)
gives the unconditional, explicit lower bound

    c_n >= exp(9[theta(n)-theta(n/2)-E_n-O(1)]) / A_n.   (13)

Elementary Stirling maximization of (1) gives

    log A_n/n -> alpha=4log(1+sqrt(2))=3.525494348...

Indeed the exponent of a summand with j/n=x has derivative
2log((1-x^2)/x^2), with its unique maximum at x=1/sqrt(2), and the sum
has at most n+1 positive summands. Consequently (13) excludes primitive
decay whenever

    limsup E_n/n < (9/2-alpha)/9 = 0.1082784057... .       (14)

Under (14), the primitive forms instead have positive lower exponential
rate at least 9/2-alpha-9 limsup E_n/n. This is a sufficient conditional
barrier, not a proved estimate on E_n. Current bounds such as
E_n<=log A_n do not imply (14). The remaining question is a definite
Apéry-residue exceptional-prime or full-content estimate, rather than
an isolation or nonvanishing gap.

## 5. Exact finite certificate and scope

`scripts/verify_new_linear_form_route.py` reconstructs the residues and
proves the complete polynomial partial-fraction identity coefficient by
coefficient for 1<=n<=24. It verifies (7)--(9), prime congruences (11)--(12),
and rigorous Arb enclosures of the primitive values. Additional selected
parameters examine the asymptotic endpoint contribution and its sign.
The certificate records exactly which finite parameters were checked;
no finite observations are promoted to an estimate on E_n or G_n.

The useful new output is (2), (3), (10), and (11)--(13). The source of
polynomial decay has been located and bounded over the entire infinite
sum. A different numerator, pole order, zero multiplicity, or summation
range would need to remove that endpoint contribution while preserving
isolation and controlling its own primitive content. The present note
does not make that further construction.
