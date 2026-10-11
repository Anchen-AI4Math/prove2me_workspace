Let $m$ be a nonnegative integer, and write
$$
D_m(z)=\prod_{k=0}^{m}(z+k),\qquad
C_{m,j}(z)=\prod_{\substack{0\le k\le m\\k\ne j}}(z+k).
$$
For $0\le j\le m$ and $1\le s\le9$, define the rational coefficient
$$
c_{m,j,s}(A)=[X^{9-s}]\,
\frac{A(X-j)}{C_{m,j}(X-j)^9}
$$
using the formal power series at $X=0$. The denominator has nonzero constant coefficient, so this formal inverse is defined.

For $\deg A<9(m+1)$ and a rational $t$ with $t+k\ne0$ for every $0\le k\le m$, we prove
$$
\frac{A(t)}{D_m(t)^9}
=\sum_{j=0}^{m}\sum_{s=1}^{9}\frac{c_{m,j,s}(A)}{(t+j)^s}.
$$
First reconstruct $A$ by its polynomial local blocks. Evaluate that finite identity at $t$ and divide by the nonzero value $D_m(t)^9$.

For each summand use
$$
D_m(t)=(t+j)C_{m,j}(t),\qquad
(t+j)^{9-s}(t+j)^s=(t+j)^9.
$$
All canceled factors are nonzero by the regular-point hypothesis. Summing the resulting termwise identities proves the formula. The local expansion removes the corresponding pole before taking the first nine Taylor coefficients. Its order-nine truncation leaves a remainder divisible by $Z^9$. Translating back to the pole $-j$ shows that $(X+j)^9$ divides the reconstruction error at that pole; all other local blocks already contain this factor. The distinct rational linear factors $X+j$ are pairwise coprime, so their ninth powers together divide the error:
$$
\prod_{j=0}^{m}(X+j)^9\mid A-P_m(A).
$$
The reconstruction has degree below $9(m+1)$. The original numerator satisfies the same strict degree bound, while the displayed divisor has degree exactly $9(m+1)$. The error must therefore vanish.

The submitted file contains the complete reconstruction and cancellation proofs; it does not assume a partial-fraction representation or import its own target.