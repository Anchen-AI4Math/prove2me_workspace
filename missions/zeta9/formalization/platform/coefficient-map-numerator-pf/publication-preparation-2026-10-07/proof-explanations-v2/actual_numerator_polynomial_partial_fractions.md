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

For $\deg A<9(m+1)$, we prove
$$
A=\sum_{j=0}^{m}\sum_{s=1}^{9}
c_{m,j,s}(A)\,C_{m,j}^{\,9}(X+j)^{9-s}.
$$
At each pole, the local block reproduces the first nine coefficients of the cleared series. Every block belonging to a different pole is divisible by the corresponding ninth power. Thus $D_m^9$ divides the difference between $A$ and the reconstructed numerator.

Both the original numerator and the reconstruction have degree below $9(m+1)$, whereas $D_m^9$ has degree exactly $9(m+1)$. A nonzero difference cannot have a divisor of larger degree. The difference is therefore zero, which proves the polynomial identity for every nonnegative $m$, including $m=0$.

The submitted file includes the complete supporting proofs for these divisibility and degree facts. It imports the public definition module and does not import its own target theorem.