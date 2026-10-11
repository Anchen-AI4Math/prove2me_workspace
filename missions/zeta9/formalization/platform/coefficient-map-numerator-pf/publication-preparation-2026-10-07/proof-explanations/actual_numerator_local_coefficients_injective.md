Let \(m\) be a nonnegative integer, and write
$$
D_m(z)=\prod_{k=0}^{m}(z+k),\qquad
C_{m,j}(z)=\prod_{\substack{0\le k\le m\\k\ne j}}(z+k).
$$
For \(0\le j\le m\) and \(1\le s\le9\), define the rational coefficient
$$
c_{m,j,s}(A)=[X^{9-s}]\,
\frac{A(X-j)}{C_{m,j}(X-j)^9}
$$
using the formal power series at \(X=0\). The denominator has nonzero constant coefficient, so this formal inverse is defined.

For two rational polynomials \(A,B\) of degree below \(9(m+1)\), equality of all coefficients \(c_{m,j,s}\) implies \(A=B\).

The difference \(A-B\) still has degree below \(9(m+1)\). Formal-series multiplication and coefficient extraction are linear in the numerator, so
$$
c_{m,j,s}(A-B)=c_{m,j,s}(A)-c_{m,j,s}(B)=0
$$
for every indicated pole and order.

Reconstruct the proper numerator \(A-B\) from these actual local coefficients. Every summand in its reconstruction is zero, hence \(A-B=0\). The complete reconstruction and linearity proofs are included in the submitted file. This argument uses the full local array and adds no independent injectivity assumption.