Let $m$ be a nonnegative integer. Define
$$
D_m(X)=\prod_{k=0}^{m}(X+k),\qquad
C_{m,j}(X)=\prod_{\substack{0\le k\le m\\k\ne j}}(X+k).
$$
For $0\le j\le m$, the series $A(-j+Z)/C_{m,j}(-j+Z)^9$ is defined at $Z=0$, since its denominator has nonzero constant coefficient. Write
$$
c_{m,j,s}(A)=[Z^{9-s}]\frac{A(-j+Z)}{C_{m,j}(-j+Z)^9},
\qquad 1\le s\le9,
$$
and define the finite reconstruction
$$
P_m(A)(X)=\sum_{j=0}^{m}\sum_{s=1}^{9}
c_{m,j,s}(A)\,C_{m,j}(X)^9(X+j)^{9-s}.
$$

For every rational polynomial $A$ of degree below $9(m+1)$, we prove the complete polynomial reconstruction
$$
A=P_m(A).
$$
The proof matches the first nine cleared Taylor coefficients at every pole, then forces the reconstruction error to vanish by divisibility and degree.

At the pole $-j$, remove the factor $(X+j)^9$ from the denominator and truncate the resulting formal series after degree eight. The truncation remainder is divisible by $Z^9$. Translating back shows that the local block reproduces $A$ modulo $(X+j)^9$. Every block for another pole already contains $(X+j)^9$, so
$$
(X+j)^9\mid A-P_m(A)\qquad(0\le j\le m).
$$
The distinct rational linear factors $X+j$ are pairwise coprime. Consequently,
$$
D_m(X)^9\mid A-P_m(A).
$$
Each reconstructed block has degree at most $9m+8$, and $A$ has degree below $9(m+1)$. The difference therefore has degree below $9(m+1)$, while $D_m^9$ has degree exactly $9(m+1)$. A nonzero difference cannot be divisible by a polynomial of this larger degree. Hence $A=P_m(A)$. The argument also covers $m=0$.