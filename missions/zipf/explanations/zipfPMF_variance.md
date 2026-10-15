For $N\geq1$ and every real $s$, the variance of the rank is

$$
\frac{H_{N,s-2}}{H_{N,s}}-\frac{H_{N,s-1}^2}{H_{N,s}^2}.
$$

For each positive rank, the real-power subtraction identity rewrites its $p$th-moment contribution as its weight with exponent $s-p$, divided by the original normalizing constant. Thus

$$
\sum_{k=1}^{N}k^p\,\operatorname{zipfPMF}(N,s,k)=\frac{H_{N,s-p}}{H_{N,s}}.
$$

Use this identity for $p=2$ and $p=1$ in the defining expression $\mathbb E[K^2]-\mathbb E[K]^2$. Squaring the quotient for the first moment gives the required denominator and numerator squares.
