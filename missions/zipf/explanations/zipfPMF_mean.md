For $N\geq1$ and every real $s$, the mean rank is

$$
\sum_{k=1}^{N}k\,\operatorname{zipfPMF}(N,s,k)=\frac{H_{N,s-1}}{H_{N,s}}.
$$

More generally, multiplying the mass at rank $k$ by $k^p$ shifts the harmonic exponent by the natural number $p$. All ranks under consideration are positive, so the real-power subtraction identity applies:

$$
k^{s-p}=\frac{k^s}{k^p},\qquad
k^p\frac{k^{-s}}{H_{N,s}}=\frac{k^{-(s-p)}}{H_{N,s}}.
$$

Summing and factoring out the denominator gives the moment formula. Taking $p=1$ yields the stated mean.
