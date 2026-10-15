For $N\geq1$ and $n\leq N$, the cumulative mass through rank $n$ is

$$
\sum_{k=1}^{n}\operatorname{zipfPMF}(N,s,k)=\frac{H_{n,s}}{H_{N,s}}.
$$

Every rank in the summation interval lies in the support of the distribution. Its mass is therefore $k^{-s}/H_{N,s}$. Pulling the common denominator outside the finite sum leaves exactly the defining sum of $H_{n,s}$. This also handles $n=0$, when the interval and both numerator sums are empty.
