For $N\geq1$ and every real $s$, the entropy is

$$
-\sum_{k=1}^{N}p_k\log p_k
=\frac{s}{H_{N,s}}\sum_{k=1}^{N}\frac{\log k}{k^s}+\log H_{N,s}.
$$

On the support, the positive normalizer and positive rank powers give

$$
\log p_k=-s\log k-\log H_{N,s}.
$$

Multiplying by $p_k$, summing, and distributing the finite sums yields

$$
\sum_{k=1}^{N}p_k\log p_k
=-s\sum_{k=1}^{N}p_k\log k-\log H_{N,s}\sum_{k=1}^{N}p_k.
$$

Normalization makes the last sum equal to $1$. In the weighted logarithm sum, factoring out $H_{N,s}$ leaves the displayed sum of $\log k/k^s$. Negating the resulting identity proves the formula.
