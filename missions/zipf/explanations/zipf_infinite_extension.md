For every real exponent $s\geq 0$,

$$
\sum_{k=1}^{\infty} k^{-s}\text{ converges}\iff s>1.
$$

When $s>1$, the normalizing constants $H_{N,s}$ converge to $\zeta(s)$; when $s\leq1$, they tend to $+\infty$. The argument identifies the finite normalizing constants with the partial sums of the translated $p$-series.

Induction on $N$ gives

$$
H_{N,s}=\sum_{k=0}^{N-1}\frac{1}{(k+1)^s}.
$$

Mathlib's translated $p$-series criterion gives summability exactly for $s>1$. In that range, positivity of $k+1$ identifies the complex cast of its real power with the corresponding complex power. The defining series of the Riemann zeta function on the half-plane $\operatorname{Re}(s)>1$ therefore gives

$$
\sum_{k=0}^{\infty}\frac{1}{(k+1)^s}=\zeta(s),
\qquad H_{N,s}\longrightarrow\zeta(s)
$$

in $\mathbb C$, as required by the formal statement.

For $s\leq1$, the same criterion shows that the series is not summable. Every term is nonnegative, so the general equivalence between nonsummability and divergence of nonnegative partial sums implies

$$
H_{N,s}\longrightarrow+\infty.
$$
