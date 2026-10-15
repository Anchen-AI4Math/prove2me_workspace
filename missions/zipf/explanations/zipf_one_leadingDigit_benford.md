For every decimal digit $1\leq d\leq9$, the finite Zipf law with exponent $1$ satisfies

$$
\lim_{N\to\infty}\sum_{\substack{1\leq k\leq N\\\operatorname{leadingDigit}(k)=d}}
\frac{1}{kH_N}=\log_{10}(1+1/d).
$$

The proof groups the reciprocal weights into complete decimal blocks, then controls an arbitrary endpoint between two successive powers of ten.

The integers with first digit $d$ in the $j$th block form exactly the interval

$$
[d10^j,(d+1)10^j).
$$

Its reciprocal weight is the difference

$$
B_j=H_{(d+1)10^j-1}-H_{d10^j-1}.
$$

The Euler–Mascheroni limit states that $H_n-\log(n+1)$ tends to the same constant for all sequences of indices tending to infinity. Applying it at the two block endpoints cancels that constant. The logarithmic difference is independent of $j$, so

$$
B_j\longrightarrow c=\log(d+1)-\log d.
$$

Let $A_M$ be the reciprocal weight of all first-digit-$d$ integers below $10^M$. The exact block partition gives $A_M=\sum_{j<M}B_j$. Cesàro convergence and the same harmonic-number limit yield

$$
\frac{A_M}{M}\longrightarrow c,\qquad
\frac{H_{10^M-1}}{M}\longrightarrow\log10.
$$

These limits persist when a cutoff index is increased from $M$ to $M+1$ while the scaling denominator remains $M$.

For an arbitrary $N$, set $M=\lfloor\log_{10}(N+1)\rfloor$. Both the digit weight and the harmonic normalizer increase with their cutoff. They therefore give the probability bounds

$$
\frac{A_M}{H_{10^{M+1}-1}}
\leq\sum_{\substack{1\leq k\leq N\\\operatorname{leadingDigit}(k)=d}}\frac1{kH_N}
\leq\frac{A_{M+1}}{H_{10^M-1}}.
$$

As $N$ tends to infinity, so does $M$. Both bounds converge to $c/\log10=\log_{10}(1+1/d)$, proving the required limit for all cutoffs.
