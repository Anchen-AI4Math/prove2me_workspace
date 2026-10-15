For integers $r\ge1$ and $0\le k\le r$, write $p=k/r$ and $H(p)=-p\log p-(1-p)\log(1-p)$. The claimed bounds are

$$\frac{e^{rH(p)}}{r+1}\le\binom rk\le e^{rH(p)}.$$

The endpoint cases $k=0$ and $k=r$ have entropy zero and binomial coefficient one, so follow immediately. For the remaining cases, consider the binomial probability masses

$$b_j=\binom rj p^j(1-p)^{r-j},\qquad 0\le j\le r.$$

The binomial theorem gives $\sum_j b_j=1$. Their exact adjacent recurrence is

$$b_{j+1}(j+1)(1-p)=b_j(r-j)p.$$

Since $rp=k$, this shows that the masses increase up to index $k$ and decrease thereafter. Thus $b_k$ is maximal, and nonnegativity and the sum identity imply

$$\frac1{r+1}\le b_k\le1.$$

Finally the logarithm identity

$$\log\bigl(p^k(1-p)^{r-k}\bigr)=-rH(p)$$

implies that multiplying $b_k$ by $e^{rH(p)}$ recovers $\binom rk$. Multiplying the two mass bounds by this positive factor proves both inequalities. Every step uses real identities and integer binomial recurrences, with no numerical approximation or unproved child theorem.
