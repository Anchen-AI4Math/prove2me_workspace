Let $m\geq2$, $q>0$, and $mq<1$. For every injective enumeration of all nonempty words in nonincreasing probability order, the word at zero-based rank $r$ satisfies

$$
C_1(r+1)^{-a}\leq p_r\leq C_2(r+1)^{-a},\qquad
a=\log_m(1/q),
$$

with positive constants

$$
C_1=q(1-mq),\qquad C_2=(1-mq)/q.
$$

Write $L$ for the length of the word at rank $r$. The assumptions give $0<q<1$, so probability decreases strictly with length. Every word among the first $r+1$ ranks has length at most $L$. There are at most $m^j$ words of length $j$, and the geometric sum therefore gives

$$
r+1\leq\sum_{j=0}^{L}m^j\leq m^{L+1}.
$$

If $L>1$, all $m^{L-1}$ words of length $L-1$ have strictly greater probability and must appear before rank $r$. The same weak bound is immediate when $L=1$. Consequently,

$$
m^{L-1}\leq r+1,\qquad m^L\leq m(r+1).
$$

Raising these bounds to the negative exponent $\log_m q=-a$ reverses their direction. The identity $(m^j)^{\log_m q}=q^j$ then gives

$$
q(r+1)^{-a}\leq q^L\leq q^{-1}(r+1)^{-a}.
$$

Multiplying by the positive space probability $1-mq$ gives the stated bounds. Equal-probability ties require no additional ordering assumption.
