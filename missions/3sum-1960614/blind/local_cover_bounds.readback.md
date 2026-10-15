---
declaration: ThreeSum1960614.local_cover_bounds
readback_model: GPT-6
---

For every pair of natural numbers $c,h$ satisfying $3\le c$ and $0<h$, let $N=c(2h)=2ch$, and let $\binom{m}{r}$ denote the number of $r$-element subsets of an $m$-element set (with value $0$ when $r>m$). The theorem asserts that all five of the following statements hold simultaneously:
$$
\begin{aligned}
\binom{N}{h}\binom{N-h}{h}
  &=\binom{N}{2h}\binom{2h}{h},\\
\binom{N-h}{h}
  &\le\binom{N}{h},\\
\binom{2h}{h}
  &<2^{2h},\\
2^{2h}
  &<\binom{N}{2h},\\
\left(\binom{N-h}{h}\right)^2
  &<\binom{N}{2h}\,2^{2h}.
\end{aligned}
$$
All products, powers, binomial coefficients, and comparisons here are in the natural numbers. The subtraction in $N-h$ is natural-number subtraction, which gives $0$ if the subtrahend exceeds the minuend; under these hypotheses $N\ge6h\ge h$, so it equals the ordinary nonnegative difference. The hypotheses exclude $h=0$ and $c=0,1,2$; they also ensure that every displayed binomial coefficient has its lower argument at most its upper argument. The second assertion is a non-strict upper bound, whereas the third, fourth, and fifth assertions are strict bounds.
