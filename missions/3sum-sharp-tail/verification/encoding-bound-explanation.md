Put \(M=\binom{cm}{m}9^{cm-m}\). The binomial entropy lower bound gives
\[
 M\geq \frac{\exp(cmH(1/c))}{cm+1}\,9^{(c-1)m}.
\]
All factors are positive for \(c>10\) and \(m\geq1\), so taking square roots
and dividing preserves the inequality. Using \(\log9=2\log3\) and
\(D=4^m\), the remaining exponential is exactly \(D^{A(c)}\). Thus
\[
 \frac{10^{cm}}{\sqrt M}\leq\sqrt{cm+1}\,D^{A(c)}.
\]
This is the pointwise encoding estimate in the manuscript. It supports the
eventual tile-fit and preprocessing argument; the full program and reduction
costs are separate obligations.
