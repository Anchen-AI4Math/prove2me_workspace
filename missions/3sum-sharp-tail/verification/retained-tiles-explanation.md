Let \(B\) be the sum of the lengths of the star-box lists traversed by one tile.
The published enumeration theorem gives
\[
 |\operatorname{starBoxes}(L,m,t,e)|
   =\sum_{f=e}^{m-t}\binom Lf9^{L-f}.
\]
Each inner sum is bounded by the sum starting at zero. There are at most
\(m+1\) lists; reflecting \(f=m-d\) therefore gives
\[
 B\leq(m+1)\sum_{d=t}^m\beta_d.
\]
At \(L=cm\) and \(t=\lceil\theta m\rceil\), the proved sharp tail bounds the
right side by \((m+1)M R\), with
\[
 R=\frac{cm+1}{1-9/(c-1)}(4^m)^{-\Gamma(c,\theta)}.
\]

Expanding the actual routine time functions, rather than an asymptotic
description, gives
\[
 t_{\rm tile}=220+(m-t+1)(30L+150)+B(580L+790).
\]
This is at most \(1500(L+1)(B+m+1)\). The two nested band loops, their tests
and setup, and the final constant then give
\[
 t_{\rm allTiles}\leq1600(L+1)
       \bigl(n_B^2(B+m+1)+n_B+1\bigr).
\]
Substitution of the sharp bound on \(B\) proves the statement, for every
number of bands including zero. It is an explicit bound on the routine's
published step-count function. The program correctness contracts, band-count
and tile-fit estimates, encoding stage, compiler costs, and reductions are
separate parts of the final word-RAM bridge.
