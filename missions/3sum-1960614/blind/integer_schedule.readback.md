---
declaration: ThreeSum1960614.integer_schedule
readback_model: GPT-6
---

For every three natural numbers $J,s,j$ such that $J>0$, $s>0$, $s$ is even, $j<J$, and $j/J\leq 13/20$ when this quotient is taken in the real numbers, put $d=J-j$, $r=ds$, and $a=j/J$. Here the natural-number subtraction $J-j$, which in general is truncated at zero, is the ordinary positive difference under the hypothesis $j<J$. Define the real-valued functions
$$
H(t)=\frac{-t\log t-(1-t)\log(1-t)}{\log 2},\qquad
P(t)=\frac{785174904t+72447023t^2+24044466t^3+12022459t^4}{100000000},
$$
where $\log$ is the total real natural logarithm: $\log t=\ln|t|$ for $t\ne0$ and $\log0=0$, so the entropy summands at zero are zero. There exists a natural number $q>0$ with $q\leq\lfloor r/2\rfloor$ such that the following comparison of nonnegative integers holds:
$$
500000000d\bigl(785174904qr^3+72447023q^2r^2+24044466q^3r+12022459q^4\bigr)
\geq
100000000\bigl(159243801J+500000000j\bigr)r^4.
$$
Moreover, for every natural number $k<q$, including $k=0$, this integer comparison is false after replacing $q$ by $k$; thus $q$ is least among all natural numbers satisfying that comparison, not merely among those in the stated upper range. For this same $q$, putting $x=q/r$, all four of the following real inequalities hold:
$$
\frac{159243801/500000000+a}{1-a}\leq P(x),
$$
$$
P(x)<\frac{159243801/500000000+a}{1-a}+\frac{9}{r},
$$
$$
\frac{193175570}{1000000000}
\leq
2\left(-\frac{62656016}{1000000000}\right)-a
+(1-a)\left[232H\left(\frac1{232}\right)-232H\left(\frac{1-x}{232}\right)\right],
$$
$$
(1-a)H(x)
<\frac{2790503}{10000000}\left(1+\frac{159243801}{500000000}\right)
+\frac{9(2790503/10000000)}{Js}.
$$
The bound on $q$ uses natural-number division, hence the floor indicated above; since $s$ is positive and even, $r$ is even and at least $2$, so that floor equals the exact integer $r/2$. Every quotient in the four analytic inequalities, and in $a$, $x$, $H$, and $P$, is real division, with natural numbers embedded into the real numbers. Their denominators are nonzero: $J>0$, $r>0$, $Js>0$, and $1-a\geq 7/20>0$. In particular $0<x\leq 1/2$, so the entropy arguments appearing in these inequalities are positive and less than $1$. The hypotheses allow $j=0$ and allow $J=1$ with $j=0$; they impose no additional lower bound on $J$ or on the positive even number $s$.
