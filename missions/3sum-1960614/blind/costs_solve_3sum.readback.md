---
declaration: ThreeSum1960614.costs_solve_3sum
readback_model: GPT-6
---

For every rational number $r$, assume $0<r$ and assume that each of the following twelve real numbers is strictly less than the real number represented by $r$. Here $e=203889696/1000000000$, $d=62656016/1000000000$, $s=193175570/1000000000$, and $H(t)=\bigl(-t\ln t-(1-t)\ln(1-t)\bigr)/\ln 2$ is the binary entropy in base two; all arguments of $H$ appearing below lie strictly between zero and one:
$$
\begin{aligned}
&232eH(1/232),\\
&1+e\bigl(116H(1/232)+d\bigr),\\
&2-es,\\
&2-e\bigl(1/2-d-H(40409899/1000000000)\bigr),\\
&2-e\Bigl(1/2+d-\bigl(464H(1/464)-232H(1/232)-1\bigr)
 -(2790503/10000000)(1+s+2d)\Bigr),\\
&2-e\Bigl(13/20-1/2+d-\bigl(464H(1/464)-232H(1/232)-1\bigr)\Bigr),\\
&(8e/5)\bigl(116H(1/232)+1/2\bigr),\\
&2+e\bigl(4/5-(232/5)H(1/232)+2d\bigr),\\
&1+e(1/2+d),\\
&2-e\bigl(116H(1/232)-d\bigr),\\
&2-2e\bigl(116H(1/232)-d\bigr),\\
&1.
\end{aligned}
$$
Then, for every natural number $\kappa$ (including zero), there exist a finite program $P$, a natural number $b$ (with no separately imposed positivity condition), and a function $T:\mathbb N\to\mathbb N$ with the following two properties simultaneously. First, writing the positive rational $r=p/q$ in lowest terms with positive integer numerator $p$ and positive integer denominator $q$, there exists a natural number $K$ such that, for every natural number $n\ge2$, $T(n)^q\le K n^p$. Second, for every natural number $n$, every function $x:\{0,\ldots,n-1\}\to\mathbb Z$, and every natural word width $W$, if $|x(i)|\le n^\kappa$ for every input position $i$ and $W\ge b(\lfloor\log_2 n\rfloor+1)$, then there exist a Boolean verdict $v$ and a final memory $m$ assigning a $W$-bit word to every integer address such that running $P$ from program position zero on the initial memory specified below halts within $T(n)$ steps with precisely verdict $v$ and memory $m$, and
$$
v=\mathrm{true}\quad\Longleftrightarrow\quad
\exists i,j,k\in\{0,\ldots,n-1\},\quad
i\ne j\ \land\ j\ne k\ \land\ i\ne k\ \land\ x(i)+x(j)+x(k)=0.
$$
The sum and absolute-value bound in this equivalence and its hypothesis are operations on the original, unbounded integers. The witnesses $P,b,T$ may depend on $\kappa$ and the fixed $r$ but must work simultaneously for all permitted $n,x,W$; $K$ is also chosen before $n$. In the width bound, the natural-number binary logarithm is defined to be zero at $n=0$, is zero at $n=1$, and is $\lfloor\log_2 n\rfloor$ for positive $n$. Initial memory contains the integer $n$ reduced modulo $2^W$ at address zero, $x(i)$ reduced modulo $2^W$ at address $i+1$ for $0\le i<n$, and the zero word at every other integer address, including all negative addresses. The program is a finite list whose positions are numbered by natural numbers; each instruction is exactly one of the following: write the word for $1$ into a specified integer-addressed cell; write into a specified cell the sum, difference, or product of the words in two specified cells, with these word operations performed modulo $2^W$; load into a specified cell the word at the address obtained by reading another specified cell as a signed integer; store the word in a specified source cell at the address obtained by reading another specified cell as a signed integer; branch to a specified natural program position if a specified cell read as a signed integer is negative, otherwise advance to the next position; accept with Boolean verdict true; or reject with Boolean verdict false. Each cell named directly by an instruction may have any integer address, and an indirect signed address may also be negative. For $W>0$, signed word interpretation uses the interval $[-2^{W-1},2^{W-1}-1]$; for $W=0$, the sole word and its signed interpretation are zero, so even writing $1$ yields zero. Every write updates only its destination cell and advances to the next program position; branches change only the program position; accept and reject return the current memory. Executing at any position beyond the list's end executes reject. Every executed instruction, including accept, reject, and rejection beyond the end, consumes one step; with no steps remaining there is no returned verdict or memory, even if the next instruction would halt. The default output predicate is true: the output function reads, for each natural $a$, the signed word in final-memory cell $n+1+a$, but no condition is imposed on those words or on any other final-memory contents. The strict cost hypotheses include $1<r$, and equality with any listed cost does not meet the hypotheses. Correctness is required also at $n=0,1,2$, where there are no three distinct positions and the program must reject; at $n=0$ the input bound is vacuous, and when $\kappa=0$ the convention $n^0=1$ applies even at $n=0$. The power bound imposes no inequality at $n=0$ or $n=1$, although the halting and correctness requirement still applies there. Width zero is included if the chosen $b$ makes its lower bound zero; there is no separate hypothesis requiring positive $W$ or requiring exact signed representation of the input words.
