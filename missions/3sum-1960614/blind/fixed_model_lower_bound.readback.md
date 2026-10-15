# Read-back: `ThreeSum1960614.fixed_model_lower_bound`

readback_model: GPT-6

For every seven real numbers $e,b,S,\theta,u,r,R$, where $\theta$ denotes the argument named `th`, $u$ denotes `terminal`, and $r$ denotes `ratio`, define the normalized binary entropy, on the arguments in $[0,1]$ used here, by $H(x)=-\bigl(x\log x+(1-x)\log(1-x)\bigr)/\log 2$, with the endpoint convention $0\log 0=0$ and with $\log$ the natural logarithm. Suppose all of the following conditions hold:

$$
\begin{gathered}
0<e<1,\qquad b<0,\qquad 0<S,\\
0\le\theta\le\frac12,\qquad 0\le u<1,\qquad 0<r,\\
S-2b\le 232H\!\left(\frac1{232}\right)-232H\!\left(\frac{1-\theta}{232}\right),\\
\text{for every real }t\text{ with }0\le t\le\frac12,\quad
H(t)\le r\left(1+232H\!\left(\frac1{232}\right)-232H\!\left(\frac{1-t}{232}\right)\right).
\end{gathered}
$$

Suppose also that every real number $z$ belonging to the twelve-entry ledger is at most $R$; fully expanded, this means that each of the following twelve inequalities holds, in the ledger's order:

$$
\begin{aligned}
1.\quad &2e\left(116H\!\left(\frac1{232}\right)\right)\le R,\\
2.\quad &1+e\left(116H\!\left(\frac1{232}\right)-b\right)\le R,\\
3.\quad &2-eS\le R,\\
4.\quad &2-e\left(\frac12+b-H(\theta)\right)\le R,\\
5.\quad &2-e\left(\frac12-b-\left(464H\!\left(\frac1{464}\right)-232H\!\left(\frac1{232}\right)-1\right)-r(1+S-2b)\right)\le R,\\
6.\quad &2-e\left(u-\frac12-b-\left(464H\!\left(\frac1{464}\right)-232H\!\left(\frac1{232}\right)-1\right)\right)\le R,\\
7.\quad &e\,\frac85\left(116H\!\left(\frac1{232}\right)+\frac12\right)\le R,\\
8.\quad &2+e\left(\frac45-\frac25\left(116H\!\left(\frac1{232}\right)\right)-2b\right)\le R,\\
9.\quad &1+e\left(\frac12-b\right)\le R,\\
10.\quad &2-e\left(116H\!\left(\frac1{232}\right)+b\right)\le R,\\
11.\quad &2-2e\left(116H\!\left(\frac1{232}\right)+b\right)\le R,\\
12.\quad &1\le R.
\end{aligned}
$$

Then the theorem asserts the strict lower bound $\frac{196061349120}{100000000000}<R$. The natural-number parameter of the feasibility predicate is fixed to $232$, rather than quantified. The quantifiers over $t$ include both $t=0$ and $t=\frac12$; the permitted parameter values include $\theta=0$, $\theta=\frac12$, and $u=0$. The values $e=0$, $e=1$, $b=0$, $S=0$, $u=1$, and $r=0$ are excluded by strict hypotheses. No integrality assumptions or further bounds on these seven real parameters are imposed; in particular, $R$ is quantified over all real numbers before the hypotheses are applied. Every ledger bound and both entropy comparison bounds are non-strict, whereas the asserted bound on $R$ is strict.
