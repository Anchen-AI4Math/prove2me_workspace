# Literal read-back

**`entropy`.** For every real number $t$, this definition returns the real number $H(t)=\bigl(-tL(t)-(1-t)L(1-t)\bigr)/\ln 2$, where $L(x)=\ln|x|$ for a nonzero real number $x$ and $L(0)=0$. Thus the logarithm is a total real function, including negative arguments, and the formula is defined for every real $t$, with no restriction to the interval $[0,1]$. In particular, $H(0)=H(1)=0$ and $H(1/2)=1$; the denominator $\ln 2$ is nonzero.

**`E`.** For every natural number $c$, including $c=0$, let $C$ be the same number regarded as a real number. This definition returns $\frac{C}{2}H(1/C)$, where $H(x)=\bigl(-xL(x)-(1-x)L(1-x)\bigr)/\ln 2$, $L(y)=\ln|y|$ when $y\ne0$, and $L(0)=0$. Real division is total and a real number divided by zero is zero, so when $c=0$ the argument $1/C$ is zero and the returned value is zero. The returned value is also zero when $c=1$.

**`kappa`.** For every natural number $c$, including zero, with $C$ its value in the real numbers, this definition returns $2C H\bigl(1/(2C)\bigr)-C H(1/C)-1$, where $H(x)=\bigl(-xL(x)-(1-x)L(1-x)\bigr)/\ln 2$, $L(y)=\ln|y|$ for $y\ne0$, and $L(0)=0$. Every real division by zero has value zero. Consequently the returned value is $-1$ when $c=0$ and is $1$ when $c=1$.

**`gamma`.** For every natural number $c$ and every real number $t$, with $C$ the real value of $c$, this definition returns $C H(1/C)-C H\bigl((1-t)/C\bigr)$, where $H(x)=\bigl(-xL(x)-(1-x)L(1-x)\bigr)/\ln 2$, $L(y)=\ln|y|$ for $y\ne0$, and $L(0)=0$. No interval restriction is imposed on $t$. Division by zero is zero, so for $c=0$ the result is zero for every $t$; for $c=1$ it is $-H(1-t)$. For every $c$ the result at $t=0$ is zero.

**`phi`.** For every real number $t$, this definition returns the real polynomial value $\bigl(785174904t+72447023t^2+24044466t^3+12022459t^4\bigr)/100000000$. All coefficients and the denominator are exact real values of the displayed integers, and there is no restriction on $t$.

**`phiDeriv`.** For every real number $t$, this definition returns the real polynomial value $\bigl(785174904+2\cdot72447023t+3\cdot24044466t^2+4\cdot12022459t^3\bigr)/100000000$. This declaration specifies that formula for every real input; it contains no hypothesis or assertion about differentiation.

**`epsilon`.** This definition has no arguments and returns the exact real number $203889696/1000000000$.

**`beta`.** This definition has no arguments and returns the exact real number $-(62656016/1000000000)$.

**`saving`.** This definition has no arguments and returns the exact real number $193175570/1000000000$.

**`theta`.** This definition has no arguments and returns the exact real number $40409899/1000000000$.

**`tau`.** This definition has no arguments and returns the exact real number $13/20$.

**`rho`.** This definition has no arguments and returns the exact real number $2790503/10000000$.

**`tangentPoint`.** This definition has no arguments and returns the exact real number $17200068185091493/100000000000000000$.

**`principal`.** This definition has no arguments and returns the exact real number $196061388/100000000$.

**`target`.** This definition has no arguments and returns the exact rational number $1960614/1000000$.

**`v`.** This definition has no arguments and returns the real number $193175570/1000000000-2\bigl(-(62656016/1000000000)\bigr)$, equivalently $159243801/500000000$.

**`threshold`.** For every real number $a$, this definition returns $\bigl(159243801/500000000+a\bigr)/(1-a)$. It includes the input $a=1$: since real division by zero is defined to be zero, the returned value at that input is zero.

**`ledger`.** For every eight real arguments $e,b,S,d,p,A,K,B$, corresponding in order to the parameters $e,b,S,\mathit{terminal},\mathit{ratio},EE,kk,hh$, this definition returns the ordered list of twelve real numbers $[\,2eA,\ 1+e(A-b),\ 2-eS,\ 2-e(1/2+b-B),\ 2-e\bigl(1/2-b-K-p(1+S-2b)\bigr),\ 2-e(d-1/2-b-K),\ e(8/5)(A+1/2),\ 2+e\bigl(4/5-(2/5)A-2b\bigr),\ 1+e(1/2-b),\ 2-e(A+b),\ 2-2e(A+b),\ 1\,]$. No positivity, sign, distinctness, or interval conditions are imposed on any argument; the list always has twelve entries, with its final entry equal to one, even when some entries coincide.

**`costs`.** This definition has no arguments and returns the following ordered list of twelve real numbers: $[\,2eA,\ 1+e(A-b),\ 2-eS,\ 2-e(1/2+b-B),\ 2-e\bigl(1/2-b-K-p(1+S-2b)\bigr),\ 2-e(d-1/2-b-K),\ e(8/5)(A+1/2),\ 2+e\bigl(4/5-(2/5)A-2b\bigr),\ 1+e(1/2-b),\ 2-e(A+b),\ 2-2e(A+b),\ 1\,]$, where $e=203889696/1000000000$, $b=-(62656016/1000000000)$, $S=193175570/1000000000$, $d=13/20$, $p=2790503/10000000$, $A=116H(1/232)$, $K=464H(1/464)-232H(1/232)-1$, and $B=H(40409899/1000000000)$. Here $H(x)=\bigl(-xL(x)-(1-x)L(1-x)\bigr)/\ln2$, with $L(y)=\ln|y|$ for $y\ne0$ and $L(0)=0$. The displayed fractions and all arithmetic are exact real arithmetic, and the order of the twelve entries is part of the returned list.

**`clearedSwitch`.** For every four natural numbers $J,s,j,q$, including zero, this definition is the proposition $500000000d\bigl(785174904qr^3+72447023q^2r^2+24044466q^3r+12022459q^4\bigr)\ge100000000(159243801J+500000000j)r^4$, where $d=\max\{J-j,0\}$ is natural subtraction truncated at zero and $r=ds$; all products, powers, additions, and the comparison in this formula are natural-number operations. There is no requirement that $j<J$, or that $s$ or $q$ be positive. If $j\ge J$, both sides are zero and the proposition is true, so in particular it is true for every $s,j,q$ when $J=0$; if $s=0$, the right-hand side is zero and the left-hand side is nonnegative, so it is again true. If $j<J$ and $s>0$ but $q=0$, the left-hand side is zero and the right-hand side is positive, so the proposition is false.

**`ModelFeasible`.** For every natural number $c$ and seven real numbers $e,b,S,u,d,p,R$, corresponding in order to $e,b,S,\mathit{th},\mathit{terminal},\mathit{ratio},R$, this definition is a proposition that is true exactly when all the following conditions hold together: $0<e<1$, $b<0$, $S>0$, $0\le u\le1/2$, $0\le d<1$, $p>0$, $S-2b\le G(u)$, for every real $t$ with $0\le t\le1/2$ one has $H(t)\le p(1+G(t))$, and every real number $z$ belonging to the twelve-entry list $[\,2eA,\ 1+e(A-b),\ 2-eS,\ 2-e(1/2+b-B),\ 2-e\bigl(1/2-b-K-p(1+S-2b)\bigr),\ 2-e(d-1/2-b-K),\ e(8/5)(A+1/2),\ 2+e\bigl(4/5-(2/5)A-2b\bigr),\ 1+e(1/2-b),\ 2-e(A+b),\ 2-2e(A+b),\ 1\,]$ satisfies $z\le R$. In these conditions, $C$ is the real value of $c$, $H(x)=\bigl(-xL(x)-(1-x)L(1-x)\bigr)/\ln2$, $L(y)=\ln|y|$ for $y\ne0$ and $L(0)=0$, $G(t)=C H(1/C)-C H((1-t)/C)$, $A=(C/2)H(1/C)$, $K=2C H(1/(2C))-C H(1/C)-1$, and $B=H(u)$. All real divisions by zero have value zero. The interval in the universal condition includes both endpoints and is nonempty; the list condition is equivalently the simultaneous upper bound by $R$ on each of its twelve entries, including $1\le R$, regardless of repeated entries. The natural input $c=0$ is included but makes this proposition false, since then $G(u)=0$ whereas $S-2b>0$ under the other conditions; $c=1$ also makes it false, since then $G(u)=-H(1-u)\le0$ for $0\le u\le1/2$.
