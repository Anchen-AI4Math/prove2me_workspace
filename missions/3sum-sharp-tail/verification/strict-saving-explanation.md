For $c>10$ and $0<\theta<0.9$, the old saving is positive and the new saving is strictly larger:

$$0<\gamma(c,\theta)<\gamma_*(c,\theta).$$

Positivity follows because $(c-1)/9>1$ and $\log4>0$. For the strict comparison, expand the two entropy terms and cancel the common logarithms of $c$. The difference between their numerator and $\theta\log(c-1)$ becomes

$$F=(c-1+\theta)\log\left(1+\frac{\theta}{c-1}\right)+(1-\theta)\log(1-\theta).$$

The strict inequality $\log x<x-1$ for positive $x\ne1$, applied to reciprocals, gives

$$\log(1-\theta)>-\frac{\theta}{1-\theta},\qquad
\log\left(1+\frac{\theta}{c-1}\right)>
\frac{\theta/(c-1)}{1+\theta/(c-1)}.$$

Multiplying by the positive coefficients shows that the first summand of $F$ exceeds $\theta$ and the second exceeds $-\theta$, hence $F>0$. Subtracting $\theta\log9$ from both numerators and dividing by the positive $\log4$ proves the strict saving comparison. This is a direct analytic proof and makes no algorithmic running-time claim by itself.
