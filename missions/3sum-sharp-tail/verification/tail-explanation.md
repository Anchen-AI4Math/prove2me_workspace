For integers $c>10$, $m\ge1$ and $0<\theta<0.9$, put $t=\lceil\theta m\rceil$, $L=cm$, $D=4^m$, and

$$\beta_d=\binom L{m-d}9^{L-m+d},\qquad\rho=\frac9{c-1}<1.$$

We prove the sharp normalized bound

$$\frac1{\beta_0}\sum_{d=t}^m\beta_d\le
\frac{cm+1}{1-\rho}D^{-\gamma_*(c,\theta)}.$$

First, the binomial adjacent-coefficient identity gives $(c-1)\beta_d\le9\beta_{d-1}$ for $1\le d\le m$. Iterating and summing the finite geometric series yields

$$\sum_{d=t}^m\beta_d\le\frac{\beta_t}{1-\rho}.$$

Apply the imported two-sided binomial entropy theorem to the numerator coefficient at $m-t$ and to the denominator coefficient at $m$. After cancelling the common power of nine, this gives

$$\frac{\beta_t}{\beta_0}\le(cm+1)\exp\left(cmH\left(\frac{m-t}{cm}\right)-cmH(1/c)+t\log9\right).$$

The ceiling is handled without a rounding factor. The combined function

$$f(u)=cH((1-u)/c)+u\log9$$

is continuous on $[0,1]$, and its derivative on $(0,1)$ is

$$f'(u)=\log\left(\frac{9(1-u)}{c-1+u}\right)<0.$$

Thus $f$ is decreasing on the closed interval. Since $\theta\le t/m\le1$, the displayed exponent is at most

$$m\bigl(f(\theta)-cH(1/c)\bigr)=-m\log4\,\gamma_*(c,\theta).$$

Exponentiating gives $D^{-\gamma_*}$; division by the positive $\beta_0$ and $1-\rho$ completes the proof. The endpoint $t=m$ follows from the same closed-interval monotonicity argument. The sole platform theorem dependency is the two-sided binomial entropy bound; all tail, derivative, and rounding steps are proved in this submission.
