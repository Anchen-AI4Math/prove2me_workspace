For every $\rho>0$, the Yule–Simon mass has the asymptotic equivalent

$$
f(k;\rho)\sim\frac{\rho^2\Gamma(\rho)}{k^{\rho+1}}
=\frac{\rho\Gamma(\rho+1)}{k^{\rho+1}}.
$$

The constant is positive because the Gamma function is positive on positive real arguments. The proof uses Euler's limit formula directly, avoiding an asymptotic expansion of the Gamma function.

Repeated use of its functional equation gives

$$
\Gamma(\rho+k+1)=\Gamma(\rho)\prod_{j=0}^{k}(\rho+j),
\qquad k!=k\Gamma(k)\quad(k\geq1).
$$

Substituting these identities and $\Gamma(\rho+1)=\rho\Gamma(\rho)$ into the mass formula gives the exact ratio

$$
\frac{f(k;\rho)}{\rho^2\Gamma(\rho)/k^{\rho+1}}
=\frac{1}{\Gamma(\rho)}\,
\frac{k^\rho k!}{\prod_{j=0}^{k}(\rho+j)}.
$$

The last numerator quotient is Mathlib's Euler sequence for $\Gamma(\rho)$ and converges to that positive value. The displayed ratio therefore tends to $1$, which establishes the formal asymptotic equivalence. The exceptional rank $0$ does not affect a limit at infinity.
