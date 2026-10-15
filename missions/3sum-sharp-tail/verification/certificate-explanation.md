The exact parameters

$$c=21,\quad\theta=0.11202,\quad a=0.05665,\quad s=0.06945$$

satisfy all five analytic admissibility inequalities in the target statement. In addition,

$$2-as/4=1.999016414375,\qquad
1.999017-(2-as/4)=0.000000585625.$$

Each terminating decimal is treated as an exact rational, with the appropriate coercion to the reals. The logarithms are enclosed by the verified series bounds

$$2\sum_{i=0}^{K-1}\frac{z^{2i+1}}{2i+1}
\le\log\frac{1+z}{1-z}
\le2\left(\sum_{i=0}^{K-1}\frac{z^{2i+1}}{2i+1}
+\frac{z^{2K+1}}{1-z^2}\right),\qquad0\le z<1.$$

Arguments are scaled by powers of two into $[1,2]$, where the corresponding $z$ is at most $1/3$. Rational partial sums and rational remainder bounds are evaluated exactly. The entropy arguments include

$$\frac{1-\theta}{21}=\frac{44399}{1050000},\qquad
1-\frac{1-\theta}{21}=\frac{1005601}{1050000}.$$

The resulting interval estimates imply

$$0.069454\le\gamma_*(21,\theta)\le0.069456,\qquad
q(\theta)\le0.43054,\qquad A(21)\le17.581.$$

These suffice for the encoding, preprocessing, and query conditions. For the prime-selection condition, the exact integer inequality $7^{100}<2^{281}$ proves $\log7/\log2<2.81$, which leaves enough margin after adding $3a/2$. The instance-construction inequality and both displayed rational equalities follow by exact arithmetic.

This reduction uses two child certificates: the encoding logarithm certificate supplies the baseline and encoding constants, and the entropy logarithm certificate supplies the tail and query arguments. Their enclosures replace the series evaluations inside this final submission. The entropy and exponent comparisons, prime-power inequality, and exact rational equalities are proved here. The parameter theorem is closed once both children are independently verified.

This proves the numerical parameter certificate without floating-point evaluation or an assumed logarithm value. The separate theorem connecting these admissible parameters to a correct word-RAM program is an additional proof obligation.
