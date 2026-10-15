# Source v3 audit, 2026-10-14

## Confirmed source claims

The original supplied package was kept unchanged. Its complete checksum list
matches the live files. All three standard-library Fraction certificate checks
and all twelve rejection tests passed; see `source-audit.json` and
`certificate-check.txt`.

The derivative of the entropy loss is
`[log(c-1+t)-log(1-t)]/log 2`. Integrating the absolutely convergent power
series on `[0,1/2]` yields the stated positive coefficients. The coefficient
checks therefore imply the polynomial minorant. Positive coefficients give
monotonicity/convexity and reduce the derivative upper bound to the right endpoint.

The entropy tangent is `A+B*t`, where `A=-log_2(1-u)` and
`B=log_2((1-u)/u)`. The polynomial tangent is a global minorant.
Their gap is affine, so its strict positivity at both endpoints covers the
whole closed interval. This uses concavity/convexity, not sampling.

The cleared-switch comparison multiplies the real comparison by the positive
denominators `D*(J-j)*Q*r^4`, with `r=(J-j)*s`. Its coefficients and `N/D`
match the quartic and `v=159243801/500000000`. Positive even `s`, `j<J`, and
`j/J<=13/20` ensure all denominators and the integer half range are valid.
Minimality supplies the previous grid point; the strict derivative bound gives
the `9/r` allowance. Since `(1-j/J)*r^(-1)=(J*s)^(-1)`, the entropy allowance
is independent of the level. The initial tangent argument remains valid when
the least threshold point is below theta by entropy monotonicity, and when
above theta by the tangent inequality.

All twelve ledger formulas match the fixed upstream Parameters.lean formulas
after replacing its named parameters consistently. Interval arithmetic takes
the lower E bound in the auxiliary-correlation charge and upper bounds for
positive E coefficients. The quartic maximum is
`1.9606138795768596941522816`, strictly below `1.96061388<1.960614`.

For the relaxed model lower bound, writing `delta=2-R`, `x=delta/e`,
`a=1-2*rho0`, `A=1/2-k0-rho0`, the reporting cost gives
`b<=(A-(1+rho0)*x)/a`. The switch and initial-query costs then imply
`x<=UG(theta)` and `x<=UH(theta)` with the stated denominators 3 and
`2-rho0`. Monotonicity splits the entire theta interval at the certified point.
The encoding cost gives `delta<=a*x/[a*E0-A+(2-rho0)*x]`; the checked positive
intercept makes this increasing in x. These steps justify the fixed-model
bound, including the easy R>=2 case. They are not a lower bound for 3SUM.

## Open full-machine claim

The supplied package does not prove the complete modified machine runtime.
This is an actual source-level gap, not merely the absence of Lean code.
The extracted fixed commit confirms hard-coded expansion constants, the
original scale `blockCount m=20*(m/(100*microSize m))`, and an end bridge
specialized to the original hybrid cost and exponent `981/500`.

Needed extensions include consistent local universe/prime/counts at expansion
232; a rational-scale executable block schedule and limits; floored band
division; the integer quartic switch; correctness of the changed global cover,
reporting, filtering and coloring assembly; all twelve actual cost contracts;
subpolynomial overhead absorption; polynomial word/address/depth resources;
and the shared word-RAM conclusion for all kappa and all required word widths.

The new mission therefore treats `SolvedInTime 1.960614` and its complete
cost-to-program bridge as open targets. Draft `sorry` declarations are
specifications only. Big O Speedrun submission is deferred until that exact
goal has a complete allowed-axiom proof.
