# Independent CoefficientMapJet review

PASS for the actual formal local coefficients and all s=1,...,9 convolution.
Frozen Jet source SHA256:
`e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a`.

The coefficients are extracted from the genuine shifted numerator divided in
Q[[z]] by the ninth power of the genuine erased-pole polynomial. Its constant
coefficient is proved nonzero from the actual product. Mathlib inverse laws
prove the denominator identity and uniqueness. No coefficient array, target
convolution, partial-fraction formula or inverse-map assertion is an input.
The independent audit also proves the weighted quotient exists uniquely and
bridges it to actual weightedR(-j+z)*z^9 at every regular point.

The full Icc(s,9) convolution comes from PowerSeries.coeff_mul and a checked
antidiagonal bijection. For integer W the composed multiplier coefficients
are integers and are cast to Q exactly. The local coefficients themselves
remain rational: n=2,j=0,s=8,W=1 gives -173/2 by exact quotient recurrence.
Thus this file does not close lower coefficient denominator normalization.
The highest coefficients agree with the frozen CoefficientMap entry; the
n=0 formal series is independently checked to be 1 with all lower pole
coefficients zero. Arbitrary W is allowed locally, without claiming its degree
satisfies the global decay condition.

Separate exact-source base build, Jet build and independent audit all exit 0
under Lean 4.33.1 and actual Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. Ten original Jet endpoints and ten
independent review statements have no axioms outside propext,
Classical.choice, Quot.sound. The imported report covers all nine definitions
and nineteen proofs, plus the original integer-quartic statement. Exact
Fraction regressions separately check 2025 all-order weighted coefficients,
540 integer multiplier coefficients and 675 regular weighted bridges.

The proved object is a formal local quotient. Its polynomial evaluation
bridges do not evaluate an infinite formal series numerically and do not
assert analytic convergence. A full Laurent/RatFunc interface, global partial
fractions, reflection/total-coefficient cancellation, exact infinite L,
complete F, invertibility and prescribed-output inverse images remain open.
Irrationality remains open. No original source, shared root, scope, API state,
credentials, or frozen advanced source package was edited by this review.

See independent-review.json and independent-review/independent-compile.log.
