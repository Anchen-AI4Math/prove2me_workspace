# Independent CoefficientMap review

PASS for the actual finite leading-pole entry, source SHA256
`e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03`.

The source defines the genuine p=9,q=1,m=n rational numerator and full pole
product. It proves the regular-point clearing identity with nonzero denominator,
then computes the cleared value at -j from factorial products. The coefficient
is not defined by its binomial closed form. The unweighted actual coefficient
is integral, nonzero for all j<=n, and has the correct general phase (-1)^(n+j).
Its even signed positivity and n=0,j=0 value 1 are verified.

For arbitrary rational-coefficient polynomial W, the actual highest local
coefficient is multiplied by W(-j(n-j)). A nonzero W can vanish at this node;
the independent Lean audit proves the exact nonzero criterion and a cancelling
W=X+1 example at n=2,j=1. The local coordinate identity uses the unscaled u.

Independent original-source build and closed statement/boundary audit both
exit 0 under Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Eight original endpoints and ten independent review statements have no axioms
outside propext, Classical.choice, Quot.sound. All 27 original declarations
are covered by the author's imported type/definition-value records. Finite
Fraction regressions separately check 91 local coefficients, 364 regular
identities and 455 weighted coefficients; they are not the universal proof.

The full lower-order Eq(5) convolution, complete partial fractions, exact
infinite L, full five-dimensional F, invertibility and prescribed-output
inverse images remain unproved by this file. Irrationality remains open.
No source, shared root, scope, frozen advanced package or API state was edited.

See independent-review.json and independent-review/independent-compile.log.
