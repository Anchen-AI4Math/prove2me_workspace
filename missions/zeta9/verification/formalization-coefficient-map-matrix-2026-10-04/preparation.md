# Matrix preparation only

The native source is prepared and has not been run through Lean. No proof-build
PASS, freeze or platform result is claimed yet. The parent will allocate a
serial Lean lane before any replay starts.

`actualFMatrix n i j` is the actual aggregate of `X^i` in output coordinate j,
so the five monomials are rows, as in the research paper. The prepared proofs
relate the genuine quartic aggregate to row action `c * F`, and explicitly
identify Mathlib's default column-action matrix as the transpose of this F.
The planned nonsingularity proof uses only the already proved KernelBridge
bijectivity for even n>=2. No matrix-invertibility input is introduced.

The prepared two-by-five selection matrix has rows selecting B and rho9.
For integer outputs b,a, the actual target is `(b,0,0,0,a)` over Q and the
inverse multiplier's rational coefficients are `(b,a) * S * F^-1`. The source
also prepares the actual five aggregate coordinates, exact L, HasSum and norm
summability, with L equal to b+a*zetaReal9. Integer outputs do not assert that
the resulting polynomial has integer coefficients.

The range is the original p=9,q=1,m=n,d=0 family, even n>=2. This preparation
does not address inverse denominator bounds, height growth, integer multiplier
preimages, J, or irrationality.

Only the actual Aggregate and KernelBridge sources and the required pinned
Mathlib matrix lemmas were read. Connection and earlier frozen records remain
unchanged; no root, scope, API or credential operation was made.

On 2026-10-04 the root checked the actual pinned Mathlib statement
`Function.Surjective A.vecMul ↔ IsUnit A` and corrected the uncompiled
candidate's use from `.mpr` to `.mp`. This is an offline source correction,
not a Lean success claim. The first compilation still awaits a free lane.
