The theorem preserves the saving delta and logarithmic degree of the supplied
thresholded solver. Its new large-size runtime is not inferred from the old
fixed saving.

For sizes below N = max n0 3, the existing Proved uniform solver at saving
7/4000 supplies correctness and a finite bound. Its time is at most
K0 * N^delta * (log N + 1) times the desired new uniform shape. For sizes
at least N, the supplied explicit bound is instantiated at
kappa = max 1 (log u / log n); logarithm inequalities bound this by the
new uniform shape with coefficient max 1 K. These are direct pointwise
inequalities, including logarithmic degree zero.

The actual native ChooseBySize program combines the two solvers. A positive
sum of their constants and the fixed choice overhead bounds its time on
every input size. The native monotone-time interface supplies the final
uniform theorem. Polynomial resources and program shifting are proved by
the generic native execution bodies, rather than asserted as new assumptions
in the theorem statement.

The independently checked mathematical assembly is saved in
`verification/uniform-small-bound.lean`. The platform solution contains
those proof bodies and the actual program assembly; the only external
algorithm used for the small branch is the existing Proved uniform theorem.
