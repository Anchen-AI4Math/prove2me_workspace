# Native connection polynomial kernel and finite system

The final source proves the genuine homogeneous equation `D*P.comp u+Hq=0`
forces `P=q=0` for every natural `n>=1` and `q.natDegree<=9`. No bound on P
is needed for this kernel theorem. The proof factors q at n and uses the actual
simple root `v-Cn=(X-C1)*(X+Cn)`, with nonzero first-factor value at1.

The source also defines the fifteen real input coefficients (P degree<=4,
q degree<=9) and proves its linear map bijective. Its output coordinates are
the fifteen even t coefficients, not the literal u-coefficient matrix in the
paper. Actual reflection and degree proofs show these coordinates determine
the complete polynomial. Surjectivity is lifted to the full original equation:
every f of degree<=14 has a unique degree-bounded pair P,q. This includes the
five actual c_n Z_n(u)(u-n-1)^r right-hand sides for r=0,...,4.

Final full native build: attempt7 actual exit0. All39 actual native declaration
records (12 definitions,27 theorems) and12 closed boundary records pass with
only propext, Classical.choice and Quot.sound. Earlier failed native and
boundary attempts are retained and excluded. The new short p/b project shared
only the pinned Mathlib package cache; it borrowed no native proof object.
The early attempt2 kernel object was observed at its successful build and later
overwritten; only the retained attempt5 and final7 objects are hash-bound here.

All principal results retain n>=1. At n0 the Nat subtraction definition of v
differs from the written signed formula. The written n0 system has the explicit
nonzero kernel P=0,q=v^9, proved separately in the boundary audit.

This is an author audit, awaiting independent review. It closes the polynomial
system only. It does not claim actual F transport, the connection determinant,
Smith bounds, asymptotics or zeta irrationality. No root/scope/API/credential
files or previous frozen sources were modified.
