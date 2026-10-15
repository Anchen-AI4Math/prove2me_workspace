# Algorithm bridge: pinned interfaces and remaining work

## Current continuation: exact-tail pruned interface

The real-parameter and finite-cost steps are now proved: rational theta
selection, transfer to exact pruned costs, and a finite `RatParams` witness
for the entire `CostsWithinP` regime are ACCEPTED. The actual generic offline
program specification is also ACCEPTED. Original algorithm reduction
`8dd09e30-fb6a-4ec5-b696-400ce5c61423` is SKETCH_ACCEPTED and connects these
to `ThreeSumSharpTail.cost_regime_solve_3sum`, the remaining Open semantic
child. Both the original algorithm theorem and the main 3SUM goal remain Open.

The remaining child must use the full-D host. The generic mid-D host at
`claim_ae_theorem_17_mid` cannot be applied with only the weakened exponent s:
for g=D^(s/2) and Dmid about D/g, g/Dmid^s is
D^(-s/2+s^2/2), which is larger than the needed D^(-s/2). The original
full-D `claim17_of_host` (accepted older Exact-Triangle source, lines
6314-6327), `et17_solves`, and parameter-procedure construction provide one
route. Another full-D all-edges route is recorded in
`verification/allEdgesExactTriangle-source.lean`: generic
`obeysBound17_allHostTime` (24362), `claim17_of_allEdges_host` (24765),
`allEt17_solves` (28538), and `full_host_of_prepared` (24746).

The actual offline step count, full-D rational parameter procedures and
polynomial host needs, full-D call and extra costs, explicit Exact-Triangle
time deduction, exact rational regime representation, and generic 3SUM
conversion are now ACCEPTED. The original cost-regime reduction composes
these interfaces and compiles locally, but has not been submitted while
its two program frontiers remain unfinished: native generic Lop detection
and all-size uniformization. The latter may use the existing Proved uniform
solver only for bounded small sizes; its large-size saving comes from the
new explicit-time theorem.

Native program resources use `ThinInst`/`TaskN` and arbitrary free pointers.
The resource child has a polynomial `Need` witness and actual offline
`Meets` conclusion for every appended program. The finite branch tests the
exact integer inequality `D^B <= N^A`, equivalent to `D <= N^a`, and uses
the actual brute routine outside that regime. The previous `ThinInstance`
and `ProgramSolves` source interface is absent from the flattened platform
definition mirror and is not the active path.

The newer existing platform module `Definitions.Def_APSP299791_Defs4` comes
from `ThreeSumApsp.Pruned.Costs` at commit `27a2fa4bab32`. It contains a complete
proof of `CorollaryP.costs`, for arbitrary real c, theta and epsilon. Its
`GammaOf` is the same entropy expression as `ThreeSumSharpTail.sharpSaving`.
The actual `cost8p` keeps `tailBeta/M` and the retained encoding count, and
`CostsWithinP` uses this exact cost. The generic program is `program31P G`.

The platform accepted this task's `encoding_bound`, actual `retained_tiles_cost`,
and `pruned_encoding_comparison`. The latter proves `Apruned <= encodingExponent`
and transfers the original strict thinness assumption to `AdmissibleP`.
The next formal obligations are rational theta selection with the strict
margins preserved, an exact transfer to `CostsWithinP`, and a generic finite
program plus all-edges/Exact-Triangle/3SUM reduction for a and s. Existing
fixed-parameter accepted results provide source bodies and verified children;
they do not replace the original generalized bridge statement.

The old interface obstruction described below concerns `cost8` and
`CostsWithin`; it does not apply to `cost8p` and `CostsWithinP`.

Source commit: `e1a4e6508154ea59f030480661590a9fe3018011` of
`anthropics/formal-math`, subtree `3sum-apsp`. Relevant source snapshots are in
`verification/upstream/`; the accepted older Exact Triangle solution and its
actual platform graph are saved separately.

The existing platform result `TrulySubcubicAPSP.exactTriangle`
(`86662280-ad77-4341-89f6-2a606cd717da`) is Proved. Its graph contains existing
program-correctness and cost lemmas and 106 theorem/definition nodes. This is
useful reusable source material. The old exponent does not imply the smaller
new exponent.

## Where the sharper estimate must enter

`Light.Sec4.program31` computes the rational parameters and the threshold for
bounded-size exceptions. Its compiled correctness interfaces are
`Light.Sec4.isDataStructure_of_costsWithin` and
`Light.Sec4.solves_of_costsWithin` in
`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean`.

These interfaces require `CostsWithin`. The old certificate bounds the
relaxed quantity `cost8`, whose first term is proportional to

`L * m * rho^t / (1-rho) * N^2`.

It is therefore insufficient to prove the new entropy tail and apply the old
interface unchanged: the old bound has already replaced the actual tail by a
uniform geometric estimate. The needed program-cost interface must retain the
actual box count, bounded by `(m+1) * sum beta_d`, through the preprocessing
cost assembly, and only then apply `sharp_normalized_tail`. Program correctness
is reusable; the stronger step-count bound needs its own proof.

## Exact obligations of the existing published bridge target

1. Prove the retained-tail preprocessing bound for the actual program and its
   memory/word-width requirements, including the encoding term and tile fit.
2. Prove the query bound with the ceiling switch point. For general real theta,
   choose rational program parameters using the strict hypothesis margins.
3. Compose the parameterized Exact Triangle reduction, retaining witness-scan,
   prime-selection, and instance-construction costs at the chosen D and g.
4. Apply the verified 3SUM reduction to that Exact Triangle solver and absorb
   rounding/polylogarithmic losses using the strict exponent gap.
5. Transport the resulting program to the exact shared `EndStatement` model,
   with one finite instruction list for each kappa, bounded-size exceptions,
   and correctness for every word width above the threshold. The standalone
   `lean/KappaZeroAdapter.lean` now proves that the positive-kappa result extends
   to kappa=0, with the same witnesses for kappa=1 and a separate empty-input
   argument; its axiom report is in `verification/kappa-zero-check.txt`.

The main reduction already connects the existing numerical certificate and
this exact bridge target. No oracle, assumed program, or replacement goal has
been introduced. The bridge remains Open until these obligations are closed.
