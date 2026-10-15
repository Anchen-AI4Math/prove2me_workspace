# Complete-program extension frontier

Pinned source: `verification/upstream`, fixed public commit
2b639655e07421b9ac743de9090459bab473a7c0. That directory remains an immutable
source snapshot; it is not a modified or compiled 1.960614 implementation.

## Verified local machine components

The changed natural block and band definitions, finite rounding and limit
contracts are now proved in the ThreeSum1960614 namespace. The accepted
analytic, finite scheduling and local-cover proofs also have exact closed
local mirrors. The new `machine/lean/Submission/ThreeSum/QuarticSwitch.lean`
implements the integer quartic test in the inherited Light language;
`ActualQuarticSwitch.lean` proves its execution at every admissible reporting
depth, including zero residual, using the accepted integer scheduling result.
Time is 200*(r+1)+100, every scalar fits (J+r+1000000001)^96, and memory is
preserved. `closed-machine-build-final.txt` verifies all these contracts with
only the three standard axioms. The machine modules are local work and have
not yet been uploaded as a complete project.

The remaining items below concern integrating these verified components
into the complete changed solver, along with the expansion-232 cover/global
encoding, actual twelve-cost charges and polynomial machine realization.

## Executable scales

`Submission/ThreeSum/Scales.lean` defines the original
`blockCount m = 20 * (m / (100 * microSize m))`, and its finite estimates and
limits specialize total size to the ratio 1/5. The new rational ratio requires
`20 * ((203889696 * m) / (20 * 1000000000 * microSize m))`, with the zero-size
fallback retained. Prove `0 <= e*m-mu <20*s`, the eventual positivity, and the
limit mu/m -> e for this actual natural-number schedule.

`BandScales.lean` currently derives the divisor from total-size divisibility
and a fixed 1/20 shift, and concludes log divisor/log n -> 1/100. Replace
that construction by `2 ^ floor((-beta)*mu)` as an executable nonnegative
integer quotient. Reprove its factor-two rounding control and its limit
`(-beta)*epsilon`, along with the number of bands and its addressing bounds.

## Local universe, primes and global encoding

`LocalCoverBounds.lean` has general incidence/degree/mean estimates, but its
concrete localThreshold/localPrime/localBucketCap choose L=512*h.
The new instance requires L=464*h throughout. The accepted mission lemma
justifies the required finite incidence and strict comparisons for expansion
232. The concrete prime and bucket contracts still need the new L.

`LightLocalCoverSchedule.lean` uses weights and candidate coverage on the
universe 512*h, including row counts `p^(2*(512*h))`. Update the consistent
local types and then the global encoding dimension 256*s -> 232*s. Preserve
coverage, trimming independence and multiplicity. Generic finite source
lemmas may be reused; old concrete contracts must not be treated as generic.

## Integer quartic switch and query/reporting assembly

`Switch.lean` uses a cleared cubic numerator and constants 291, 1000 and 10.
`LightSwitch.lean` evaluates that same cubic in the light language, with its
word and step bounds. Both must implement the new degree-four comparison
and fixed constants 500000000, 159243801, 100000000 and the four coefficient
numerators. The switch must preserve its finite least-index semantics and
uniform `9/r` error, and its real-world resource contract must cover the
larger fixed constants and the additional multiplication.

The entropy and box conclusions must apply to every level of the changed
schedule and the initial rounded threshold. Prefix catalog, partial zeta,
sparse query, reporting and offset routines must consume these new contracts
without assuming their own correctness or abstract uncharged callbacks.

## All actual costs and the end statement

`ThreeSumHybridCosts.lean` and the concrete LightThreeSumHybrid solver must
charge their executed operations according to all twelve new exponents.
The strict principal/target gap is used only after showing that local search,
prime chains, arithmetic, table overheads and coloring costs are subpolynomial.
Exceptional sizes keep a verified fallback; needed word/cell/depth resources
must remain polynomial.

The published `costs_solve_3sum` interface quantifies over every positive
rational r with each actual ledger cost strictly below r. It includes r
between the exact ledger maximum and the convenient principal cap
1.96061388. A theorem proved only for r>principal cannot solve that interface.
Preserve the individual raw cost exponents in the operational PowerBound
proofs, then absorb overhead using the strict gap from their finite maximum
to the supplied r. The mission goal uses r=1.960614 and the accepted
parameter certificate afterward.

`FinalSolver.lean` derives the original exact result from
`LightThreeSumHybrid.solves` and `poly_need`.
`ThreeSumHybridEndBridge.lean` is specialized to the original time and
981/500 target. Generalize the actual cost/solver bridge to the new exponent
and then use the inherited realization/compiler interfaces to obtain the
unchanged `EndStatement.ThreeSum.SolvedInTime (980307/500000)` for every
kappa and every required word width.

The fixed-model lower-bound root is not an algorithmic premise. Do not
replace any item above by the mere truth of the numeric ledger. Submit the
Big O Speedrun `Race.bound` only when the complete operational proof closes.
