# Research handoff — 2 October 2026

The [irrationality target](p2m:theorem/523f37b8-ae98-406c-a3f7-43aa8e002dd7) remains **Open**.
The research has been organized into a current overview, complete dated notes and source,
and bounded exact certificates. Recent written results are not Lean-verified theorems.

**Download:** [source and verification release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02),
[research ZIP](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-research-2026-10-02.zip),
[file hashes](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/source-manifest.json).
Begin with `missions/zeta9/README.md`, `PUBLIC_OVERVIEW.md`, and
`research/progress-2026-10-02.md` in the archive. The package README gives the independent replay commands.

## Current written results

1. **Actual directions and arithmetic.** A primitive-row Gram gcd divides exterior content times
   the saturated Gram discriminant, giving a directly computable divisor of the center denominator.
   An exact minimum-denominator rational in a same-side coordinate interval produces a nonzero
   integer form. Six actual cases through n=192 satisfy `0<abs(q*zeta(9)-p)<1` rigorously.
   The interval algorithm's infinite decay and the growth of both Farey parent denominators remain
   equivalent to irrationality; the finite successes are not a noncircular proof of the goal.
2. **Growing-dimensional positive Gram family.** Dimension h and 2h+3 consecutive square poles
   give a positive isolated linear form after full primitive reduction. For M/h -> c, its real error
   exponent is squeezed between f_c-log(16) and f_c<0. At c=0 the endpoints are approximately
   -8.8797162298 and -6.1071275076. The required reduced-denominator bound is unproved.
   Thirty-nine finite matrices have expensive primitive values; a maximal-minor gcd of 24077 at
   (h,M)=(10,10) prevents assuming a universal gcd-one rule.
3. **Complete scalar dispersed-pole classification.** With h=1 and numerator S=1, all integer
   pole positions are covered: m<=5 primitive positive values grow exponentially, with a uniform
   lower rate 9/50 per largest pole even for m=5; m>=6 eliminate the zeta coefficient and give
   primitive constant one. Exact zero-tail exceptions are handled by colored prime budgets.
   This theorem does not cover every higher-rank dispersed matrix.
4. **Isolated rational sum.** Seven derivatives of an Apéry-type double-pole rational function
   give A_n*zeta(9)-b_n, with no suppressed lower-zeta relation. The complete boundary estimate
   is L_n ~ (16/15)n^-4(log n)^5>0. A large-prime theorem applies after full primitive
   cancellation; the needed exceptional-prime mass estimate remains unproved.
5. **An exact leakage repair.** Eightfold zeros remove all first n seventh-derivative summands
   and preserve isolation. Six certified cases have changing signs and primitive absolute values
   above one. Eventual nonvanishing, the actual analytic rate and full primitive cost remain open.

## Verification and next work

The final five scripts passed root reruns and an independent extracted-package replay:
direction arithmetic (6 actual matrices, 358 integer row pairs, 160 minimum-denominator interval checks),
growing rank one (39 matrices), dispersed poles (701 integer configurations and 213 prime valuations),
isolated series (324 residue terms and 79 prime congruences), and the repair
(90 residue terms and 168 endpoint-zero checks). Counts describe distinct check types and are not an
infinite parameter audit. Source hashes and the exact ranges are in the package manifest and certificates.

The old research milestones now distinguish written completion from concrete Lean formalization.
Volume V and the VC/VD arithmetic budgets have written proofs; they should not be re-derived as the
main remaining mathematical obstacles. The main route still needs an input excluding eventual fixation
of the shortest primitive direction. S remains a stronger sufficient condition. The alternative routes
have their own stated denominator or nonvanishing gaps; they need not all be solved simultaneously.

Formal status is separate: the root and its exponential-form obligations remain Open.
This handoff adds no new Lean proof and does not claim irrationality.
