# General denominator stability: Lean coverage and limits

The standalone file `formalization/HarmonicStability.lean` was compiled
from the repository root with Lean 4.33.1 by

    lake env lean missions/zeta9/formalization/HarmonicStability.lean

All eight exported arithmetic and analytic theorems compiled with no
`sorry`, no custom axiom, and no `sorryAx` dependency. Their printed axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
`lean-check.log` preserves the exact successful output. The separately
compiled `HarmonicStabilityDefinitions.lean` is a lightweight definition
source for the root agent's formal module integration; it is not imported
together with the standalone duplicated definition block.

## Exact coverage of the original research statement

- Original Lemma 2, all rational `h,r`: both denominator divisibilities
  and the absolute logarithmic difference bound, without numerator-height,
  sign, nonzero, or cancellation restrictions.
- Original Theorem 1's finite upper arithmetic step, all natural `s,N`:
  the actual rational sum `sum j in Icc 1 N, 1/(j:Q)^s` has reduced
  denominator dividing `Nat.lcmUpto N ^ s`. Its logarithmic upper bound
  is also proved. The result includes zero endpoint and zero order as
  well as the originally stated positive orders.
- Unconditional perturbation-error transfer: for every rational sequence
  `h,r`, every nonnegative normalization scale, and every filter, if the
  normalized log denominator of `r` tends to zero then the normalized
  difference of the actual perturbed and unperturbed log denominators
  tends to zero. No baseline denominator-rate limit is assumed for this
  theorem.
- General rate transfer: if the unperturbed rational sequence has a limit
  `a` for its normalized log denominator, the perturbed sequence has that
  same limit. The conclusion is proved from the unconditional arithmetic
  inequality, not inserted as an assumption.
- Application to the actual harmonic sequence: its normalized perturbation
  error tends to zero unconditionally under the small-perturbation premise.
  The exact-rate harmonic corollary is explicitly conditional on the
  unperturbed harmonic rate, which is a separate original theorem.

## Not covered

The original finite large-prime block valuation theorem, the PNT-dependent
baseline limit `log den(H_N^(s))/N -> s`, and the Mellin matrix perturbation
estimates are not established by this file. No PNT axiom was declared to
hide this gap. In the exported `harmonic_log_den_rate_stability`, `hh` is
an explicit hypothesis for the unperturbed rate; the theorem must not be
published as a complete proof of that baseline rate or of the original
unconditional PNT corollary. Root-module integration and platform
submission are handled separately by the root agent.
