import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Lightweight definition source for the formal integration of
`HarmonicStability.lean`. It contains only the two actual mathematical
objects and no theorem assumptions, prime-number-theorem axiom, or proof.
The root agent will install these definitions in the shared Definitions
module and replace the standalone proof file's matching definition block
by that import. -/

set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.HarmonicStability

/-- Natural logarithm of the reduced positive rational denominator. -/
noncomputable def logDen (q : ℚ) : ℝ := Real.log (q.den : ℝ)

/-- The generalized harmonic rational number, including `N=0` and `s=0`. -/
def harmonicPower (s N : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℚ) ^ s

end ZetaNine.HarmonicStability
