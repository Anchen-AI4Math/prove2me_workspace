import Definitions.Def_ZetaNine_HarmonicStability

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.HarmonicStability

/-- The sum of the actual harmonic terms whose index is not divisible by p. -/
def primeRemainder (s N p : ℕ) : ℚ :=
  ∑ j ∈ (Finset.Icc 1 N).filter (fun j => ¬ p ∣ j), 1 / (j : ℚ) ^ s

/-- Product of the absolute reduced numerators of the actual first K harmonic prefixes. -/
def harmonicExceptionalProduct (s K : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 K, (harmonicPower s k).num.natAbs

end ZetaNine.HarmonicStability
