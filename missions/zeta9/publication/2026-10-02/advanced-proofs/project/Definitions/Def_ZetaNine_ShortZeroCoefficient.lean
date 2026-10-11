import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Basic

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.ShortZeroCoefficient

/-- The exact integer coefficient of `z^j` in the weighted Franel polynomial. -/
def weightedCoeff (n m r b j : ℕ) : ℕ :=
  n.choose j ^ r * ((j + m).choose m * (n - j + m).choose m) ^ b

/-- The genuine finite sum from the C3 note, rather than an abstract positive sum. -/
def A (n m : ℕ) : ℤ :=
  28 * ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (m + j) *
    (weightedCoeff n m 3 7 j : ℤ)

end ZetaNine.ShortZeroCoefficient
