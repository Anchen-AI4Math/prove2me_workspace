import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Basic

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.ShortZeroCoefficient

/-- The exact natural weight used by the genuine finite coefficient sum. -/
def weightedCoeff (n m r b j : ℕ) : ℕ :=
  n.choose j ^ r * ((j + m).choose m * (n - j + m).choose m) ^ b

/-- The exact integer highest coefficient in the original short-zero construction. -/
def A (n m : ℕ) : ℤ :=
  28 * ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (m + j) *
    (weightedCoeff n m 3 7 j : ℤ)

end ZetaNine.ShortZeroCoefficient
