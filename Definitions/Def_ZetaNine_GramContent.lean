import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.GramContent

variable {ι : Type*} [Fintype ι]

/-- The integral scalar product, in arbitrary finite dimension. -/
def dot (u v : ι → ℤ) : ℤ := ∑ i, u i * v i

/-- The square norm of an integral row. -/
def normSq (u : ι → ℤ) : ℤ := dot u u

/-- The integral quotient representing the squared norm of the divided
exterior row. For a common minor divisor the division is exact. -/
def saturatedGram (u v : ι → ℤ) (Δ : ℤ) : ℤ :=
  (normSq u * normSq v - (dot u v) ^ 2) / (Δ ^ 2)


end ZetaNine.GramContent
