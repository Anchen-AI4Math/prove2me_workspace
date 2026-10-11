import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMap

def numerator (n : ℕ) (t : ℚ) : ℚ :=
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))

def poleProduct (n : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ range (n + 1), (t + k)

def actualR (n : ℕ) (t : ℚ) : ℚ := numerator n t / poleProduct n t ^ 9

def clearedPoleProduct (n j : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ (range (n + 1)).erase j, (t + k)

def clearedR (n j : ℕ) (t : ℚ) : ℚ :=
  numerator n t / clearedPoleProduct n j t ^ 9

def leadingPoleCoefficient (n j : ℕ) : ℚ := clearedR n j (-(j : ℚ))

def weightedR (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  actualR n t * W.eval (t * (t + n))

def clearedWeightedR (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  clearedR n j t * W.eval (t * (t + n))

def weightedLeadingPoleCoefficient (n j : ℕ) (W : ℚ[X]) : ℚ :=
  clearedWeightedR n j W (-(j : ℚ))

end ZetaNine.CoefficientMap
