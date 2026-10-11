import Definitions.Def_ZetaNine_CoefficientMap
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet

def shiftedVariable (j : ℕ) : ℚ[X] := X - C (j : ℚ)

def shiftedNumerator (n j : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (shiftedVariable j - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (shiftedVariable j + C (n : ℚ) + C ((i : ℚ) + 1)))

def shiftedClearedDenominator (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (shiftedVariable j + C (k : ℚ))

def localU (n j : ℕ) : ℚ[X] := shiftedVariable j * (shiftedVariable j + C (n : ℚ))

def integerLocalU (n j : ℕ) : ℤ[X] :=
  C (-(j : ℤ) * (n - j : ℕ)) + C ((n : ℤ) - 2 * j) * X + X ^ 2

def clearedSeries (n j : ℕ) : PowerSeries ℚ :=
  (shiftedNumerator n j : PowerSeries ℚ) *
    ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹

def weightedClearedSeries (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  clearedSeries n j * (W.comp (localU n j) : PowerSeries ℚ)

def localCoefficient (n j s : ℕ) : ℚ := PowerSeries.coeff (9 - s) (clearedSeries n j)

def weightedLocalCoefficient (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (weightedClearedSeries n j W)

end ZetaNine.CoefficientMapJet
