import Definitions.Def_ZetaNine_CoefficientMapInjectivity
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

def clearedPolePolynomial (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ))

def localTruncation (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (CoefficientMapJet.weightedClearedSeries n j W)

def partialBlock (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (localTruncation n j W).comp (X + C (j : ℚ))

def partialNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    C (CoefficientMapJet.weightedLocalCoefficient n j s W) *
      clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

def candidateClearedSeries (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  ((partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹

end ZetaNine.CoefficientMapPartialFractions
